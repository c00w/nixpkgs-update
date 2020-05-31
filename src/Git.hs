{-# LANGUAGE OverloadedStrings #-}

module Git
  ( checkAutoUpdateBranchDoesntExist,
    checkoutAtMergeBase,
    cleanAndResetTo,
    cleanup,
    commit,
    deleteBranchesEverywhere,
    diff,
    fetch,
    fetchIfStale,
    headHash,
    push,
    setupNixpkgs,
  )
where

import Control.Concurrent
import Control.Exception
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Text as T
import qualified System.Process.Typed
import qualified Data.Text.Encoding as T
import System.Posix.Env (setEnv)
import qualified Data.Text.IO as T
import Data.Time.Clock (addUTCTime, getCurrentTime)
import qualified Data.Vector as V
import OurPrelude hiding (throw)
import System.Directory (doesDirectoryExist, getModificationTime, setCurrentDirectory)
import System.Environment.XDG.BaseDir (getUserCacheDir)
import System.Exit
import Utils (Options (..), Context (..), branchName, branchPrefix)

clean :: ProcessConfig () () ()
clean = silently "git clean -fdx"

checkout :: Text -> Text -> ProcessConfig () () ()
checkout branch target =
  silently $ proc "git" ["checkout", "-B", T.unpack branch, T.unpack target]

reset :: Text -> ProcessConfig () () ()
reset target = silently $ proc "git" ["reset", "--hard", T.unpack target]

delete1 :: Text -> ProcessConfig () () ()
delete1 branch = delete [branch]

delete :: [Text] -> ProcessConfig () () ()
delete branches = silently $ proc "git" (["branch", "-D"] ++ fmap T.unpack branches)

deleteOrigin :: [Text] -> ProcessConfig () () ()
deleteOrigin branches =
  silently $ proc "git" (["push", "origin", "--delete"] ++ fmap T.unpack branches)

cleanAndResetTo :: MonadIO m => Text -> ExceptT Text m ()
cleanAndResetTo branch =
  let target = "upstream/" <> branch
   in do
        runProcessNoIndexIssue_ $ silently "git reset --hard"
        runProcessNoIndexIssue_ clean
        runProcessNoIndexIssue_ $ checkout branch target
        runProcessNoIndexIssue_ $ reset target
        runProcessNoIndexIssue_ clean

cleanup :: MonadIO m => Text -> ExceptT Text m ()
cleanup bName = do
  liftIO $ T.putStrLn ("Cleaning up " <> bName)
  cleanAndResetTo "master"
  runProcessNoIndexIssue_ (delete1 bName)
    <|> liftIO (T.putStrLn ("Couldn't delete " <> bName))

diff :: MonadIO m => ExceptT Text m Text
diff = readProcessInterleavedNoIndexIssue_ $ proc "git" ["diff"]

staleFetchHead :: MonadIO m => m Bool
staleFetchHead =
  liftIO $ do
    nixpkgsGit <- getUserCacheDir "nixpkgs"
    let fetchHead = nixpkgsGit <> "/.git/FETCH_HEAD"
    oneHourAgo <- addUTCTime (fromInteger $ -60 * 60) <$> getCurrentTime
    fetchedLast <- getModificationTime fetchHead
    return (fetchedLast < oneHourAgo)

fetchIfStale :: MonadIO m => ExceptT Text m ()
fetchIfStale = whenM staleFetchHead fetch

fetch :: MonadIO m => ExceptT Text m ()
fetch =
  runProcessNoIndexIssue_ $
    silently "git fetch -q --prune --multiple upstream origin"

push :: MonadIO m => Context -> ExceptT Text m ()
push context =
  runProcessNoIndexIssue_
    ( proc
        "git"
        ( [ "push",
            "--force",
            "--set-upstream",
            "origin",
            T.unpack (branchName (updateEnv context))
          ]
            ++ ["--dry-run" | not (doPR (options context))]
        )
    )

-- Setup a NixPkgs clone in $XDG_CACHE_DIR/nixpkgs
-- Since we are going to have to fetch, git reset, clean, and commit, we setup a
-- cache dir to avoid destroying any uncommitted work the user may have in PWD.
setupNixpkgs :: Text -> IO ()
setupNixpkgs githubt = do
  fp <- getUserCacheDir "nixpkgs"
  exists <- doesDirectoryExist fp
  unless exists $ do
    proc "hub" ["clone", "nixpkgs", fp]
      & System.Process.Typed.setEnv -- requires that user has forked nixpkgs
      [("GITHUB_TOKEN" :: String, githubt & T.unpack)]
      & runProcess_
    setCurrentDirectory fp
    shell "git remote add upstream https://github.com/NixOS/nixpkgs"
      & runProcess_
  setCurrentDirectory fp
  _ <- runExceptT fetchIfStale
  _ <- runExceptT $ cleanAndResetTo "master"
  System.Posix.Env.setEnv "NIX_PATH" ("nixpkgs=" <> fp) True

checkoutAtMergeBase :: MonadIO m => Text -> ExceptT Text m ()
checkoutAtMergeBase bName = do
  base <-
    readProcessInterleavedNoIndexIssue_
      "git merge-base upstream/master upstream/staging"
      & fmapRT T.strip
  runProcessNoIndexIssue_ (checkout bName base)

checkAutoUpdateBranchDoesntExist :: MonadIO m => Text -> ExceptT Text m ()
checkAutoUpdateBranchDoesntExist pName = do
  remoteBranches <-
    readProcessInterleavedNoIndexIssue_ "git branch --remote"
      & fmapRT (T.lines >>> fmap T.strip)
  when
    (("origin/" <> branchPrefix <> pName) `elem` remoteBranches)
    (throwE "Update branch already on origin.")

commit :: MonadIO m => Text -> ExceptT Text m ()
commit ref =
  runProcessNoIndexIssue_ (proc "git" ["commit", "-am", T.unpack ref])

headHash :: MonadIO m => ExceptT Text m Text
headHash = T.strip <$> readProcessInterleavedNoIndexIssue_ "git rev-parse HEAD"

deleteBranchesEverywhere :: Vector Text -> IO ()
deleteBranchesEverywhere branches = do
  let branchList = V.toList $ branches
  result <- runExceptT $ runProcessNoIndexIssue_ (delete branchList)
  case result of
    Left error1 -> T.putStrLn $ tshow error1
    Right success1 -> T.putStrLn $ tshow success1
  result2 <- runExceptT $ runProcessNoIndexIssue_ (deleteOrigin branchList)
  case result2 of
    Left error2 -> T.putStrLn $ tshow error2
    Right success2 -> T.putStrLn $ tshow success2

runProcessNoIndexIssue_ ::
  MonadIO m => ProcessConfig () () () -> ExceptT Text m ()
runProcessNoIndexIssue_ config = tryIOTextET go
  where
    go = do
      (code, out, e) <- readProcess config
      case code of
        ExitFailure 128
          | "index.lock" `BS.isInfixOf` BSL.toStrict e -> do
            threadDelay 100000
            go
        ExitSuccess -> return ()
        ExitFailure _ -> throw $ ExitCodeException code config out e

readProcessInterleavedNoIndexIssue_ ::
  MonadIO m => ProcessConfig () () () -> ExceptT Text m Text
readProcessInterleavedNoIndexIssue_ config = tryIOTextET go
  where
    go = do
      (code, out) <- readProcessInterleaved config
      case code of
        ExitFailure 128
          | "index.lock" `BS.isInfixOf` BSL.toStrict out -> do
            threadDelay 100000
            go
        ExitSuccess -> return $ (BSL.toStrict >>> T.decodeUtf8) out
        ExitFailure _ -> throw $ ExitCodeException code config out out
