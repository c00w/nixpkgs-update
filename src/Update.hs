{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}

module Update
  ( addPatched,
    cveReport,
    prMessage,
    updateAll,
    updatePackage,
  )
where

import qualified Blacklist
import CVE (CVE, cveID, cveLI)
import qualified Check
import Control.Concurrent
import qualified Data.ByteString.Lazy.Char8 as BSL
import Data.IORef
import Data.Maybe (fromJust)
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Data.Time.Calendar (showGregorian)
import Data.Time.Clock (getCurrentTime, utctDay)
import qualified GH
import qualified Git
import NVD (getCVEs, withVulnDB)
import qualified Nix
import qualified NixpkgsReview
import OurPrelude
import Outpaths
import qualified Rewrite
import qualified Time
import Utils
  ( Options (..),
    URL,
    UpdateEnv (..),
    Version,
    Context (..),
    MergeBaseOutpathsInfo (..),
    branchName,
    logDir,
    parseUpdates,
    prTitle,
  )
import qualified Version
import Prelude hiding (log)

default (T.Text)


log' :: MonadIO m => FilePath -> Text -> m ()
log' logFile msg = do
  runDate <- liftIO $ runM $ Time.runIO Time.runDate
  liftIO $ T.appendFile logFile (runDate <> " " <> msg <> "\n")

logFileName :: IO String
logFileName = do
  lDir <- logDir
  now <- getCurrentTime
  let logFile = lDir <> "/" <> showGregorian (utctDay now) <> ".log"
  putStrLn ("Using log file: " <> logFile)
  return logFile

getLog :: Options -> IO (Text -> IO ())
getLog o = do
  if batchUpdate o
    then do
      logFile <- logFileName
      let l = log' logFile
      T.appendFile logFile "\n\n"
      return l
    else return T.putStrLn

notifyOptions :: (Text -> IO ()) -> Options -> IO ()
notifyOptions l o = do
  let repr f = if f o then "YES" else " NO"
  let pr = repr doPR
  let cachix = repr pushToCachix
  let outpaths = repr calculateOutpaths
  let cve = repr makeCVEReport
  let review = repr runNixpkgsReview
  l $ [interpolate|
    Configured Nixpkgs-Update Options:
    ----------------------------------
    Send pull request on success:  $pr
    Push to cachix:                $cachix
    Calculate Outpaths:            $outpaths
    CVE Security Report:           $cve
    Run nixpkgs-review:            $review
    ----------------------------------|]

updateAll :: Options -> Text -> IO ()
updateAll o updates = do
  l <- getLog o
  l "New run of nixpkgs-update"
  notifyOptions l o
  twoHoursAgo <- runM $ Time.runIO Time.twoHoursAgo
  mergeBaseOutpathSet <-
    liftIO $ newIORef (MergeBaseOutpathsInfo twoHoursAgo S.empty)
  updateLoop o l (parseUpdates updates) mergeBaseOutpathSet

updateLoop ::
  Options ->
  (Text -> IO ()) ->
  [Either Text (Text, Version, Version, Maybe URL)] ->
  IORef MergeBaseOutpathsInfo ->
  IO ()
updateLoop _ l [] _ = l "nixpkgs-update finished"
updateLoop o l (Left e : moreUpdates) mergeBaseOutpathsContext = do
  l e
  updateLoop o l moreUpdates mergeBaseOutpathsContext
updateLoop o l (Right (pName, oldVer, newVer, url) : moreUpdates) mergeBaseOutpathsContext = do
  l (pName <> " " <> oldVer <> " -> " <> newVer <> fromMaybe "" (fmap (" " <>) url))
  let uEnv = UpdateEnv pName oldVer newVer url
  let context = Context o mergeBaseOutpathsContext uEnv l
  updated <- updatePackageBatch context
  case updated of
    Left failure -> do
      l $ "FAIL " <> failure
      cleanupResult <- runExceptT $ Git.cleanup (branchName uEnv)
      case cleanupResult of
        Left e -> liftIO $ print e
        _ ->
          if ".0" `T.isSuffixOf` newVer
            then
              let Just newNewVersion = ".0" `T.stripSuffix` newVer
               in updateLoop
                    o
                    l
                    (Right (pName, oldVer, newNewVersion, url) : moreUpdates)
                    mergeBaseOutpathsContext
            else updateLoop o l moreUpdates mergeBaseOutpathsContext
    Right _ -> do
      l "SUCCESS"
      updateLoop o l moreUpdates mergeBaseOutpathsContext

-- Arguments this function should have to make it testable:
-- - the merge base commit (should be updated externally to this function)
-- - the merge base context should be updated externally to this function
-- - the commit for branches: master, staging, staging-next, python-unstable
updatePackageBatch ::
  Context ->
  IO (Either Text ())
updatePackageBatch context =
  runExceptT $ do
    let uEnv = updateEnv context
    let pr = doPR . options $ context
    let batch = (batchUpdate . options $ context)
    --
    -- Filters that don't need git
    Blacklist.packageName (packageName uEnv)
    Nix.assertNewerVersion uEnv
    --
    -- Update our git checkout
    Git.fetchIfStale <|> liftIO (T.putStrLn "Failed to fetch.")
    when pr $
      Git.checkAutoUpdateBranchDoesntExist (packageName uEnv)
    Git.cleanAndResetTo "master"
    --
    -- Filters: various cases where we shouldn't update the package
    attrPath <- Nix.lookupAttrPath uEnv
    when pr $
      GH.checkExistingUpdatePR context attrPath
    Blacklist.attrPath attrPath
    Version.assertCompatibleWithPathPin uEnv attrPath
    srcUrls <- Nix.getSrcUrls attrPath
    Blacklist.srcUrl srcUrls
    derivationFile <- Nix.getDerivationFile attrPath
    assertNotUpdatedOn uEnv derivationFile "master"
    assertNotUpdatedOn uEnv derivationFile "staging"
    assertNotUpdatedOn uEnv derivationFile "staging-next"
    assertNotUpdatedOn uEnv derivationFile "python-unstable"
    --
    -- Calculate output paths for rebuilds and our merge base
    Git.checkoutAtMergeBase (branchName uEnv)
    let calcOutpaths = calculateOutpaths . options $ context
    oneHourAgo <- liftIO $ runM $ Time.runIO Time.oneHourAgo
    mbOutpathsInfo <- liftIO $ readIORef (mergeBaseOutpathsInfo context)
    mergeBaseOutpathSet <-
      if calcOutpaths && lastUpdated mbOutpathsInfo < oneHourAgo
        then do
          mbos <- currentOutpathSet
          now <- liftIO getCurrentTime
          liftIO $
            writeIORef (mergeBaseOutpathsInfo context) (MergeBaseOutpathsInfo now mbos)
          return mbos
        else
          if calcOutpaths
            then return $ mergeBaseOutpaths mbOutpathsInfo
            else return $ dummyOutpathSetBefore attrPath
    --
    -- Get the original values for diffing purposes
    derivationContents <- liftIO $ T.readFile derivationFile
    oldHash <- Nix.getOldHash attrPath
    oldSrcUrl <- Nix.getSrcUrl attrPath
    --
    -- One final filter
    Blacklist.content derivationContents
    --
    ----------------------------------------------------------------------------
    -- UPDATES
    -- At this point, we've stashed the old derivation contents and validated
    -- that we actually should be touching this file. Get to work processing the
    -- various rewrite functions!
    let rwArgs = Rewrite.Args context attrPath derivationFile derivationContents
    rewriteMsgs <- Rewrite.runAll rwArgs
    ----------------------------------------------------------------------------
    --
    -- Compute the diff and get updated values
    diffAfterRewrites <- Git.diff
    lift . (log context) $ "Diff after rewrites:\n" <> diffAfterRewrites
    updatedDerivationContents <- liftIO $ T.readFile derivationFile
    newSrcUrl <- Nix.getSrcUrl attrPath
    newHash <- Nix.getHash attrPath
    -- Sanity checks to make sure the PR is worth opening
    when (derivationContents == updatedDerivationContents) $ throwE "No rewrites performed on derivation."
    when (oldSrcUrl == newSrcUrl) $ throwE "Source url did not change. "
    when (oldHash == newHash) $ throwE "Hashes equal; no update necessary"
    editedOutpathSet <- if calcOutpaths then currentOutpathSet else return $ dummyOutpathSetAfter attrPath
    let opDiff = S.difference mergeBaseOutpathSet editedOutpathSet
    let numPRebuilds = numPackageRebuilds opDiff
    Blacklist.python numPRebuilds derivationContents
    when (numPRebuilds == 0) (throwE "Update edits cause no rebuilds.")
    Nix.build attrPath
    --
    -- Publish the result
    lift . (log context) $ "Successfully finished processing"
    result <- Nix.resultLink
    publishPackage context oldSrcUrl newSrcUrl attrPath result (Just opDiff) rewriteMsgs
    Git.cleanAndResetTo "master"

publishPackage ::
  Context ->
  Text ->
  Text ->
  Text ->
  Text ->
  Maybe (Set ResultLine) ->
  [Text] ->
  ExceptT Text IO ()
publishPackage context oldSrcUrl newSrcUrl attrPath result opDiff rewriteMsgs = do
  let uEnv = updateEnv context
  let prBase =
        if (isNothing opDiff || numPackageRebuilds (fromJust opDiff) < 100)
        then "master"
        else "staging"
  cachixTestInstructions <- doCachix context result
  resultCheckReport <-
    case Blacklist.checkResult (packageName uEnv) of
      Right () -> lift $ Check.result context (T.unpack result)
      Left msg -> pure msg
  metaDescription <- Nix.getDescription attrPath <|> return T.empty
  metaHomepage <- Nix.getHomepageET attrPath <|> return T.empty
  metaChangelog <- Nix.getChangelog attrPath <|> return T.empty
  cveRep <- liftIO $ cveReport context
  releaseUrl <- GH.releaseUrl context newSrcUrl <|> return ""
  compareUrl <- GH.compareUrl oldSrcUrl newSrcUrl <|> return ""
  maintainers <- Nix.getMaintainers attrPath
  let commitMsg = commitMessage context attrPath
  Git.commit commitMsg
  commitHash <- Git.headHash
  nixpkgsReviewMsg <-
    if prBase /= "staging" && (runNixpkgsReview . options $ context)
      then liftIO $ NixpkgsReview.runReport (Utils.log context) commitHash
      else return ""
  -- Try to push it three times
  when
    (doPR . options $ context)
    (Git.push context <|> Git.push context <|> Git.push context)
  isBroken <- Nix.getIsBroken attrPath
  when
    (batchUpdate . options $ context)
    (lift untilOfBorgFree)
  let prMsg =
        prMessage
          context
          isBroken
          metaDescription
          metaHomepage
          metaChangelog
          rewriteMsgs
          releaseUrl
          compareUrl
          resultCheckReport
          commitHash
          attrPath
          maintainers
          result
          (fromMaybe "" (outpathReport <$> opDiff))
          cveRep
          cachixTestInstructions
          nixpkgsReviewMsg
  liftIO $ (log context) prMsg
  if (doPR . options $ context)
    then do
      -- FIXME: #192 This needs to be detected dynamically. Use the hub token or GH library?
      let ghUser = "r-ryantm"
      pullRequestUrl <- GH.pr context (prTitle (updateEnv context) attrPath) prMsg (ghUser <> ":" <> (branchName uEnv)) prBase
      liftIO $ (log context) pullRequestUrl
    else liftIO $ T.putStrLn prMsg

commitMessage :: Context -> Text -> Text
commitMessage context attrPath = prTitle (updateEnv context) attrPath

brokenWarning :: Bool -> Text
brokenWarning False = ""
brokenWarning True =
  "- WARNING: Package has meta.broken=true; Please manually test this package update and remove the broken attribute."

prMessage ::
  Context ->
  Bool ->
  Text ->
  Text ->
  Text ->
  [Text] ->
  Text ->
  Text ->
  Text ->
  Text ->
  Text ->
  Text ->
  Text ->
  Text ->
  Text ->
  Text ->
  Text ->
  Text
prMessage context isBroken metaDescription metaHomepage metaChangelog rewriteMsgs releaseUrl compareUrl resultCheckReport commitHash attrPath maintainers resultPath opReport cveRep cachixTestInstructions nixpkgsReviewMsg =
  -- Some components of the PR description are pre-generated prior to calling
  -- because they require IO, but in general try to put as much as possible for
  -- the formatting into the pure function so that we can control the body
  -- formatting in one place and unit test it.
  let brokenMsg = brokenWarning isBroken
      metaHomepageLine =
        if metaHomepage == T.empty
          then ""
          else "meta.homepage for " <> attrPath <> " is: " <> metaHomepage
      metaDescriptionLine =
        if metaDescription == T.empty
          then ""
          else "meta.description for " <> attrPath <> " is: " <> metaDescription
      metaChangelogLine =
        if metaDescription == T.empty
          then ""
          else "meta.changelog for " <> attrPath <> " is: " <> metaChangelog
      rewriteMsgsLine = foldl (\ms m -> ms <> T.pack "\n- " <> m) "\n###### Updates performed" rewriteMsgs
      maintainersCc =
        if not (T.null maintainers)
          then "cc " <> maintainers <> " for testing."
          else ""
      releaseUrlMessage =
        if releaseUrl == T.empty
          then ""
          else "- [Release on GitHub](" <> releaseUrl <> ")"
      compareUrlMessage =
        if compareUrl == T.empty
          then ""
          else "- [Compare changes on GitHub](" <> compareUrl <> ")"
      nixpkgsReviewSection =
        if nixpkgsReviewMsg == T.empty
          then "NixPkgs review skipped"
          else [interpolate|
            We have automatically built all packages that will get rebuilt due to
            this change.

            This gives evidence on whether the upgrade will break dependent packages.
            Note sometimes packages show up as _failed to build_ independent of the
            change, simply because they are already broken on the target branch.

            $nixpkgsReviewMsg
            |]
      pat link = [interpolate|This update was made based on information from $link.|]
      sourceLinkInfo = maybe "" pat $ sourceURL (updateEnv context)
   in [interpolate|
       Semi-automatic update generated by [nixpkgs-update](https://github.com/ryantm/nixpkgs-update) tools. $sourceLinkInfo
       $brokenMsg

       $metaDescriptionLine

       $metaHomepageLine

       $metaChangelogLine

       $rewriteMsgsLine

       ###### To inspect upstream changes

       $releaseUrlMessage

       $compareUrlMessage

       ###### Impact

       <details>
       <summary>
       <b>Checks done</b> (click to expand)
       </summary>

       ---

       - built on NixOS
       $resultCheckReport

       ---

       </details>
       <details>
       <summary>
       <b>Rebuild report</b> (if merged into master) (click to expand)
       </summary>

       ```
       $opReport
       ```

       </details>

       <details>
       <summary>
       <b>Instructions to test this update</b> (click to expand)
       </summary>

       ---

       $cachixTestInstructions
       ```
       nix-build -A $attrPath https://github.com/r-ryantm/nixpkgs/archive/$commitHash.tar.gz
       ```

       After you've downloaded or built it, look at the files and if there are any, run the binaries:
       ```
       ls -la $resultPath
       ls -la $resultPath/bin
       ```

       ---

       </details>
       <br/>

       $cveRep

       ### Pre-merge build results

       $nixpkgsReviewSection

       ---

       ###### Maintainer pings

       $maintainersCc
    |]

untilOfBorgFree :: MonadIO m => m ()
untilOfBorgFree = do
  stats <-
    shell "curl -s https://events.nix.ci/stats.php" & readProcessInterleaved_
  waiting <-
    shell "jq .evaluator.messages.waiting" & setStdin (byteStringInput stats)
      & readProcessInterleaved_
      & fmap (BSL.readInt >>> fmap fst >>> fromMaybe 0)
  when (waiting > 2) $ do
    liftIO $ threadDelay 60000000
    untilOfBorgFree

assertNotUpdatedOn ::
  MonadIO m => UpdateEnv -> FilePath -> Text -> ExceptT Text m ()
assertNotUpdatedOn uEnv derivationFile branch = do
  Git.cleanAndResetTo branch
  derivationContents <- fmapLT tshow $ tryIO $ T.readFile derivationFile
  Nix.assertOldVersionOn uEnv branch derivationContents

addPatched :: Text -> Set CVE -> IO [(CVE, Bool)]
addPatched attrPath set = do
  let list = S.toList set
  forM
    list
    ( \cve -> do
        patched <- runExceptT $ Nix.hasPatchNamed attrPath (cveID cve)
        let p =
              case patched of
                Left _ -> False
                Right r -> r
        return (cve, p)
    )

cveReport :: Context -> IO Text
cveReport context =
  let uEnv = updateEnv context in
  if not (makeCVEReport . options $ context)
    then return ""
    else withVulnDB $ \conn -> do
      let pname1 = packageName (uEnv)
      let pname2 = T.replace "-" "_" pname1
      oldCVEs1 <- getCVEs conn pname1 (oldVersion uEnv)
      oldCVEs2 <- getCVEs conn pname2 (oldVersion uEnv)
      let oldCVEs = S.fromList (oldCVEs1 ++ oldCVEs2)
      newCVEs1 <- getCVEs conn pname1 (newVersion uEnv)
      newCVEs2 <- getCVEs conn pname2 (newVersion uEnv)
      let newCVEs = S.fromList (newCVEs1 ++ newCVEs2)
      let inOldButNotNew = S.difference oldCVEs newCVEs
          inNewButNotOld = S.difference newCVEs oldCVEs
          inBoth = S.intersection oldCVEs newCVEs
          ifEmptyNone t =
            if t == T.empty
              then "none"
              else t
      inOldButNotNew' <- addPatched (packageName uEnv) inOldButNotNew
      inNewButNotOld' <- addPatched (packageName uEnv) inNewButNotOld
      inBoth' <- addPatched (packageName uEnv) inBoth
      let toMkdownList = fmap (uncurry cveLI) >>> T.unlines >>> ifEmptyNone
          fixedList = toMkdownList inOldButNotNew'
          newList = toMkdownList inNewButNotOld'
          unresolvedList = toMkdownList inBoth'
      if fixedList == "none" && unresolvedList == "none" && newList == "none"
        then return ""
        else
          return
            [interpolate|
      ###### Security vulnerability report

      <details>
      <summary>
      Security report (click to expand)
      </summary>

      CVEs resolved by this update:
      $fixedList

      CVEs introduced by this update:
      $newList

      CVEs present in both versions:
      $unresolvedList


       </details>
       <br/>
      |]

doCachix :: Context -> Text -> ExceptT Text IO Text
doCachix context resultPath =
  if pushToCachix (options context)
    then do
      lift $ (log context) ("cachix " <> (T.pack . show) resultPath)
      Nix.cachix resultPath
      return
        [interpolate|
       Either **download from Cachix**:
       ```
       nix-store -r $resultPath \
         --option binary-caches 'https://cache.nixos.org/ https://r-ryantm.cachix.org/' \
         --option trusted-public-keys '
         r-ryantm.cachix.org-1:gkUbLkouDAyvBdpBX0JOdIiD2/DP1ldF3Z3Y6Gqcc4c=
         cache.nixos.org-1:6NCHdD59X431o0gWypbMrAURkbJ16ZPMQFGspcDShjY=
         '
       ```
       (r-ryantm's Cachix cache is only trusted for this store-path realization.)
       For the Cachix download to work, your user must be in the `trusted-users` list or you can use `sudo` since root is effectively trusted.

       Or, **build yourself**:
       |]
    else do
      lift $ (log context) "skipping cachix"
      return "Build yourself:"

-- FIXME: We should delete updatePackageBatch, and instead have the updateLoop
-- just call updatePackage, so we aren't maintaining two parallel
-- implementations!
updatePackage ::
  Options ->
  Text ->
  IO (Either Text ())
updatePackage o updateInfo = do
  runExceptT $ do
    let (p, oldV, newV, url) = head (rights (parseUpdates updateInfo))
    let uEnv = UpdateEnv p oldV newV url
    let l = T.putStrLn
    let context = Context o undefined uEnv l
    liftIO $ notifyOptions l o
    --
    -- Update our git checkout and swap onto the update branch
    Git.fetchIfStale <|> liftIO (T.putStrLn "Failed to fetch.")
    Git.cleanAndResetTo "master"
    Git.checkoutAtMergeBase (branchName uEnv)
    -- Gather some basic information
    Nix.assertNewerVersion uEnv
    attrPath <- Nix.lookupAttrPath uEnv
    Version.assertCompatibleWithPathPin uEnv attrPath
    derivationFile <- Nix.getDerivationFile attrPath
    --
    -- Get the original values for diffing purposes
    derivationContents <- liftIO $ T.readFile derivationFile
    oldHash <- Nix.getOldHash attrPath
    oldSrcUrl <- Nix.getSrcUrl attrPath
    --
    ----------------------------------------------------------------------------
    -- UPDATES
    -- At this point, we've stashed the old derivation contents and validated
    -- that we actually should be touching this file. Get to work processing the
    -- various rewrite functions!
    let rwArgs = Rewrite.Args context attrPath derivationFile derivationContents
    msgs <- Rewrite.runAll rwArgs
    ----------------------------------------------------------------------------
    --
    -- Compute the diff and get updated values
    diffAfterRewrites <- Git.diff
    lift . l $ "Diff after rewrites:\n" <> diffAfterRewrites
    updatedDerivationContents <- liftIO $ T.readFile derivationFile
    newSrcUrl <- Nix.getSrcUrl attrPath
    newHash <- Nix.getHash attrPath
    -- Sanity checks to make sure the PR is worth opening
    when (derivationContents == updatedDerivationContents) $ throwE "No rewrites performed on derivation."
    when (oldSrcUrl == newSrcUrl) $ throwE "Source url did not change. "
    when (oldHash == newHash) $ throwE "Hashes equal; no update necessary"
    Nix.build attrPath
    --
    -- Publish the result
    lift . l $ "Successfully finished processing"
    result <- Nix.resultLink
    publishPackage context oldSrcUrl newSrcUrl attrPath result Nothing msgs
