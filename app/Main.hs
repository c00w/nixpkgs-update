{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}

module Main where

import Control.Applicative ((<**>))
import qualified Data.Text as T
import qualified Data.Text.IO as T
import DeleteMerged (deleteDone)
import NVD (withVulnDB)
import qualified Nix
import qualified Options.Applicative as O
import OurPrelude
import qualified Repology
import System.IO (BufferMode (..), hSetBuffering, stderr, stdout)
import qualified System.Posix.Env as P
import Update (cveReport, updateAll, updatePackage)
import Utils (Context (..), Options (..), UpdateEnv (..), getGithubToken)
import Git

default (T.Text)

data UpdateOptions
  = UpdateOptions
      { pr :: Bool,
        cve :: Bool,
        cachix :: Bool,
        nixpkgsReview :: Bool,
        outpaths :: Bool
      }

data Command
  = UpdateList UpdateOptions
  | Update UpdateOptions Text
  | DeleteDone
  | Version
  | UpdateVulnDB
  | FetchRepology
  | CheckVulnerable Text Text Text

updateOptionsParser :: O.Parser UpdateOptions
updateOptionsParser =
  UpdateOptions
    <$> O.flag False True (O.long "pr" <> O.help "Make a pull request using Hub.")
    <*> O.flag False True (O.long "cve" <> O.help "Make a CVE vulnerability report.")
    <*> O.flag False True (O.long "cachix" <> O.help "Push changes to Cachix")
    <*> O.flag False True (O.long "nixpkgs-review" <> O.help "Runs nixpkgs-review on update commit rev")
    <*> O.flag False True (O.long "outpaths" <> O.help "Calculate outpaths to determine the branch to target")

updateParser :: O.Parser Command
updateParser =
  Update
    <$> updateOptionsParser
    <*> O.strArgument (O.metavar "UPDATE_INFO" <> O.help "update string of the form: 'pkg oldVer newVer update-page'\n\n example: 'tflint 0.15.0 0.15.1 repology.org'")

commandParser :: O.Parser Command
commandParser =
  O.hsubparser
    ( O.command
        "update-list"
        (O.info (UpdateList <$> updateOptionsParser) (O.progDesc "Update a list of packages"))
        <> O.command
          "update"
          (O.info (updateParser) (O.progDesc "Update one package"))
        <> O.command
          "delete-done"
          ( O.info
              (pure DeleteDone)
              (O.progDesc "Deletes branches from PRs that were merged or closed")
          )
        <> O.command
          "version"
          ( O.info
              (pure Version)
              ( O.progDesc
                  "Displays version information for nixpkgs-update and dependencies"
              )
          )
        <> O.command
          "update-vulnerability-db"
          ( O.info
              (pure UpdateVulnDB)
              (O.progDesc "Updates the vulnerability database")
          )
        <> O.command
          "check-vulnerable"
          (O.info checkVulnerable (O.progDesc "checks if something is vulnerable"))
        <> O.command
          "fetch-repology"
          (O.info (pure FetchRepology) (O.progDesc "fetches update from Repology and prints them to stdout"))
    )

checkVulnerable :: O.Parser Command
checkVulnerable =
  CheckVulnerable <$> O.strArgument (O.metavar "PRODUCT_ID")
    <*> O.strArgument (O.metavar "OLD_VERSION")
    <*> O.strArgument (O.metavar "NEW_VERSION")

programInfo :: O.ParserInfo Command
programInfo =
  O.info
    (commandParser <**> O.helper)
    ( O.fullDesc
        <> O.progDesc "Update packages in the Nixpkgs repository"
        <> O.header "nixpkgs-update"
    )

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  hSetBuffering stderr LineBuffering
  command <- O.execParser programInfo
  case command of
    DeleteDone -> do
      token <- getGithubToken
      Git.setupNixpkgs token
      P.setEnv "GITHUB_TOKEN" (T.unpack token) True
      deleteDone token
    UpdateList UpdateOptions {pr, cachix, cve, nixpkgsReview, outpaths} -> do
      token <- getGithubToken
      updates <- T.readFile "packages-to-update.txt"
      Git.setupNixpkgs token
      P.setEnv "PAGER" "" True
      P.setEnv "GITHUB_TOKEN" (T.unpack token) True
      updateAll (Options pr True token cve cachix nixpkgsReview outpaths) updates
    Update UpdateOptions {pr, cve, cachix, nixpkgsReview} update -> do
      token <- getGithubToken
      Git.setupNixpkgs token
      P.setEnv "PAGER" "" True
      P.setEnv "GITHUB_TOKEN" (T.unpack token) True
      result <- updatePackage (Options pr False token cve cachix nixpkgsReview False) update
      case result of
        Left e -> T.putStrLn e
        Right () -> T.putStrLn "Done."
    Version -> do
      v <- runExceptT Nix.version
      case v of
        Left t -> T.putStrLn ("error:" <> t)
        Right t -> T.putStrLn t
    UpdateVulnDB -> withVulnDB $ \_conn -> pure ()
    CheckVulnerable productID oldVersion newVersion -> do
      setupNixpkgs undefined
      report <-
        cveReport
          (Context
            (Options False False undefined True False False False)
            undefined
            (UpdateEnv productID oldVersion newVersion Nothing)
            undefined)
      T.putStrLn report
    FetchRepology -> Repology.fetch
