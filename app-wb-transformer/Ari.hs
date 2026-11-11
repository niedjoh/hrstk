{-# LANGUAGE OverloadedStrings #-}
module Ari where

import qualified Data.Text.IO as TIO
import Utils.InputProcessing (processInput, InputType(HRS))
import Utils.Parse (parseProblem, scARI)
import qualified ARI.Parse as ARI
import WellBehaved
import Pretty
import Equation.Type
import Term.Type
import Prettyprinter
import Prettyprinter.Render.Text (renderStrict)
import Data.List
import System.Directory (doesDirectoryExist, listDirectory, createDirectoryIfMissing)
import System.FilePath ((</>), takeExtension, takeDirectory, splitFileName, makeRelative, dropTrailingPathSeparator)
import System.IO (hPutStrLn, Handle, IOMode(..), stdout, withFile)
import Options.Applicative
import Control.Monad (forM_)


data Opts = Opts
  { inputFile   :: FilePath
  , outName :: Maybe FilePath
  , outDir  :: Maybe FilePath
  , logFile :: Maybe FilePath
  }

optsP :: Parser Opts
optsP = Opts
  <$> argument str (metavar "FILE|DIR")
  <*> optional (strOption (long "name"    <> short 'n' <> metavar "NAME"))
  <*> optional (strOption (long "out-dir" <> short 'o' <> metavar "DIR"))
  <*> optional (strOption (long "log"     <> short 'l' <> metavar "FILE"
                           <> help "Write the log to FILE instead of stdout"))


withLogHandle :: Maybe FilePath -> (Handle -> IO a) -> IO a
withLogHandle Nothing     act = act stdout
withLogHandle (Just file) act = withFile file WriteMode act


saveToAriFile :: FilePath -> ES -> [String] -> IO ()
saveToAriFile filename equations metadata = do
  let metadataDoc = vsep (map pretty metadata)

  let eqDoc = prettyAriSystem equations

  let finalDoc = metadataDoc <> hardline <> eqDoc
  
  let layout = layoutPretty defaultLayoutOptions finalDoc
  
  let textOutput = renderStrict layout

  TIO.writeFile filename textOutput


changeLHSs :: ES -> [Term] -> ES
changeLHSs (axiom:xs) (l:ls) = axiom{lhs = l} : changeLHSs xs ls
changeLHSs _ _ = []


splitAriFile :: [String] -> ([String], [String])
splitAriFile fileLines = partition isRuleLine fileLines
  where isRuleLine l = "(rule" `isPrefixOf` l

getAriFiles :: FilePath -> IO [FilePath]
getAriFiles path = do
    isDirectory <- doesDirectoryExist path
    if isDirectory
      then do
          contents <- listDirectory path
          let fullPaths = map (path </>) contents
          concat <$> mapM getAriFiles fullPaths
      else return [path | takeExtension path == ".ari"]


computePath :: FilePath -> FilePath -> Opts -> Bool -> FilePath
computePath target file opts isDir =
  case (outDir opts, outName opts) of
    (Nothing, Nothing)   -> start </> "output" </> end </> relFile
    (Just dir, Nothing)   -> dir </> end </> relFile
    (Nothing, Just name) | isDir     -> start </> name </> end </> relFile
                         | otherwise -> start </> name
    (Just dir, Just name) | isDir     -> dir </> name </> end </> relFile
                          | otherwise -> dir </> name
  where
    baseDir     = if isDir then target else takeDirectory target
    (start, end) = splitFileName (dropTrailingPathSeparator baseDir)
    relFile     = makeRelative baseDir file


processAriFile :: Handle -> FilePath -> Opts -> Bool -> FilePath -> IO ()
processAriFile h targetDir opts isDir file = do
  hPutStrLn h $ "-----------------------------------"
  hPutStrLn h $ "Processing: " ++ file
  
  let outPath = computePath targetDir file opts isDir
  
  transformMessage <- transform file outPath

  forM_ transformMessage $ \m -> do
    hPutStrLn h m


transform :: FilePath -> FilePath -> IO [String]
transform file outPath = do
  input <- TIO.readFile file

  rawLines <- lines <$> readFile file
  let (_,metadata) = splitAriFile rawLines
  let ariParser = parseProblem scARI ARI.parser

  case processInput file input HRS False False False ariParser of
      Left errorMsg -> do
        let er =  "--- PARSE ERROR ---"
        let er2 = errorMsg
        return [er, er2]
        
      Right (_, _, _, _, _, axioms, _) -> do
        let lhss = map lhs axioms
        if not (all isEPAT lhss)
          then do
            return ["The given HRS is not an EPRS"]
          else do
            let results = map checkWellBehavedness lhss
            if and results 
              then do
                createDirectoryIfMissing True (takeDirectory outPath)
                saveToAriFile outPath axioms metadata
                return ["All the rules are already well-behaved"]
              else do
                let o1 = "Not all rules are well-behaved. Trying transformation."
                let result = map etaReduceFVLambdas lhss
                let isWellBehaved = all checkWellBehavedness result
                case isWellBehaved of
                  False -> do
                    let o2 = "The rules could not be transformed"
                    return [o1, o2]
                  _ -> do 
                    let o2 = "The rules were successfully transformed"
                    createDirectoryIfMissing True (takeDirectory outPath)
                    saveToAriFile outPath (changeLHSs axioms result) metadata
                    return [o1, o2]