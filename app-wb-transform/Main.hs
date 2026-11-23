{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Monad (forM_)
import Data.List (isPrefixOf,partition)
import qualified Data.Text.IO as TIO

import Options.Applicative
    ( (<**>),
      argument,
      fullDesc,
      header,
      help,
      info,
      long,
      metavar,
      optional,
      progDesc,
      short,
      str,
      strOption,
      switch,
      execParser,
      helper,
      Parser,
      ParserInfo )
import Prettyprinter (Doc,pretty,hardline,vsep)
import Prettyprinter.Render.Text (hPutDoc)
import System.Directory (doesDirectoryExist,listDirectory,createDirectoryIfMissing)
import System.FilePath ( (</>)
                       , takeExtension
                       , takeDirectory
                       , splitFileName
                       , makeRelative
                       , dropTrailingPathSeparator)
import System.IO (hPutStrLn, Handle, IOMode(..), stdout, withFile)

import Utils.InputProcessing (processInput, InputType(HRS))
import Utils.Parse (parseProblem, scARI)
import Utils.Pretty (prettyText)
import qualified ARI.Parse as ARI

import Term.Type (Term)
import Term.Ops (isEPAT,isPattern)
import Equation.Type (ES,Equation(..))
import ARI.Pretty (prettyARIsystem)
import WellBehaved

data Args = Args
  { inputFile :: FilePath
  , outName :: Maybe FilePath
  , outDir  :: Maybe FilePath
  , logFile :: Maybe FilePath
  , prsOnly   :: Bool
  }

main :: IO ()
main = do
    args <- execParser opts
    let inFile = inputFile args
    putStrLn $ "Scanning directory: " ++ inFile
    files <- getAriFiles inFile
    isDir <- doesDirectoryExist inFile
    putStrLn $ "Found " ++ show (length files) ++ " .ari files. Starting batch job..."
    withLogHandle (logFile args) $ \h -> do    
        hPutStrLn h $ "--- Starting Batch Job for " ++ inFile ++ " ---"
        hPutStrLn h $ "Found " ++ show (length files) ++ " files."
        forM_ files (processAriFile h inFile args isDir)
        hPutStrLn h "--- Batch Job Complete ---"
    putStrLn "Batch processing complete! Check batch_results.log for details."

transform :: FilePath -> FilePath -> Bool -> IO (Doc ann)
transform file outPath prsBool = do
  input <- TIO.readFile file
  rawLines <- lines <$> readFile file
  let (_,metadata) = splitAriFile rawLines
  let ariParser = parseProblem scARI ARI.parser
  case processInput file input HRS False False False ariParser of
      Left errorMsg -> 
        return $ "--- PARSE ERROR ---" <> hardline <> pretty errorMsg        
      Right (_, _, _, _, _, axioms, _) -> do
        let lhss = map lhs axioms
        if not (all isEPAT lhss)
          then do
            return "The given HRS is not an EPRS"
          else if prsBool && not (all isPattern lhss) then
            return "The given HRS is not a PRS (skipped because of --prs-only)"
            else do
            let results = map checkWellBehavedness lhss
            if and results 
              then do
                createDirectoryIfMissing True (takeDirectory outPath)
                saveToAriFile outPath axioms metadata
                return "All the rules are already well-behaved"
              else do
                let o1 = "Not all rules are well-behaved. Trying transformation."
                let result = map etaReduceAnchorsAtRoot lhss
                let isWellBehaved = all checkWellBehavedness result
                case isWellBehaved of
                  False -> do
                    let o2 = "The rules could not be transformed"
                    return $ o1 <> hardline <> o2
                  _ -> do 
                    let o2 = "The rules were successfully transformed"
                    createDirectoryIfMissing True (takeDirectory outPath)
                    saveToAriFile outPath (changeLHSs axioms result) metadata
                    return $ o1 <> hardline <> o2

getAriFiles :: FilePath -> IO [FilePath]
getAriFiles path = do
    isDirectory <- doesDirectoryExist path
    if isDirectory
      then do
          contents <- listDirectory path
          let fullPaths = map (path </>) contents
          concat <$> mapM getAriFiles fullPaths
      else return [path | takeExtension path == ".ari"]

splitAriFile :: [String] -> ([String], [String])
splitAriFile fileLines = partition isRuleLine fileLines
  where isRuleLine l = "(rule" `isPrefixOf` l
  
changeLHSs :: ES -> [Term] -> ES
changeLHSs (axiom:xs) (l:ls) = axiom{lhs = l} : changeLHSs xs ls
changeLHSs _ _ = []

saveToAriFile :: FilePath -> ES -> [String] -> IO ()
saveToAriFile filename equations metadata = TIO.writeFile filename textOutput where
  metadataDoc = vsep (map pretty metadata)
  eqDoc = prettyARIsystem equations
  textOutput = prettyText (metadataDoc <> hardline <> eqDoc)

computePath :: FilePath -> FilePath -> Args -> Bool -> FilePath
computePath target file args isDir =
  case (outDir args, outName args) of
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

processAriFile :: Handle -> FilePath -> Args -> Bool -> FilePath -> IO ()
processAriFile h targetDir args isDir file = do
  hPutStrLn h $ "-----------------------------------"
  hPutStrLn h $ "Processing: " ++ file  
  let outPath = computePath targetDir file args isDir
  transformMessage <- transform file outPath (prsOnly args)
  hPutDoc h (transformMessage <> hardline)

withLogHandle :: Maybe FilePath -> (Handle -> IO a) -> IO a
withLogHandle Nothing     act = act stdout
withLogHandle (Just file) act = withFile file WriteMode act

opts :: ParserInfo Args
opts = info (argsParser <**> helper)
   ( fullDesc 
   <> progDesc "transform higher-order ARI files representing EPRSs to well-behaved presentation"
   <> header "hrstk-wb-transformer" )

argsParser :: Parser Args
argsParser = Args
  <$> argument str (metavar "FILE|DIR")
  <*> optional (strOption (long "name"    <> short 'n' <> metavar "NAME"))
  <*> optional (strOption (long "out-dir" <> short 'o' <> metavar "DIR"))
  <*> optional (strOption (long "log"     <> short 'l' <> metavar "FILE"
                           <> help "write the log to FILE instead of stdout"))
  <*> switch (long "prs-only" <> help "only transform PRSs")
