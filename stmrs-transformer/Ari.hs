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
import System.IO (withFile, IOMode(..), hPutStrLn, Handle)



-- | Takes a target filename (e.g., "output.ari") and your Equation System,
-- formats it, and saves it to the disk.
saveToAriFile :: FilePath -> ES -> [String] -> IO ()
saveToAriFile filename equations metadata = do
    
    let metadataDoc = vsep (map pretty metadata)
    -- 1. Generate your fully formatted .ari Document
    let eqDoc = prettyAriSystem equations

    let finalDoc = metadataDoc <> hardline <> eqDoc
    
    -- 2. Layout the document 
    -- (This step calculates line breaks and spacing based on the document)
    let layout = layoutPretty defaultLayoutOptions finalDoc
    
    -- 3. Render the layout into a strict Data.Text object
    -- (This strips away the 'prettyprinter' wrapper and gives you raw text)
    let textOutput = renderStrict layout
    
    -- 4. Write the text directly to the file!
    TIO.writeFile filename textOutput
    
    putStrLn $ "Successfully exported rules to: " ++ filename


changeLHSs :: ES -> [Term] -> ES
changeLHSs [] [] = []
changeLHSs (axiom:xs) (l:ls) = axiom{lhs = l} : changeLHSs xs ls


splitAriFile :: [String] -> ([String], [String])
splitAriFile lines = partition isRuleLine lines
  where isRuleLine l = "(rule" `isPrefixOf` l

changeFileName :: String -> String
changeFileName name = left ++ "_transformed" ++ right
 where (left,right) = splitAfter (== '.') name

splitAfter :: (a-> Bool) -> [a] -> ([a],[a])
splitAfter this xs = case findIndex this xs of
  Nothing -> (xs,[])
  Just n -> splitAt (n) xs

-- | Recursively finds all .ari files in a given directory
getAriFiles :: FilePath -> IO [FilePath]
getAriFiles path = do
    isDirectory <- doesDirectoryExist path
    if isDirectory
        then do
            contents <- listDirectory path
            let fullPaths = map (path </>) contents
            concat <$> mapM getAriFiles fullPaths
        else return [path | takeExtension path == ".ari"]

processAriFile :: Handle -> FilePath -> FilePath -> IO ()
processAriFile h targetDir file = do
    hPutStrLn h $ "\n-----------------------------------"
    hPutStrLn h $ "Processing: " ++ file
    
    let cleanTarget = dropTrailingPathSeparator targetDir
    let (start,end) = splitFileName cleanTarget
    let relFile = makeRelative targetDir file
    let outPath = ((start </> "output") </> end) </> relFile
    createDirectoryIfMissing True (takeDirectory outPath)
    
    input <- TIO.readFile file

    rawLines <- lines <$> readFile file
    let (_,metadata) = splitAriFile rawLines
    let ariParser = parseProblem scARI ARI.parser

    case processInput file input HRS False False False ariParser of
        Left errorMsg -> do
          hPutStrLn h "--- PARSE ERROR ---"
          hPutStrLn h errorMsg
          
        Right (vars, sorts, funTypeMap, isEta, containsFun, axioms, conjectures) -> do
          hPutStrLn h $ "Parsed " ++ show (length axioms) ++ " rules."
          let lhss = map lhs axioms
          let results = map checkWellBehavedness lhss
          if all id results 
            then do
              hPutStrLn h "All the rules are already well-behaved"
              saveToAriFile outPath axioms metadata
            else do
              hPutStrLn h "Not all rules are well-behaved. Trying transformation."
              let result = map etaReduceFVLambdas lhss
              let isWellBehaved = all id $ map checkWellBehavedness result
              case isWellBehaved of
                False -> hPutStrLn h $ "The rules could not be transformed"
                _ -> do 
                  hPutStrLn h "The rules were successfully transformed"
                  saveToAriFile outPath (changeLHSs axioms result) metadata

    hPutStrLn h "Done."