{-# LANGUAGE OverloadedStrings #-}

module Utils.App where

import Control.Monad (when)
import Data.Time (getCurrentTime,diffUTCTime)
import Fmt ((+|),(|+),fixedF,fmtLn)
import Prettyprinter (pretty,vsep)
import Prettyprinter.Render.Text (putDoc)

import Utils.Parse (ProblemParser,parseProblem,scARI,scTPTP)
import Utils.Pretty (prettyNList)
import Equation.Type (ES)
import qualified TPTP
import qualified ARI

data InputFormat = ARI | TPTP

instance Show InputFormat where
  show ARI = "ari"
  show TPTP = "tptp"

inputFormatFromString :: String -> Either String InputFormat
inputFormatFromString "ari" = Right ARI
inputFormatFromString "tptp" = Right TPTP
inputFormatFromString _ = Left "supported input formats are 'ari' and 'tptp'"

chooseParser :: InputFormat -> ProblemParser
chooseParser ARI = parseProblem scARI (ARI.parser)
chooseParser TPTP = parseProblem scTPTP (TPTP.parser)

printES :: String -> ES -> IO ()
printES s es = do
  putStrLn ""
  putStrLn s
  putStrLn ""
  if null es
    then putStrLn "none"
    else putDoc . vsep $ map pretty es

printNES :: String -> ES -> IO ()
printNES s es = do
  putStrLn ""
  putStrLn s
  putStrLn ""
  if null es
    then putStrLn "none"
    else putDoc . prettyNList . map pretty $ es

wrapWithTimeMeasurement :: IO Bool -> IO ()
wrapWithTimeMeasurement work = do
  start <- getCurrentTime
  vb <- work
  stop <- getCurrentTime
  when vb . fmtLn $ "\n\ntime: " +|fixedF 3  (diffUTCTime stop start)|+"s" 
