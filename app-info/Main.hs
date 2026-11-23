{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}

module Main where

import Control.Monad (when)
import Data.Char (toLower)
import qualified Data.Text.IO as TIO
import Options.Applicative
    ( (<**>),
      argument,
      eitherReader,
      fullDesc,
      header,
      help,
      info,
      long,
      metavar,
      option,
      progDesc,
      short,
      showDefault,
      str,
      switch,
      value,
      execParser,
      helper,
      Parser,
      ParserInfo )
import Prettyprinter (pretty)
import System.Exit (exitFailure)

import Utils.Pretty (docToString)
import Utils.InputProcessing (InputType(..),processInput)
import Utils.App (InputFormat(..),inputFormatFromString,chooseParser,printES,wrapWithTimeMeasurement)
import Equation.Type (ES)
import Equation.Ops (rule, epatRule, dhpRule, patternRule, leftLinear, secondOrderEq)

data Args = Args
  { inputFile :: String
  , inputFormat :: InputFormat
  , verbose :: Bool
  }

main :: IO ()
main = wrapWithTimeMeasurement work

work :: IO Bool
work = do
  args <- execParser opts
  input <- TIO.readFile (inputFile args)
  case processInput (inputFile args)
                    input
                    HES
                    False
                    False
                    False
                    (chooseParser (inputFormat args)) of
    Left e -> do
      putStrLn "ERROR"
      putStr e
      exitFailure
    Right (n,ss,cs,ee,pd,axs,conjs) -> do
      esInfo (verbose args) ee pd axs
      return (verbose args)


-- |Checks input type of ES
esTyp :: ES -> InputType
esTyp es 
  | not (all rule es)        = HES
  | not (all epatRule es)    = HRS
  | not (all dhpRule es)     = EPRS
  | not (all patternRule es) = DPRS
  | otherwise                = PRS

esInfo :: Bool -> Bool -> Bool -> ES -> IO ()
esInfo v ee pd es = do
    putStr . docToString . pretty $ esTyp es
    if all leftLinear es
      then putStr " left-linear"
      else pure ()
    if all secondOrderEq es
      then putStr " second-order"
      else pure ()
    case (ee,pd) of
      (False,True) -> putStrLn " (modifications: eta-expanded, pulled down to sort)"
      (False,False) -> putStrLn " (modification: eta-expanded)"
      (True,True) -> putStrLn " (modification: pulled down to sort)"
      _ -> putStrLn ""
    when v $ printES "input:" es

opts :: ParserInfo Args
opts = info (argsParser <**> helper)
  ( fullDesc
  <> progDesc ("reads a file containing an HES/HRS " ++
               "and prints information about input (processing)")
  <> header "hrstk - info" )

argsParser :: Parser Args
argsParser = Args
  <$> argument str
      ( metavar "FILE"
     <> help "input file" )
  <*> option (eitherReader $ inputFormatFromString . map toLower)
      ( long "input-format"
     <> short 'i'
     <> showDefault
     <> value ARI
     <> metavar "ari | tptp"
     <> help "input format" )
  <*> switch
      ( long "verbose"
     <> short 'v'
     <> help "more output information" )
