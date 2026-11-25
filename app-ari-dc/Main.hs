{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Main where

import Control.Applicative (some)
import Data.Text (Text)
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
      progDesc,
      short,
      str,
      switch,
      execParser,
      helper,
      Parser,
      ParserInfo )
import System.Exit (exitFailure)

import Utils.Parse (parseProblem,scARI)
import Utils.InputProcessing (InputType(..),processInput)
import Utils.App (printES,wrapWithTimeMeasurement)
import Typ.Type (Sort)
import Term.Type (FunTypMap)
import Equation.Type (ES)
import Equation.Ops (canonicalFVrename)
import DuplicateChecker (TypSkeletonFunsMap,toTypSkeletonFunsMap)
import qualified ARI

data Args = Args
  { inputFiles :: [String]
  , verbose :: Bool
  }

main :: IO ()
main = wrapWithTimeMeasurement work

work :: IO Bool
work = do
  args <- execParser opts
  inputs <- mapM TIO.readFile (inputFiles args)
  case processInputs (inputFiles args) inputs of
    Left e -> do
      putStrLn "ERROR"
      putStr e
      exitFailure
    Right ps -> do
      -- mapM_ (\(f,_,_,es) -> printES f es >> putStrLn "") ps
      return (verbose args)

processInputs :: [String] -> [Text] -> Either String [(String,[Sort],FunTypMap,TypSkeletonFunsMap,ES)]
processInputs fs is =
    traverse
    (\(f,i) ->  (\(_,ss,fTyM,_,_,es,_) -> (f,ss,fTyM,toTypSkeletonFunsMap fTyM,map canonicalFVrename es)) <$>
     processInput f i HES False False False (parseProblem scARI (ARI.parser))
    )
    (zip fs is)

opts :: ParserInfo Args
opts = info (argsParser <**> helper)
  ( fullDesc
  <> progDesc ("reads higher-order ARI files " ++
               "and reports duplicates")
  <> header "hrstk - info" )

argsParser :: Parser Args
argsParser = Args
  <$> some (argument str
      ( metavar "FILES"
     <> help "input files" ))
  <*> switch
      ( long "verbose"
     <> short 'v'
     <> help "more output information" )
