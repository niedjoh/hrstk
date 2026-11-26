{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Main where

import Control.Applicative (some)
import Data.Char (toLower)
import Data.Text (Text)
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
import Prettyprinter (Doc,pretty,line,emptyDoc,(<+>))
import Prettyprinter.Render.Text (putDoc)
import System.Exit (exitFailure)

import Utils.SMT (SMTSolver,smtSolverFromString,cvc5)
import Utils.Parse (parseProblem,scARI)
import Utils.InputProcessing (InputType(..),processInput)
import Utils.App (wrapWithTimeMeasurement)
import Equation.Ops (canonicalFVrename)
import DuplicateChecker (DCProblem(..),toTypSkeletonFunsMap,duplicates)
import qualified ARI

data Args = Args
  { inputFiles :: [String]
  , smtSolver :: SMTSolver
  , verbose :: Bool
  , debug :: Bool
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
      ds <- duplicates (smtSolver args) (debug args) ps
      putDoc . duplicatesDoc $ ds
      -- verbose output??
      return (verbose args)

processInputs :: [String] -> [Text] -> Either String [DCProblem]
processInputs fs is =
    traverse
    (\(f,i) ->  (\(_,ss,fTyM,_,_,es,_) -> DCProblem { file = f
                                                    , sorts = ss
                                                    , funTypMap = fTyM
                                                    , typSkeletonFunsMap = toTypSkeletonFunsMap fTyM
                                                    , equations = map canonicalFVrename es
                                                    }) <$>
     processInput f i HES False False False (parseProblem scARI (ARI.parser))
    )
    (zip fs is)

duplicatesDoc :: [(DCProblem,DCProblem)] -> Doc ann
duplicatesDoc [] = emptyDoc
duplicatesDoc ((x,y):ps) = pretty (file x) <+> "==" <+> pretty (file y) <> line <> duplicatesDoc ps

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
  <*> option (eitherReader $ smtSolverFromString . map toLower)
      ( long "smt-solver"
     <> short 's'
     <> showDefault
     <> value cvc5
     <> metavar "cvc5 | yices | z3"
     <> help "SMT solver" )
  <*> switch
      ( long "verbose"
     <> short 'v'
     <> help "more output information" )
  <*> switch
      ( long "debug"
     <> short 'd'
     <> help "output SMT debug information" )
