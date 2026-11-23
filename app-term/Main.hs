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
import Prettyprinter.Render.Text (putDoc)
import System.Exit (exitFailure)

import Utils.SMT (SMTSolver,smtSolverFromString,z3,cvc5,yices)
import Utils.InputProcessing (InputType(..),processInput)
import Utils.App (InputFormat(..),inputFormatFromString,chooseParser,printES,wrapWithTimeMeasurement)
import Typ.Type (Sort)
import Term.Type (FunTypMap)
import Equation.Type (ES)
import Termination
data Args = Args
  { inputFile :: String
  , inputFormat :: InputFormat
  , method :: Maybe TermMethod
  , smtSolver :: SMTSolver
  , verbose :: Bool
  , debug :: Bool
  }

main :: IO ()
main = wrapWithTimeMeasurement work

work :: IO Bool
work = do
  args <- execParser opts
  input <- TIO.readFile (inputFile args)
  case processInput (inputFile args)
                    input
                    HRS
                    (secondOrderRestriction (method args))
                    False
                    False
                    (chooseParser (inputFormat args)) of
    Left e -> do
      putStrLn "ERROR"
      putStr e
      exitFailure
    Right (n,ss,cs,ee,pd,axs,conjs) -> do
      termination (method args) (smtSolver args) (verbose args) (debug args) ss cs axs
      return (verbose args)

secondOrderRestriction :: Maybe TermMethod -> Bool
secondOrderRestriction (Just Poly) = True
secondOrderRestriction _ = False

termination :: Maybe TermMethod -> SMTSolver -> Bool -> Bool -> [Sort] -> FunTypMap -> ES ->  IO ()
termination mtm s v d bts fTyM hrs = let
  termFun = case mtm of
    Just tm -> checkTermination tm
    Nothing -> terminationStrategy [NCPO,Poly]
  in do
    res  <- termFun s d bts fTyM hrs
    if terminationStatus res
      then do
        putStrLn "YES"
        when v . printES "input HRS:" $ hrs
      else do
        putStrLn "MAYBE"
        when v . printES "input HRS:" $ hrs
    when v . putDoc $ terminationResultDoc res

opts :: ParserInfo Args
opts = info (argsParser <**> helper)
  ( fullDesc
  <> progDesc ("reads a file containing an HRS " ++
               "and performs termination analysis")
  <> header "hrstk - termination tool" )

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
  <*> option (eitherReader $ methodFromString . map toLower)
      ( long "method"
     <> short 'm'
     <> showDefault
     <> value Nothing
     <> metavar "ncpo | poly | starcpo"
     <> help "specific termination method" )
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

methodFromString :: String -> Either String (Maybe TermMethod)
methodFromString "ncpo" = Right (Just NCPO)
methodFromString "poly" = Right (Just Poly)
methodFromString "starcpo" = Right (Just StarCPO)
methodFromString _ = Left "supported termination methods are 'ncpo', 'poly' and 'starcpo'"
