module Main where

import Control.Monad (when)
import Control.Monad.State (evalState)
import Control.Monad.Trans.Maybe (runMaybeT)
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
import Prettyprinter.Render.Text (putDoc)
import System.Exit (exitFailure)

import Utils.Pretty (docToString)
import Utils.SMT (SMTSolver,smtSolverFromString,z3,cvc5,yices)
import Utils.InputProcessing (InputType(..),processInput)
import Utils.App (InputFormat(..),inputFormatFromString,chooseParser,printES,wrapWithTimeMeasurement)
import Typ.Type (Sort)
import Term.Type (FunTypMap)
import Equation.Type (ES)
import qualified Equation.CriticalPairs as CP
import Confluence


data Args = Args
  { inputFile :: String
  , inputFormat :: InputFormat
  , method :: Maybe ConfMethod
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
                    DPRS
                    False
                    (leftLinearRestriction (method args))
                    (prsRestriction (method args))
                    (chooseParser (inputFormat args)) of
    Left e -> do
      putStrLn "ERROR"
      putStr e
      exitFailure
    Right (n,ss,cs,ee,pd,axs,conjs) -> do
      confluence (method args) n (smtSolver args) (verbose args)  (debug args) ss cs axs
      return (verbose args)

prsRestriction :: Maybe ConfMethod -> Bool
prsRestriction (Just DC) = True
prsRestriction _ = False

leftLinearRestriction :: Maybe ConfMethod -> Bool
leftLinearRestriction (Just OR) = True
leftLinearRestriction (Just DC) = True
leftLinearRestriction _ = False

confluence :: Maybe ConfMethod -> Int -> SMTSolver -> Bool -> Bool -> [Sort] -> FunTypMap -> ES -> IO ()
confluence mcm n s v d bts fTyM dprs = case evalState (runMaybeT $ CP.criticalPairs dprs dprs) n of
  Nothing -> do
    putStrLn "MAYBE"
    when v . printES "input DPRS:" $ dprs
    when v . putStrLn $ "\npossibly infinite behavior underlying unification\n"
  Just cpairs -> let
    confFun = case mcm of
      Just cm  -> checkConfluence cm
      Nothing  -> confluenceStrategy [OR,DC,KB]
    in do
      res <- confFun s d bts fTyM dprs cpairs
      putStrLn . show . confluenceStatus $ res
      when v . printES "input DPRS:" $ dprs
      when v . putDoc $ confluenceResultDoc res

opts :: ParserInfo Args
opts = info (argsParser <**> helper)
  ( fullDesc
  <> progDesc ("reads a file containing an DPRS " ++
               "and performs confluence analysis")
  <> header "hrstk - confluence tool" )

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
     <> metavar "ortho | dc | lc | kb"
     <> help "specific confluence method" )
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

methodFromString :: String -> Either String (Maybe ConfMethod)
methodFromString "ortho" = Right (Just OR)
methodFromString "dc" = Right (Just DC)
methodFromString "lc" = Right (Just LC)
methodFromString "kb" = Right (Just KB)
methodFromString _ = Left "supported confluence methods are 'ortho', 'dc', 'lc' and 'kb'"
