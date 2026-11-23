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

import Utils.InputProcessing (InputType(..),processInput)
import Utils.App (InputFormat(..),inputFormatFromString,chooseParser,printES,wrapWithTimeMeasurement)
import Equation.Type (Equation(..),ES)
import qualified Subst.Unif as Unif

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
                    DHPUnifProblem
                    False
                    False
                    False
                    (chooseParser (inputFormat args)) of
    Left e -> do
      putStrLn "ERROR"
      putStr e
      exitFailure
    Right (n,_,_,_,_,axs,_) -> do
      unification n (verbose args) axs
      return (verbose args)

unification :: Int -> Bool -> ES -> IO ()
unification n v (e:_) = case evalState (runMaybeT $ Unif.unif (lhs e) (rhs e)) n of
  Nothing -> do
    putStrLn "MAYBE"
    when v . printES "input DHP unification problem:" $ [e]
    when v . putStrLn $ "\npossibly infinite behavior\n"
  Just substs -> do
    if null substs
      then putStrLn "NO"
      else putStrLn "YES"
    when v . putDoc $ Unif.resultDoc e substs
unification _ _ _ = do
  putStrLn "ERROR"
  putStrLn "unification problem empty"

opts :: ParserInfo Args
opts = info (argsParser <**> helper)
  ( fullDesc
  <> progDesc ("reads a file containing a DHP equation " ++
               "and performs DHP unification")
  <> header "hrstk - DHP unification tool" )

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
