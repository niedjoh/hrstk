module Main where

import Control.Monad (unless,when)
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
import Utils.App (InputFormat(..),inputFormatFromString,chooseParser,printES,printNES,wrapWithTimeMeasurement)
import Equation.Type (ES)
import Equation.Ops (rule, epatRule, dhpRule, patternRule, leftLinear, secondOrderEq)
import qualified Equation.Rewriting as RW

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
                    DPRS
                    False
                    False
                    False
                    (chooseParser (inputFormat args)) of
    Left e -> do
      putStrLn "ERROR"
      putStr e
      exitFailure
    Right (n,ss,cs,ee,pd,axs,conjs) -> do
      conjectureJoinability (verbose args) axs conjs
      return (verbose args)
          
conjectureJoinability :: Bool -> ES -> ES -> IO ()
conjectureJoinability v dprs conjs = do
  if all (RW.joinable dprs) conjs
    then putStrLn "YES"
    else putStrLn "MAYBE"
  when v $ printES "input DPRS:" dprs
  when v . unless (null conjs) $ do
    putStrLn ""
    printNES "input conjectures:" conjs
    putStrLn ""
    putStrLn "checking joinability of conjectures:"
    putDoc $ RW.joinabilityDoc dprs conjs

opts :: ParserInfo Args
opts = info (argsParser <**> helper)
  ( fullDesc
  <> progDesc ("reads a file containing a DPRS+conjecture " ++
               "and checks whether the conjecture is joinable")
  <> header "hrstk - conjecture joinability tool" )

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
