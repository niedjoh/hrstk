{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Monad (unless,when)
import Control.Monad.State (evalState)
import Control.Monad.Trans.Maybe (runMaybeT)
import Data.Char (toLower)
import qualified Data.Text.IO as TIO
import Data.Time (getCurrentTime,diffUTCTime)
import Fmt ((+|),(|+),fixedF,fmtLn)
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
import Prettyprinter (pretty,vsep)
import Prettyprinter.Render.Text (putDoc)
import System.Exit (exitSuccess,exitFailure)

import Utils.Parse (ProblemParser,parseProblem,scARI,scTPTP)
import Utils.Pretty (prettyNList)
import Utils.SMT (SMTSolver,z3,cvc5,yices)
import Utils.InputProcessing (InputType(..),processInput)
import Typ.Type (Sort)
import Term.Type (FunTypMap)
import Equation.Type (Equation(..),ES)
import qualified Subst.Unif as Unif
import qualified Equation.Rewriting as RW
import qualified Equation.CriticalPairs as CP
import qualified Termination.Poly.Solver as Poly
import qualified Termination.NCPO.Solver as NCPO
import qualified TPTP
import qualified ARI

data InputFormat = ARI | TPTP

instance Show InputFormat where
  show ARI = "ari"
  show TPTP = "tptp"

data Mode = Termination | Unification | CPJoinability | ConjectureJoinability

instance Show Mode where
  show Termination = "term"
  show Unification = "unif"
  show CPJoinability = "cps"
  show ConjectureJoinability = "conj"

data TermMethod = NCPO | Poly

instance Show TermMethod where
  show NCPO = "ncpo"
  show Poly = "poly"

data Args = Args
  { inputFile :: String
  , mode :: Mode
  , termMethod :: TermMethod
  , inputFormat :: InputFormat
  , smtSolver :: SMTSolver
  , verbose :: Bool
  , debug :: Bool
  }

main :: IO ()
main = do
  start <- getCurrentTime
  args <- execParser opts
  input <- TIO.readFile (inputFile args)
  case processInput (inputFile args)
                    input
                    (inputType (mode args))
                    (secondOrderRestriction (termMethod args))
                    (chooseParser (inputFormat args)) of
    Left e -> do
      putStrLn "ERROR"
      putStr e
      exitFailure
    Right (n,ss,cs,axs,conjs) -> do
      case mode args of
        Termination -> termination (termMethod args) (smtSolver args) (verbose args) (debug args) ss cs axs
        Unification -> unification n (verbose args) axs
        CPJoinability -> criticalPairsJoinability n (verbose args) axs
        ConjectureJoinability -> conjectureJoinability (verbose args) axs conjs
  stop <- getCurrentTime
  fmtLn $ "time: " +|fixedF 3  (diffUTCTime stop start)|+"s"

inputType :: Mode -> InputType
inputType Termination = HRS
inputType Unification = DHPUnifProblem 
inputType CPJoinability = DPRS
inputType ConjectureJoinability = HRS

secondOrderRestriction :: TermMethod -> Bool
secondOrderRestriction Poly = True
secondOrderRestriction NCPO = False

termination :: TermMethod -> SMTSolver -> Bool -> Bool -> [Sort] -> FunTypMap -> ES ->  IO ()
termination Poly s v d _ cTyM hrs = do
  res <- Poly.checkTermination s d cTyM hrs
  if Poly.status res
    then putStrLn "YES"
    else putStrLn "MAYBE"
  when v . putDoc $ Poly.resultDoc res hrs
termination NCPO s v d bts cTyM hrs = do
  res <- NCPO.checkTermination s d bts cTyM hrs
  if NCPO.status res
    then putStrLn "YES"
    else putStrLn "MAYBE"
  when v . putDoc $ NCPO.resultDoc res hrs

criticalPairsJoinability :: Int -> Bool -> ES -> IO ()
criticalPairsJoinability n v dprs = case evalState (runMaybeT $ CP.criticalPairs dprs dprs) n of
  Nothing -> do
    putStrLn "MAYBE"
    when v . printES "input DPRS:" $ dprs
    when v . putStrLn $ "\npossibly infinite behavior underlying unification\n"
  Just cpairs -> do
    if CP.checkJoinability dprs cpairs
      then putStrLn "YES"
      else putStrLn "MAYBE"
    when v . putDoc $ CP.resultDoc dprs cpairs

conjectureJoinability :: Bool -> ES -> ES -> IO ()
conjectureJoinability v dprs conjs = do
  if all (RW.joinable dprs) conjs
    then putStrLn "YES"
    else putStrLn "MAYBE"
  when v $ putStrLn "" >> printES "input DPRS:" dprs
  when v . unless (null conjs) $ do
    putStrLn "" >> printNES "input conjectures:" conjs
    putStrLn "checking joinability of conjectures:"
    putDoc $ RW.joinabilityDoc dprs conjs

unification :: Int -> Bool -> ES -> IO ()
unification n v (e:es) = case evalState (runMaybeT $ Unif.unif (lhs e) (rhs e)) n of
  Nothing -> do
    putStrLn "MAYBE\n"
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

chooseParser :: InputFormat -> ProblemParser
chooseParser ARI = parseProblem scARI (ARI.parser)
chooseParser TPTP = parseProblem scTPTP (TPTP.parser)

printES :: String -> ES -> IO ()
printES s es = do
  putStrLn s
  if null es
    then putStrLn "none"
    else do
      putStrLn ""
      putDoc . vsep $ map pretty es
      putStrLn ""

printNES :: String -> ES -> IO ()
printNES s es = do
  putStrLn s
  if null es
    then putStrLn "none"
    else do
      putStrLn ""
      putDoc . prettyNList . map pretty $ es
      putStrLn ""

opts :: ParserInfo Args
opts = info (argsParser <**> helper)
  ( fullDesc
  <> progDesc ("reads a file containing an (equational) HRS a la Nipkow " ++
               "and performs analysis according to one of the modes")
  <> header "hrstk - higher-order rewriting toolkit" )

argsParser :: Parser Args
argsParser = Args
  <$> argument str
      ( metavar "FILE"
     <> help "input file" )
  <*> option (eitherReader $ modeFromString. map toLower)
      ( long "mode"
     <> short 'm'
     <> showDefault
     <> value ConjectureJoinability
     <> metavar "term | unif | cps | conj"
     <> help "what the tool should do; termination, unification, critical pair analysis, or conjecture joinability" )
  <*> option (eitherReader $ termMethodFromString . map toLower)
      ( long "term-method"
     <> short 't'
     <> showDefault
     <> value NCPO
     <> metavar "ncpo | poly"
     <> help "employed termination method" )
  <*> option (eitherReader $ inputFormatFromString . map toLower)
      ( long "input-format"
     <> short 'i'
     <> showDefault
     <> value ARI
     <> metavar "ari | tptp"
     <> help "input format" )
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

modeFromString :: String -> Either String Mode
modeFromString "term" = Right Termination
modeFromString "unif" = Right Unification
modeFromString "cps" = Right CPJoinability
modeFromString "conj" = Right ConjectureJoinability
modeFromString _ = Left "supported modes are 'term', 'unif', 'cps', 'conf' and 'conj'"

termMethodFromString :: String -> Either String TermMethod
termMethodFromString "ncpo" = Right NCPO
termMethodFromString "poly" = Right Poly
termMethodFromString _ = Left "supported termination methods are 'ncpo' and 'poly'"

inputFormatFromString :: String -> Either String InputFormat
inputFormatFromString "ari" = Right ARI
inputFormatFromString "tptp" = Right TPTP
inputFormatFromString _ = Left "supported input formats are 'ari' and 'tptp'"

smtSolverFromString :: String -> Either String SMTSolver
smtSolverFromString "z3" = Right z3
smtSolverFromString "cvc5" = Right cvc5
smtSolverFromString "yices" = Right yices
smtSolverFromString _ = Left "supported SMT solvers are 'z3', 'cvc5' and 'yices'"
