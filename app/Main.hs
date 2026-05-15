{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}

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
import Utils.Pretty (prettyNList,docToString)
import Utils.SMT (SMTSolver,z3,cvc5,yices)
import Utils.InputProcessing (InputType(..),processInput)
import Typ.Type (Sort)
import Term.Type (FunTypMap)
import Equation.Type (Equation(..),ES)
import Equation.Ops (rule, dhpRule, patternRule, leftLinear, secondOrderEq)
import qualified Subst.Unif as Unif
import qualified Equation.Rewriting as RW
import qualified Equation.CriticalPairs as CP
import Termination
import qualified Termination.Poly.Solver as Poly
import qualified Termination.NCPO.Solver as NCPO
import qualified TPTP
import qualified ARI

data InputFormat = ARI | TPTP

instance Show InputFormat where
  show ARI = "ari"
  show TPTP = "tptp"

data Mode = Info | Termination | Confluence | Unification | CPJoinability | ConjectureJoinability

instance Show Mode where
  show Termination = "term"
  show Confluence = "conf"
  show Unification = "unif"
  show CPJoinability = "cps"
  show ConjectureJoinability = "conj"

data ConfMethod = OR | CP | DC

instance Show ConfMethod where
  show OR = "orthogonality"
  show CP = "terminating + joinable CPs"
  show DC = "development closedness"

data Args = Args
  { inputFile :: String
  , mode :: Mode
  , termMethod :: Maybe TermMethod
  , confMethod :: Maybe ConfMethod
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
    Right (n,ss,cs,ee,pd,axs,conjs) -> do
      case mode args of
        Info -> esInfo (verbose args) ee pd axs
        Termination -> termination (termMethod args) (smtSolver args) (verbose args) (debug args) ss cs axs
        Confluence -> undefined
        Unification -> unification n (verbose args) axs
        CPJoinability -> criticalPairsJoinability n (verbose args) axs
        ConjectureJoinability -> conjectureJoinability (verbose args) axs conjs
  stop <- getCurrentTime
  when (verbose args) . fmtLn $ "time: " +|fixedF 3  (diffUTCTime stop start)|+"s"

inputType :: Mode -> InputType
inputType Info = ES
inputType Termination = HRS
inputType Confluence = DPRS
inputType Unification = DHPUnifProblem 
inputType CPJoinability = DPRS
inputType ConjectureJoinability = HRS

secondOrderRestriction :: Maybe TermMethod -> Bool
secondOrderRestriction (Just Poly) = True
secondOrderRestriction _ = False

prsRestriction :: Maybe ConfMethod -> Bool
prsRestriction (Just DC) = True
prsRestriction _ = False

leftLinearRestriction :: Maybe ConfMethod -> Bool
leftLinearRestriction (Just OR) = True
leftLinearRestriction (Just DC) = True
leftLinearRestriction _ = False

-- |Checks input type of ES
esTyp :: ES -> InputType
esTyp es 
  | not (all rule es)        = ES
  | not (all dhpRule es)     = HRS
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
    when v $ printES "\ninput:" es
    when v $ putStrLn ""

termination :: Maybe TermMethod -> SMTSolver -> Bool -> Bool -> [Sort] -> FunTypMap -> ES ->  IO ()
termination (Just tm) s v d bts fTyM hrs = do
  res  <- checkTermination tm s d bts fTyM hrs
  if terminationStatus res
    then putStrLn "YES"
    else putStrLn "MAYBE"
  when v . putDoc $ terminationResultDoc res hrs
termination Nothing s v d bts fTyM hrs = do
  resNCPO <- checkTermination NCPO s d bts fTyM hrs
  if terminationStatus resNCPO
    then do
      putStrLn "YES"
      when v . putDoc $ terminationResultDoc resNCPO hrs
    else do
      if all secondOrderEq hrs
        then do
          resPoly <- checkTermination Poly s d bts fTyM hrs
          if terminationStatus resPoly
            then do
              putStrLn "YES"
              when v . putDoc $ terminationResultDoc resPoly hrs
            else putStrLn "MAYBE"
        else putStrLn "MAYBE"

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
     <> value Info
     <> metavar "info | term | conf | unif | cps | conj"
     <> help "what the tool should do; termination, confluence, unification, critical pair analysis, or conjecture joinability" )
  <*> option (eitherReader $ termMethodFromString . map toLower)
      ( long "term-method"
     <> short 't'
     <> showDefault
     <> value Nothing
     <> metavar "ncpo | poly"
     <> help "specific termination method" )
  <*> option (eitherReader $ confMethodFromString . map toLower)
      ( long "conf-method"
     <> short 'c'
     <> showDefault
     <> value Nothing
     <> metavar "ortho | cp | dc"
     <> help "specific confluence method" )
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
modeFromString "conf" = Right Confluence
modeFromString "unif" = Right Unification
modeFromString "cps" = Right CPJoinability
modeFromString "conj" = Right ConjectureJoinability
modeFromString _ = Left "supported modes are 'term', 'conf', 'unif', 'cps' and 'conj'"

termMethodFromString :: String -> Either String (Maybe TermMethod)
termMethodFromString "ncpo" = Right (Just NCPO)
termMethodFromString "poly" = Right (Just Poly)
termMethodFromString _ = Left "supported termination methods are 'ncpo' and 'poly'"

confMethodFromString :: String -> Either String (Maybe ConfMethod)
confMethodFromString "ortho" = Right (Just OR)
confMethodFromString "cp" = Right (Just CP)
confMethodFromString "dc" = Right (Just DC)
confMethodFromString _ = Left "supported confluence methods are 'ortho', 'cp' and 'dc'"

inputFormatFromString :: String -> Either String InputFormat
inputFormatFromString "ari" = Right ARI
inputFormatFromString "tptp" = Right TPTP
inputFormatFromString _ = Left "supported input formats are 'ari' and 'tptp'"

smtSolverFromString :: String -> Either String SMTSolver
smtSolverFromString "z3" = Right z3
smtSolverFromString "cvc5" = Right cvc5
smtSolverFromString "yices" = Right yices
smtSolverFromString _ = Left "supported SMT solvers are 'z3', 'cvc5' and 'yices'"
