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
import Confluence
import qualified TPTP
import qualified ARI

data InputFormat = ARI | TPTP

instance Show InputFormat where
  show ARI = "ari"
  show TPTP = "tptp"

data Mode = Info | Termination | Confluence | Unification | ConjectureJoinability

instance Show Mode where
  show Termination = "term"
  show Confluence = "conf"
  show Unification = "unif"
  show ConjectureJoinability = "conj"

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
                    (leftLinearRestriction (confMethod args))
                    (prsRestriction (confMethod args))
                    (chooseParser (inputFormat args)) of
    Left e -> do
      putStrLn "ERROR"
      putStr e
      exitFailure
    Right (n,ss,cs,ee,pd,axs,conjs) -> do
      case mode args of
        Info -> esInfo (verbose args) ee pd axs
        Termination -> termination (termMethod args) (smtSolver args) (verbose args) (debug args) ss cs axs
        Confluence -> confluence (confMethod args) n (smtSolver args) (verbose args)  (debug args) ss cs axs
        Unification -> unification n (verbose args) axs
        ConjectureJoinability -> conjectureJoinability (verbose args) axs conjs
  stop <- getCurrentTime
  when (verbose args) . fmtLn $ "\n\ntime: " +|fixedF 3  (diffUTCTime stop start)|+"s"

inputType :: Mode -> InputType
inputType Info = ES
inputType Termination = HRS
inputType Confluence = DPRS
inputType Unification = DHPUnifProblem 
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
    when v $ printES "input:" es

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

unification :: Int -> Bool -> ES -> IO ()
unification n v (e:es) = case evalState (runMaybeT $ Unif.unif (lhs e) (rhs e)) n of
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

opts :: ParserInfo Args
opts = info (argsParser <**> helper)
  ( fullDesc
  <> progDesc ("reads a file containing an HES/HRS " ++
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
     <> metavar "info | term | conf | unif | conj"
     <> help "what the tool should do; termination, confluence, unification or conjecture joinability" )
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
     <> metavar "ortho | dc | lc | kb"
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
modeFromString "info" = Right Info
modeFromString "term" = Right Termination
modeFromString "conf" = Right Confluence
modeFromString "unif" = Right Unification
modeFromString "conj" = Right ConjectureJoinability
modeFromString _ = Left "supported modes are 'info', 'term', 'conf', 'unif', and 'conj'"

termMethodFromString :: String -> Either String (Maybe TermMethod)
termMethodFromString "ncpo" = Right (Just NCPO)
termMethodFromString "poly" = Right (Just Poly)
termMethodFromString _ = Left "supported termination methods are 'ncpo' and 'poly'"

confMethodFromString :: String -> Either String (Maybe ConfMethod)
confMethodFromString "ortho" = Right (Just OR)
confMethodFromString "dc" = Right (Just DC)
confMethodFromString "lc" = Right (Just LC)
confMethodFromString "kb" = Right (Just KB)
confMethodFromString _ = Left "supported confluence methods are 'ortho', 'dc', 'lc' and 'kb'"

inputFormatFromString :: String -> Either String InputFormat
inputFormatFromString "ari" = Right ARI
inputFormatFromString "tptp" = Right TPTP
inputFormatFromString _ = Left "supported input formats are 'ari' and 'tptp'"

smtSolverFromString :: String -> Either String SMTSolver
smtSolverFromString "z3" = Right z3
smtSolverFromString "cvc5" = Right cvc5
smtSolverFromString "yices" = Right yices
smtSolverFromString _ = Left "supported SMT solvers are 'z3', 'cvc5' and 'yices'"
