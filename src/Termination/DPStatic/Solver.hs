{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Termination.DPStatic.Solver where

import qualified Language.Hasmtlib as SMT
import qualified Data.Map.Strict as M
import qualified Data.Set as Set
import Utils.Type
import Typ.Ops
import Term.Ops
import Typ.Type
import Term.Type
import Utils.SMT (SMTSolver(Solver),z3,cvc5,yices, Constraint, IntExpr, smtVarMap)
import Equation.Type
import qualified Data.Set as Set
import qualified Data.Map as Map
import Utils.FreshMonad (MonadFresh, freshVar)
import Control.Monad (forM)
import Control.Monad.State (evalState)
import Data.Graph (SCC(..), stronglyConnComp)
import Data.List.NonEmpty (toList)
import Data.Bool (Bool)

data Candidate = Candidate {term :: Term, condition :: [(Head,Int)]} deriving (Ord, Eq, Show)
data SDP = SDP {rule :: Equation, sdpCondition :: [(Head,Int)]} deriving (Eq, Show)

data MFlag = Minimal | Arbitrary | Computable ES deriving (Show, Eq)
data FFlag = Formative | All deriving (Show, Eq)

data DPProblem = DPProblem {dprules :: [SDP], rules :: ES, mflag :: MFlag, fflag :: FFlag} deriving (Show, Eq)

data ProcResult
  = No
  | Problems [DPProblem]

definedSymbols :: ES -> Set.Set Head
definedSymbols es  = Set.fromList $ map (\eq -> hd $ lhs eq) es

buildMinarMap :: ES -> Map.Map Head Int
buildMinarMap es = Map.fromList 
    [ (hd leftSide, length (sp leftSide)) | eq <- es, let leftSide = lhs eq ]

stripArgs :: Int -> Typ -> Typ
stripArgs n (Typ as b) = Typ (drop n as) b

candidates :: Term -> [(Head,Int)] -> Map.Map Head Int -> Set.Set Head -> [Candidate]
candidates term@(Term{nlams = n}) args minarMap definedSymbols
 | n > 0 = candidates (term{nlams = 0, typ = stripArgs n (typ term)}) args minarMap definedSymbols
 | (hd term) `Set.member` definedSymbols = 
      let 
          k = Map.findWithDefault 0 (hd term) minarMap 
          truncatedSpine = take k (sp term)
          truncatedTerm = term{sp = truncatedSpine}
      in (Candidate truncatedTerm args) : concatMap (\x -> candidates x args minarMap definedSymbols) (sp term)
 | sp term == [] = []
 | isFV (hd term) = concat [candidates t ((hd term,i):args) minarMap definedSymbols |  (i,t) <- zip [1..] (sp term)]
 | otherwise = concatMap (\x -> candidates x args minarMap definedSymbols) (sp term)


metafyGo :: MonadFresh m => Int -> M.Map Int Var -> Term -> m (Term, M.Map Int Var)
metafyGo n seen term@(Term { nlams = i, hd = DB m, sp = spine })
  | m >= n + i = do
      let key = m - (n + i)
      case M.lookup key seen of
        Just v -> do
          (spine', seen') <- goSpine (n + i) seen spine
          pure (term { hd = FV v, sp = spine' }, seen')
        Nothing -> do
          v <- freshVar
          let seen1 = M.insert key v seen
          (spine', seen') <- goSpine (n + i) seen1 spine
          pure (term { hd = FV v, sp = spine' }, seen')
  | otherwise = do
      (spine', seen') <- goSpine (n + i) seen spine
      pure (term { sp = spine' }, seen')
metafyGo n seen term@(Term { nlams = i, sp = spine }) = do
  (spine', seen') <- goSpine (n + i) seen spine
  pure (term { sp = spine' }, seen')

goSpine:: MonadFresh m => Int -> M.Map Int Var -> [Term] -> m ([Term], M.Map Int Var)
goSpine _ seen [] = pure ([], seen)
goSpine n seen (t : ts) = do
  (t', seen')   <- metafyGo n seen t
  (ts', seen'') <- goSpine n seen' ts
  pure (t' : ts', seen'')

metafy :: MonadFresh m => Term -> m Term
metafy term = fst <$> metafyGo 0 M.empty term

addSharp :: Head -> Head
addSharp (F (Id t)) = F (Id (t <> "#"))

staticDependencyPairs :: MonadFresh m => ES -> m [SDP]
staticDependencyPairs es = fmap concat $ forM [ e | e@Equation{isRule = b} <- es, b] $ \Equation{lhs = l, rhs = r} -> do
  let cs = candidates r [] minarMap definedS
  forM cs $ \Candidate{term = p, condition = c} -> do
    let lSharp = l { hd = addSharp (hd l) }
    let pSharp = p { hd = addSharp (hd p) }
    rhs' <- metafy pSharp
    pure SDP {rule = Equation { lhs = lSharp, rhs = rhs', isRule = True }, sdpCondition =  c}
 where minarMap = buildMinarMap es
       definedS = definedSymbols es

runStaticDependencyPairs :: ES -> [SDP]
runStaticDependencyPairs es = evalState (staticDependencyPairs es) 0

buildEdges :: [SDP] -> [(SDP, Int, [Int])]
buildEdges sdps = [ (s, i, targets s) | (s, i) <- zip sdps [0..] ]
  where
    targets s1 = [ j | (s2, j) <- zip sdps [0..], hasEdge s1 s2 ]
    hasEdge s1 s2 = hd (rhs (rule s1)) == hd (lhs (rule s2))

sccs :: [SDP] -> [SCC SDP]
sccs sdps = stronglyConnComp (buildEdges sdps)


nonTrivialSCCs :: [SDP] -> [[SDP]]
nonTrivialSCCs sdps =
  [ ns | scc <- sccs, Just ns <- [nonTrivial scc] ]
 where
  edges = buildEdges sdps
  sccs  = stronglyConnComp edges
  nonTrivial (NECyclicSCC ns) = Just (toList ns)
  nonTrivial (AcyclicSCC _)   = Nothing


dependencyGraphProcessor :: DPProblem -> ProcResult
dependencyGraphProcessor prob@(DPProblem{dprules = dp}) = Problems [ prob{dprules = cycle}| cycle <- nonTrivialSCCs dp]

runProcessors :: ES -> IO Bool
runProcessors es = do
  let sdp = runStaticDependencyPairs es
  let dpProblem =  DPProblem{dprules = sdp, rules = es, mflag = (Computable es), fflag = Formative}
  let Problems cycles = dependencyGraphProcessor dpProblem
  if null cycles
    then return True
    else return False