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
import Utils.FreshMonad (MonadFresh, freshVar)
import Control.Monad (forM, forM_)
import Control.Monad.State (evalState)
import Data.Graph (SCC(..), stronglyConnComp)
import Data.List.NonEmpty (toList)
import Termination.AFP.Solver
import qualified Termination.StarCPO.Type as CPO
import Termination.StarCPO.Ordering
import Termination.StarCPO.Solver
import qualified Termination.NCPO.Type as NCPOType
import qualified Termination.NCPO.Ordering as NCPOOrdering
import qualified Termination.NCPO.Solver as NCPOSolver



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

allHeadSymbols :: ES -> Set.Set Head
allHeadSymbols es = Set.fromList $ concatMap (\Equation{lhs = l, rhs = r} -> [hd $ l, hd $ r]) es

buildMinarMap :: ES -> M.Map Head Int
buildMinarMap es = M.fromList 
    [ (hd leftSide, length (sp leftSide)) | eq <- es, let leftSide = lhs eq ]

buildMinarMapAll :: ES -> M.Map Head Int
buildMinarMapAll es = M.fromList 
    [ (hd side, length (sp side)) | let sides = concatMap (\Equation{lhs = l, rhs = r} -> [l,r]) es, side <- sides]

stripArgs :: Int -> Typ -> Typ
stripArgs n (Typ as b) = Typ (drop n as) b

candidates :: Term -> [(Head,Int)] -> M.Map Head Int -> Set.Set Head -> [Candidate]
candidates term@(Term{nlams = n}) args minarMap definedSymbols
 | n > 0 = candidates (term{nlams = 0, typ = stripArgs n (typ term)}) args minarMap definedSymbols
 | (hd term) `Set.member` definedSymbols = 
      let 
          k = M.findWithDefault 0 (hd term) minarMap 
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

runProcessors :: ES -> SMTSolver -> [Sort] -> FunTypMap -> IO Bool
runProcessors es s allSorts fTyM = do
  mPrec <- findSortOrdering s allSorts es
  case mPrec of
    Nothing   -> return False
    Just prec -> do
      let sdp = runStaticDependencyPairs es
      let dpProblem =  DPProblem{dprules = sdp, rules = es, mflag = (Computable es), fflag = Formative}
      let Problems cycles = dependencyGraphProcessor dpProblem
      if null cycles
        then return True
        else processorLoop cycles s allSorts prec fTyM

processorLoop :: [DPProblem] -> SMTSolver -> [Sort] -> M.Map Id Integer -> FunTypMap -> IO Bool
processorLoop dpps s allSorts prec fTyM = do
  computed <- forM dpps $ \dpp -> computableSubtermProcessor s dpp allSorts prec
  computed2 <- forM computed $ \dpp -> reductionTripleNCPOProcessor dpp s allSorts fTyM (length $ dprules dpp)
  let resplit = [ p { dprules = c } | p <- computed, c <- nonTrivialSCCs (dprules p) ]
      size ps = sum (map (length . dprules) ps)
  if null resplit then return True
  else if size resplit >= size dpps then return False
  else processorLoop resplit s allSorts prec fTyM


computableSubtermProcessor :: SMTSolver -> DPProblem -> [Sort] -> M.Map Id Integer -> IO DPProblem
computableSubtermProcessor s prob@(DPProblem{dprules = dp, rules = rs}) allSorts prec = do
  computedSDPs <- maximizeSolvedConstraints s rs (length dp) dp allSorts prec
  return prob{dprules = computedSDPs}

maximizeSolvedConstraints :: SMTSolver -> ES -> Int -> [SDP] -> [Sort] -> M.Map Id Integer -> IO [SDP]
maximizeSolvedConstraints _ _ 0 sdps _ _ = return sdps
maximizeSolvedConstraints solver@(Solver _ s _) rs k sdps allSorts prec = do
  (res, model) <- SMT.solveWith (SMT.solver s) $ do
    let dpRules = [r | SDP{rule = r} <- sdps]
    let headSymbols = Set.toList $ allHeadSymbols dpRules
    let minarMap = buildMinarMapAll dpRules
    sortPrecedence <- smtVarMap @SMT.IntSort allSorts
    forM_ (M.toList prec) $ \(so, v) ->
      SMT.assert (sortPrecedence M.! so SMT.=== fromInteger v)
    let env = AFPInfo { sPrec = sortPrecedence }
    mapM_ (SMT.assert . afpRule env) rs
    nuVars <- smtVarMap @SMT.BoolSort [ (f, i) | f <- headSymbols, i <- [0 .. (minarMap M.! f) - 1]]
    forM_ headSymbols $ \f -> SMT.assert (exactlyOne [ nuVars M.! (f, i) | i <- [0 .. (minarMap M.! f) - 1] ])
    flags <- forM sdps $ \SDP{rule = r} -> do
      b <- SMT.var @SMT.BoolSort
      SMT.assert (b SMT.==> projectionConstraint nuVars env (lhs r) (rhs r))
      SMT.assert (SMT.not b SMT.==> projectionConstraintEqual nuVars env (lhs r) (rhs r))
      return b

    SMT.assert (sum [ SMT.ite b (1 :: IntExpr) 0 | b <- flags ] SMT.>=? fromIntegral k)
    return flags

  case (res, model) of
    (SMT.Sat, Just bs) -> return [ dp | (dp, False) <- zip sdps bs ]
    _                  -> maximizeSolvedConstraints solver rs (k - 1) sdps allSorts prec


projectionConstraint :: M.Map (Head, Int) BoolExpr -> AFPInfo -> Term -> Term -> Constraint
projectionConstraint pMap env s t = SMT.and [((pMap M.! (hd s,i)) SMT.&& (pMap M.! (hd t, j))) SMT.==> computableSubtermConstraint env (sp s !! i) (sp t !! j) | 
  i <- [0 .. (length $ sp s) - 1], j <- [0 .. (length $ sp t) - 1]]

projectionConstraintEqual :: M.Map (Head, Int) BoolExpr -> AFPInfo -> Term -> Term -> Constraint
projectionConstraintEqual pMap env s t = SMT.and [((pMap M.! (hd s,i)) SMT.&& (pMap M.! (hd t, j))) SMT.==> SMT.bool (sp s !! i == sp t !! j) | 
  i <- [0 .. (length $ sp s) - 1], j <- [0 .. (length $ sp t) - 1]]

computableSubtermConstraint :: AFPInfo -> Term -> Term -> Constraint
computableSubtermConstraint env s t
  | s == t    = SMT.false
  | not (sort (typ s) && sort (typ t)) = SMT.false
  | otherwise = accessibleArguments env s t SMT.|| matchesViaMetaVarSMT env s t


matchesViaMetaVarSMT :: AFPInfo -> Term -> Term -> Constraint
matchesViaMetaVarSMT env s t = case hd t of 
 FV z -> accessibleMetaVarOccurrence env s z
 _ -> SMT.false
 

accessibleMetaVarOccurrence :: AFPInfo -> Term -> Var -> Constraint
accessibleMetaVarOccurrence env term@(Term {nlams = n, hd = h, sp = s, typ = ty}) z
    | h == FV z = SMT.true   -- reached an occurrence of Z itself (whatever its own arguments happen to be)
    | n > 0     = accessibleMetaVarOccurrence env (term { nlams = n - 1, typ = getBodyType ty }) z
    | isFV h || isFun h =
        let hdTyp = getHeadType term
            subs  = accSMT env h hdTyp
            validSubs = [ (s !! (i-1), accCond)
                        | (i, accCond) <- subs
                        , case h of
                            FV v -> v `Set.notMember` freeVars (s !! (i-1))
                            _    -> True ]
            subConstraints = map (\(sub, cond) -> cond SMT.&& accessibleMetaVarOccurrence env sub z) validSubs
        in SMT.or subConstraints
    | otherwise = SMT.false


findSortOrdering :: SMTSolver -> [Sort] -> ES -> IO (Maybe (M.Map Id Integer))
findSortOrdering (Solver _ s _) allSorts rs = do
  (res, msol) <- SMT.solveWith (SMT.solver s) $ do
    sortPrecedence <- smtVarMap @SMT.IntSort allSorts
    let env = AFPInfo { sPrec = sortPrecedence }
    mapM_ (SMT.assert . afpRule env) rs
    return sortPrecedence
  return $ case res of
    SMT.Sat -> msol
    _       -> Nothing

exactlyOne :: [Constraint] -> Constraint
exactlyOne bs =
  SMT.or bs SMT.&&
  SMT.and [ SMT.not (a SMT.&& b)
          | (a, i) <- zip bs [0 :: Int ..]
          , (b, j) <- zip bs [0 ..]
          , i < j ]

type BoolExpr = SMT.Expr SMT.BoolSort

getAllIdsOfTerm :: Term -> [Id]
getAllIdsOfTerm (Term{hd = F i, sp = s}) = i : concatMap getAllIdsOfTerm s
getAllIdsOfTerm (Term{sp = s})           = concatMap getAllIdsOfTerm s

getIDs :: ES -> [Id]
getIDs es = Set.toList . Set.fromList $
  concatMap (\Equation{lhs = l, rhs = r} -> getAllIdsOfTerm l ++ getAllIdsOfTerm r) es

reductionTripleProcessor :: DPProblem -> SMTSolver -> [Sort] -> FunTypMap -> Int -> IO DPProblem
reductionTripleProcessor dpp _ _ _ 0 = return dpp
reductionTripleProcessor dpp@(DPProblem{dprules = dps}) solver@(Solver _ s _) allSorts fTyps k = do
  let fs = getIDs $ rules dpp ++ [ r | SDP{rule = r} <- dps ]
  let fTypsAll = markedTyps (rules dpp) fTyps
  (res, model) <- SMT.solveWith (SMT.solver s) $ do
    sortPrec   <- CPO.Prec  <$> smtVarMap @SMT.IntSort allSorts
    basic      <- CPO.Basic <$> smtVarMap @SMT.BoolSort allSorts
    st         <- CPO.Stat  <$> smtVarMap @SMT.BoolSort fs
    funPrec    <- CPO.Prec  <$> smtVarMap @SMT.IntSort fs
    accessible <- CPO.Acc   <$> smtVarMap @SMT.BoolSort
                    [ (f,i) | f <- fs, i <- [0 .. arity (fTypsAll M.! f) - 1] ]
    let cpoinfo = CPO.CPOInfo { CPO.sorts = allSorts, CPO.sPrec = sortPrec, CPO.stat = st
                          , CPO.fPrec = funPrec, CPO.isBasic = basic, CPO.isAccessible = accessible }
    mapM_ (SMT.assert . basicCond cpoinfo fs fTypsAll) allSorts
    mapM_ SMT.assert [ accessibleCond cpoinfo f i a b
                     | f <- fs, Typ as b <- [fTypsAll M.! f], (a,i) <- zip as [0..] ]
    forM_ [ r | r@Equation{isRule = True} <- rules dpp ] $ \r ->
      SMT.assert (scpoWeakWrapper cpoinfo (lhs r) (rhs r))
    flags <- forM dps $ \SDP{rule = r} -> do
      b <- SMT.var @SMT.BoolSort
      SMT.assert (scpoWeakWrapper cpoinfo (lhs r) (rhs r))
      SMT.assert (b SMT.==> scpoWrapper cpoinfo (lhs r) (rhs r))
      return b
    SMT.assert (sum [ SMT.ite b (1 :: IntExpr) 0 | b <- flags ] SMT.>=? fromIntegral k)
    return flags
  case (res, model) of
    (SMT.Sat, Just bs) -> return dpp { dprules = [ dp | (dp, False) <- zip dps bs ] }
    _                  -> reductionTripleProcessor dpp solver allSorts fTyps m
 where m = if k == 1 then 0 else (k-1)


markedTyps :: ES -> FunTypMap -> FunTypMap
markedTyps es fTyps = M.union fTyps $ M.fromList
  [ (Id (t <> "#"), ty)
  | F (Id t) <- Set.toList (definedSymbols es)
  , Just ty <- [M.lookup (Id t) fTyps] ]


reductionTripleNCPOProcessor :: DPProblem -> SMTSolver -> [Sort] -> FunTypMap -> Int -> IO DPProblem
reductionTripleNCPOProcessor dpp _ _ _ 0 = return dpp
reductionTripleNCPOProcessor dpp@(DPProblem{dprules = dps}) solver@(Solver _ s _) allSorts fTyps k = do
  let fs = getIDs $ rules dpp ++ [ r | SDP{rule = r} <- dps ]
  let fTypsAll = markedTyps (rules dpp) fTyps
  (res, model) <- SMT.solveWith (SMT.solver s) $ do
    sortPrec   <- NCPOType.Prec  <$> smtVarMap @SMT.IntSort allSorts
    basic      <- NCPOType.Basic <$> smtVarMap @SMT.BoolSort allSorts
    st         <- NCPOType.Stat  <$> smtVarMap @SMT.BoolSort fs
    funPrec    <- NCPOType.Prec  <$> smtVarMap @SMT.IntSort fs
    accessible <- NCPOType.Acc   <$> smtVarMap @SMT.BoolSort
                    [ (f,i) | f <- fs, i <- [0 .. arity (fTypsAll M.! f) - 1] ]
    let cpoinfo = NCPOType.CPOInfo { NCPOType.sorts = allSorts, NCPOType.sPrec = sortPrec, NCPOType.stat = st
                          , NCPOType.fPrec = funPrec, NCPOType.isBasic = basic, NCPOType.isAccessible = accessible }
    mapM_ (SMT.assert . NCPOSolver.basicCond cpoinfo fs fTypsAll) allSorts
    mapM_ SMT.assert [ NCPOSolver.accessibleCond cpoinfo f i a b
                     | f <- fs, Typ as b <- [fTypsAll M.! f], (a,i) <- zip as [0..] ]
    forM_ [ r | r@Equation{isRule = True} <- rules dpp ] $ \r ->
      SMT.assert $ evalState (NCPOOrdering.ncpoWeakWrapper cpoinfo (lhs r) (rhs r)) 0
    flags <- forM dps $ \SDP{rule = r} -> do
      b <- SMT.var @SMT.BoolSort
      let strictC = evalState (NCPOOrdering.ncpoWrapper cpoinfo (lhs r) (rhs r)) 0
      SMT.assert $ (b SMT.==> strictC)
      SMT.assert $ (SMT.not b SMT.==> SMT.bool (lhs r == rhs r))
      return b
    SMT.assert (sum [ SMT.ite b (1 :: IntExpr) 0 | b <- flags ] SMT.>=? fromIntegral k)
    return flags
  case (res, model) of
    (SMT.Sat, Just bs) -> return dpp { dprules = [ dp | (dp, False) <- zip dps bs ] }
    _                  -> reductionTripleNCPOProcessor dpp solver allSorts fTyps m

 where m = if k == 1 then 0 else 1