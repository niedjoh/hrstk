{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}

-- |Solver for polynomial interpretations. Limited to second-order terms.
module Termination.Poly.Solver (PolyIntRes(status),checkTermination,resultDoc) where

import Control.Monad (foldM,zipWithM)
import Control.Monad.Extra (concatMapM)
import Control.Monad.State (MonadState,runState)
import Data.Default (def)
import Data.List (groupBy,permutations)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import qualified Data.MultiSet as MS
import Data.Vector (Vector)
import qualified Data.Vector as V
import GHC.Num.Integer (integerFromInt,integerToInt)
import qualified Language.Hasmtlib as SMT
import Prettyprinter (line,vsep,pretty,(<+>),Doc,line)

import Utils.SMT (Constraint,IntExpr,SMTSolver(..),VarVec,Vec(..))
import Utils.Type (Id(..))
import Term.Type (FunTypMap)
import Equation.Type (Equation(..),ES)
import Termination.Poly.Type
    ( apvArgs
    , apvVar
    , normApplPVarFPoly
    , ApplPVar(..)
    , ApplPVarP
    , FPoly(..)
    , FPolynomial
    , Monomial
    , Par(Par)
    , Parameter
    , Poly(..)
    , Polynomial )
import Termination.Poly.Interpretation (constIntMapWithStricts, interpret)

-- |result of termination proof attempt by polynomial interpretations
data PolyIntRes = PolyIntRes
  { status :: Bool
  , mSolVec :: Maybe (Vec Integer)
  , cIntMap :: Map Id FPolynomial
  , constrs :: [(FPolynomial,FPolynomial)]
  }

-- |Check termination of an HRS using polynomial interpretations.
checkTermination ::SMTSolver -> Bool -> FunTypMap -> ES -> IO PolyIntRes
checkTermination (Solver _ s _) debug constTyM es = do
  let (cIMapWStricts,n) = runState (constIntMapWithStricts constTyM) 0
      cIMap = M.map fst cIMapWStricts
      stricts = concatMap snd $ M.elems cIMapWStricts
      fpps = map (\e -> (interpret cIMap (lhs e), interpret cIMap (rhs e))) es
  (res,mSol) <- SMT.solveWith (if debug then SMT.solver (SMT.debugging def s) else SMT.solver s) $ do
    SMT.setLogic "QF_NIA"
    as <- V.replicateM n $ SMT.var @SMT.IntSort
    mapM_ (\(a,i) -> SMT.assert $ a SMT.>=? (if i `elem` stricts then 1 else 0)) (zip (V.toList as) [0..])
    constraints <- concatMapM (uncurry $ genConstraints True as) fpps
    mapM_ SMT.assert constraints
    return (Vec as)
  let boolRes = case res of
        SMT.Sat -> True
        SMT.Unsat -> False
        SMT.Unknown -> False
  return $ PolyIntRes { status = boolRes, mSolVec = mSol, cIntMap = cIMap, constrs = fpps }

-- |Print the result of a solution attempt to a termination check using polynomial interpretations.
resultDoc :: PolyIntRes -> ES -> Doc ann
resultDoc res es = let
   prettyConstr (p,q) e = line <> pretty e <> line <> line <> " " <+> pretty p <> line <> ">" <+> pretty q
   cIntD = line <> line <> "constant interpretations:" <> line <> line <>
     vsep (map (\(idt,fp) -> "⟦" <> pretty idt <> "⟧" <+> "=" <+> pretty fp) (M.assocs (cIntMap res)))
   constrD = line <> line <> "constraints:" <> line <> vsep (zipWith prettyConstr (constrs res) es)
   inputHRS = line <> "input HRS:" <> line <> line <> vsep (map pretty es)
 in case mSolVec res of
  Just (Vec sol) -> do
    let solInt = V.map integerToInt sol
        mConstrsSolved = mapM solvedForm (constrs res)
        solvedForm (p,q) = do
          pSolved <- parFPolyToIntFPoly solInt p
          qSolved <- parFPolyToIntFPoly solInt q
          return (normApplPVarFPoly pSolved, normApplPVarFPoly qSolved)
    case mConstrsSolved of
      Just constrsSolved -> inputHRS <> cIntD <> constrD <>
        line <> line <> "solution:" <> line <> line <>
        vsep (zipWith (\k i -> "a" <> pretty i <+> "⟼" <+> pretty k) (V.toList solInt) [(0 :: Int) .. ]) <>
        line <> line <> "solved constraints:" <> line <>
        vsep (zipWith prettyConstr constrsSolved es) <> line <> line
      Nothing -> "ERROR (something went wrong while constructing the solution)"
  Nothing -> inputHRS <> cIntD <> constrD <> line <> line

-- |Calculate the value of a parameter according to a solution vector for parameter variables.
-- TODO return the solution directly and move this into Codec
parToInt :: Vector Int -> Parameter -> Maybe Int
parToInt v (Poly m) = sumM [ productM (Just a : [ v V.!? i | (Par i) <- MS.elems ms])
                           | (ms,a) <- M.assocs m ] where
  sumM = foldM (combineM (+)) 0
  productM = foldM (combineM (*)) 1
  combineM op x y = (`op` x) <$> y 

-- |Transform a parameterized polynomial into a concrete one according to a solution vector.
parPolyToIntPoly :: Vector Int -> Poly (ApplPVar Parameter) Parameter -> Maybe (Poly (ApplPVar Int) Int)
parPolyToIntPoly v (Poly m) = Poly . M.fromList <$> mapM f (M.assocs m) where
  f (k,a) = do
    k' <- MS.fromList <$> mapM g (MS.toList k)
    a' <- parToInt v a
    return (k',a')
  g (ApplPVar var fps) = ApplPVar var <$> mapM (parFPolyToIntFPoly v) fps

-- |Transform functional polynomial into concrete functional polynomial according to solution vector.
parFPolyToIntFPoly :: Vector Int -> FPoly (ApplPVar Parameter) Parameter -> Maybe (FPoly (ApplPVar Int) Int)
parFPolyToIntFPoly v (PLam fp) = PLam <$> parFPolyToIntFPoly v fp
parFPolyToIntFPoly v (PBase p) = PBase <$> parPolyToIntPoly v p

-- |Adds the constant 0 to a given polynomial if it does not contain a constant part.
add0ConstantIfNotPresent :: Polynomial -> Polynomial
add0ConstantIfNotPresent p@(Poly m) = case m M.!? MS.empty of
    Just _ -> p
    Nothing -> Poly $ M.insert MS.empty 0 m

-- |Generate constraints for a strict/weak comparison between two functional polynomials.
-- since polynomials are normalized, we need to ensure that the second polynomial contains a constant part.
genConstraints :: Monad m => MonadState s m =>
  SMT.MonadSMT s m => Bool -> VarVec -> FPolynomial -> FPolynomial -> m [Constraint]
genConstraints strict v lfp rfp = concatMapM (comp strict True v lp rp) comps where
  lp = toPoly lfp
  rp = add0ConstantIfNotPresent. toPoly $ rfp
  comps = comparisons lp rp

-- |Convert a functional polynomial to a polynomial by dropping lambdas.
toPoly :: FPolynomial -> Polynomial
toPoly (PLam fp) = toPoly fp
toPoly (PBase p) = p

-- |Given two polynomials, a list of pairs of lists of monomials with the same variables is returned.
-- These pairs of lists need to be compared wrt. coefficent and arguments.
comparisons :: Polynomial -> Polynomial -> [([Monomial ApplPVarP], [Monomial ApplPVarP])]
comparisons (Poly lMap) (Poly rMap) = [(M.findWithDefault [] key lGroups, rGroups M.! key) | key <- rKeys] where
  lGroups = groupByVars lMap
  rGroups = groupByVars rMap
  rKeys = M.keys rGroups
  groupByVars m = foldr (uncurry $ M.insertWith (++)) M.empty [ (MS.map apvVar ms, [ms]) | ms <- M.keys m ]

-- |Comparison of two lists of Monomials which all have the same multiset of variables.
-- (The arguments of higher-order variables might differ.)
comp :: MonadState s m => SMT.MonadSMT s m =>
  Bool -> Bool -> VarVec -> Polynomial -> Polynomial -> ([Monomial ApplPVarP], [Monomial ApplPVarP]) ->
  m [Constraint]
comp _ _ v _ (Poly rMap) ([],rmss) = pure $ map (\rms -> 0 SMT.=== toSMTExpr v (rMap M.! rms) ) rmss
comp strict coeff v (Poly lMap) (Poly rMap) ([lms], [rms]) = do
  let compFun = if MS.null rms && strict then (SMT.>?) else (SMT.>=?)
      coeffConstraint = toSMTExpr v (lMap M.! lms) `compFun` toSMTExpr v (rMap M.! rms)
      varEq apv1 apv2 = apvVar apv1 == apvVar apv2
      removeFOVars = MS.filter (not . null . apvArgs)
      groups = groupBy varEq . MS.toAscList . removeFOVars
      recCase (ApplPVar _ lfps) (ApplPVar _ rfps) =
        SMT.and . concat <$> zipWithM (genConstraints False v) lfps rfps
  recConstraints <- sequence [ SMT.or <$> zipWithM recCase lg rg'
                             | (lg,rg) <- zip (groups lms) (groups rms), rg' <- permutations rg]
  return $ if coeff then coeffConstraint : recConstraints else recConstraints
comp _ _ v (Poly lMap) (Poly rMap) (lmss, rmss) = do
  let n = length lmss
  let m = length rmss
  es <- V.replicateM (n * m) $ SMT.var @SMT.IntSort
  let getFreshVar i j = es V.! (i * m + j)
      choice lms rms i j = do
        let coeffC = getFreshVar i j SMT.>=? toSMTExpr v (rMap M.! rms)
        -- we already checked the coefficient
        recConstraints <- comp False False v (Poly lMap) (Poly rMap) ([lms],[rms])
        return $ SMT.or [SMT.and (coeffC : recConstraints), 0 SMT.=== toSMTExpr v (rMap M.! rms)]
      newVarsPositive = map (SMT.>=? 0) (V.toList es)
      coeffPartitionCs = [ toSMTExpr v (lMap M.! lms) SMT.>=? sum [ getFreshVar i j
                                                                  | (_,j) <- zip rmss [0..] ]
                         | (lms,i) <- zip lmss [0..]]
  constraints <- sequence [ SMT.or <$> sequence [ choice lms rms i j
                                                | (lms,i) <- zip lmss [0..] ]
                          | (rms,j) <- zip rmss [0..] ]
  return $ newVarsPositive ++ coeffPartitionCs ++ constraints

-- |Converts a parameter into an SMT expression.
toSMTExpr :: VarVec -> Parameter -> IntExpr
toSMTExpr v (Poly m)
  | M.null m  = 0
  | otherwise = sum (map f (M.assocs m)) where
      f (_,0) = 0
      f (ms,1) = rest ms
      f (ms,c)
        | MS.null ms = fromInteger (integerFromInt c)
        | otherwise  = fromInteger (integerFromInt c) * rest ms
      rest ms
        | MS.null ms = 1
        | otherwise  = product (map (\(Par i) -> v V.! i) (MS.toList ms))
