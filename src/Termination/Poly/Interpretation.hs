{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

-- |Interpretations for simply-typed lambda terms. the shape of constant interpretations is limited
-- to second-order terms.
module Termination.Poly.Interpretation (constIntMap, constIntMapWithStricts, constantInterpretation, interpret) where

import Control.Monad (replicateM,mapAndUnzipM)
import Data.List (nub, partition, foldl')
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import qualified Data.MultiSet as MS

import Utils.FreshMonad (FreshM, fresh)
import Utils.Type (Id(..))
import Typ.Type (Typ(..))
import Typ.Ops (arity)
import Term.Type (Term(..),Head(..))

import Termination.Poly.Type

-- |Computes the symbolic polynomial interpretation of a term given symbolic polynomial
-- interpretations for all constants occuring in the term.
interpret :: Map Id FPolynomial -> Term -> FPolynomial
interpret m s = iterate PLam (foldl pBeta fp (map (interpret m) (sp s))) !! nlams s where
  k = length $ sp s
  fp = case hd s of
    F f -> M.findWithDefault (error "lookup failed") f m
    FV v -> pVarToFPoly k (PFV v)
    DB i -> pVarToFPoly k (PDB (i + k))

-- |Generate a polynomial constant interpretation consisting of:
-- * linear part: a0 + a1 * x1(b11,...,b1k1) + an * xn(bn1,...,bnkn) for arguments x1,...xn
-- * HO part: cj * xj(x1,...xk) + dj * x1 * ... * xk * xj(x1,...xk)
--            for all combinations of FO and HO variables (fully applied)
-- * non-linear FO part: eij * xi * xj for i < j
constantInterpretation :: Typ -> FreshM (FPolynomial,[Int])
constantInterpretation (Typ bs _) = do
  let n = length bs
      vars = [(PDB (n-i), m) | (b,i) <- zip bs [1..], m <- [arity b] ]
      (foVars,hoVars) = partition ((== 0) . snd) vars
      arg par = PBase . Poly $ M.singleton MS.empty (fst par)
  p1 <- sequence [ MS.singleton . ApplPVar v <$> sequence [arg <$> mpar | mpar <- replicate m freshPar ]
                 | (v,m) <- vars ]
  let (p2,p3) = unzip . concat $
        [ [ (MS.singleton appl, MS.fromList (appl : map (`ApplPVar` []) (nub vs)))
          | vs <- replicateM m . map fst $ foVars
          , appl <- [ApplPVar w (map (pVarToFPoly 0) vs)] ]
        | (w,m) <- hoVars ]
      p4 = [ MS.fromList . map (`ApplPVar` []) $ [vi,vj]
           | (vi,i) <- zip (map fst foVars) [(0 :: Int)..], (vj,j) <- zip (map fst foVars) [0..], i < j ]
      addFreshPar x = (x,) . fst <$> freshPar
  constPart <- addFreshPar MS.empty
  (stricts,is) <- mapAndUnzipM (\x -> (\(par,i) -> ((x,par),i)) <$> freshPar) p1
  nonStricts <- mapM addFreshPar (p2 ++ p3 ++ p4)
  return (iterate PLam (PBase . Poly $ M.fromList (constPart : stricts ++ nonStricts)) !! n, is)

-- |Generate a map from constant identifiers to their parameterized polynomial interpretations
-- as well as a list which indicates the parameters wich have to be larger than 0.
constIntMapWithStricts :: Map Id Typ -> FreshM (Map Id (FPolynomial,[Int]))
constIntMapWithStricts = mapM constantInterpretation

-- |Generate a map from constant identifiers to their parameterized polynomial interpretations.
constIntMap :: Map Id Typ -> FreshM (Map Id FPolynomial)
constIntMap = mapM (fmap fst . constantInterpretation)

-- |Convert a pvar to an fpolynomial where the number of lambda abstractions is given by the first argument.
pVarToFPoly :: Int -> PVar -> FPolynomial
pVarToFPoly n x = iterate PLam (PBase p) !! n where
  p = Poly $
    M.singleton
    (MS.singleton
      (ApplPVar x [ PBase . Poly $ M.singleton (MS.singleton (ApplPVar (PDB (n-i)) [])) 1 | i <- [1..n]])
    )
    1

-- |Generate a parameter with a fresh name.
freshPar ::  FreshM (Parameter, Int)
freshPar = do
  i <- fresh
  return (Poly $ M.singleton (MS.singleton (Par i)) 1, i)

-- |Computes the application of a functional polynomial to another functional polynomial
-- via a form of beta-reduction.
--
-- >>> pretty $ pBeta (interpret cIntMap . parseTerm env $ "F") (interpret cIntMap . parseTerm env $ "t")
-- F(t)
pBeta :: FPolynomial -> FPolynomial -> FPolynomial
pBeta (PLam p) q = fpSubst 0 q p 
pBeta _ _ = error "type mismatch"

-- |Shifts all De Bruijn indices greater or equal than the first argument
-- by the second argument in a given functional polynomial.
fpShift :: Int -> Int -> FPolynomial ->  FPolynomial
fpShift i j (PLam p) = PLam $ fpShift (i+1) j p
fpShift i j (PBase p) = PBase $ pShift i j p

-- |Shifts all De Bruijn indices greater or equal than the first argument
-- by the second argument in a given polynomial.
pShift :: Int -> Int -> Polynomial -> Polynomial
pShift i j (Poly m) = Poly $ M.mapKeys (MS.map f) m where
  f (ApplPVar v@(PFV _) ps) = ApplPVar v (map (fpShift i j) ps)
  f (ApplPVar v@(PDB k) ps)
    | k < i = ApplPVar v (map (fpShift i j) ps)
    | otherwise = ApplPVar (PDB (k+j)) (map (fpShift i j) ps)

-- |Substitutes a De Bruijn index by a functional polynomial in a given functional polynomial.
fpSubst :: Int -> FPolynomial -> FPolynomial -> FPolynomial
fpSubst i q (PLam p) = PLam $ fpSubst (i+1) (fpShift 0 1 q) p
fpSubst i q (PBase p) = PBase $ pSubst i q p

-- |Substitutes a De Bruijn index by a functional polynomial in a given polynomial.
-- disclaimer: never invoke with a first argument < 0 due to hack regarding target
pSubst :: Int -> FPolynomial -> Polynomial -> Polynomial
pSubst i q (Poly m) = foldl' (+) (Poly rest) news where
  target = PDB (-1)
  m' = M.mapKeys (MS.map recurseAndShift) m
  (modify,rest) = M.partitionWithKey (\k _ -> target `MS.member` MS.map apvVar k) m'
  news = map (mSubst target q) (M.assocs modify)
  recurseAndShift (ApplPVar v@(PFV _) ps) = ApplPVar v (map (fpSubst i q) ps)
  recurseAndShift (ApplPVar v@(PDB k) ps) =
    let
      ps' = map (fpSubst i q) ps
     in case compare k i of
      LT -> ApplPVar v ps'
      EQ -> ApplPVar (PDB (-1)) ps' -- avoid clash with k-1, make it 'injective'
      GT -> ApplPVar (PDB (k-1)) ps'

-- |This function performs substitution of a variable with a functional polynomial in a given monomial.
-- Since there may be multiple occurrences of the variable in the monomial, the result is a list of
-- polynomials which is computed by applying the functional polynomial to the arguments of the variable
-- which it was substituted for and multiplying each polynomial by the remaining part of the monomial.
-- Note that the result consists of polynomials rather than functional polynomials as in our settting,
-- higher-order variables in monomials are always fully applied.
mSubst :: PVar -> FPolynomial -> (Monomial ApplPVarP,Parameter) -> Polynomial
mSubst target q (m,par) = foldl' (+) 0 $ map (* (Poly $ M.singleton rest par)) ms  where
  (modify,rest) = MS.partition ((== target) . apvVar) m
  ms = [ pFullBeta q (apvArgs apv) | apv <- MS.toList modify ]
  pFullBeta p qs = case foldl pBeta p qs of
    PBase r -> r
    -- we can do this because we always assume HO vars in monomials to be fully applied
    PLam _ -> error "polynomial interpretations in wrong form"



