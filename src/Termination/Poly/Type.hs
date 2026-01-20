{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

-- |efficient implementation of polynomials based on maps which gives distribution and factoring for free
module Termination.Poly.Type where

import Data.List (intersperse,sortOn)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MS
import Prettyprinter (Pretty,pretty,(<+>),parens)

import Utils.Type (Var)
import Utils.Pretty (parensIf)

-- |monomials as multisets of variables
type Monomial v = MultiSet v

-- |polynomials represented as maps from multisets of variables to constants
newtype Poly v c = Poly (Map (Monomial v) c) deriving (Eq, Ord)

-- |functional polynomial interpretations (with lambda abstraction)
data FPoly v c = PLam (FPoly v c) | PBase (Poly v c) deriving (Eq, Ord)

-- |variables in polynomials
data PVar = PDB Int | PFV Var deriving Eq

-- |custom 'Ord' instance because DBs are in reverse direction of printed names
instance Ord PVar where
  compare (PDB _) (PFV _) = LT
  compare (PFV _) (PDB _) = GT
  compare (PDB i) (PDB j) = compare j i
  compare (PFV v) (PFV w) = compare v w

-- |symbolic parameters
newtype Par = Par Int deriving (Eq, Ord)

-- |representation of symbolic coefficients which are then solved for
type Parameter = Poly Par Int

-- |polynomial variables applied to functional polynomials
data ApplPVar c = ApplPVar PVar [FPoly (ApplPVar c) c] deriving (Eq, Ord)

-- |standard usage of applied variables
type ApplPVarP = ApplPVar Parameter

-- |polynomial interpretations of terms of ground type
type Polynomial = Poly ApplPVarP Parameter

-- |functional polynomial interpretations
type FPolynomial = FPoly ApplPVarP Parameter

instance Pretty Par where
  pretty (Par i) = "a" <> pretty i

instance (Eq c, Num c, Pretty c, Pretty v) => Pretty (Poly v c) where
  pretty (Poly m)
    | M.null m  = "0"
    | otherwise = foldr1 (<>) (intersperse "+" (map f (M.assocs m))) where
      f (k,v)
        | MS.null k = pretty v
        | v == 1    = rest 
        | otherwise = pretty v <> "*" <> rest where
            rest = foldr1 (<>) (intersperse "*" (map pretty (MS.elems k)))
 
instance Pretty FPolynomial where
  pretty = go [] (0 :: Int) where
    go ctx d (PLam p) = 
      let var = "y" <> pretty d
      in "λ" <> var <> "." <> go (var:ctx) (d+1) p
    go ctx d (PBase (Poly m))
      | M.null m  = "0"
      | otherwise = foldr1 (<+>) (intersperse "+" (map prettyMonomial assocs)) where
          assocs = sortOn fst (M.assocs m)
          prettyMonomial (ms,par)
            | MS.null ms = pretty par
            | par == 1   = rest
            | otherwise  = parensIf (isPlus par) (pretty par) <+> "*" <+> rest where
                rest = foldr1 (\x y -> x <+> "*" <+> y) (map prettyVar (MS.elems ms))
          isPlus (Poly a) = M.size a >= 2   
          prettyVar (ApplPVar (PDB i) ps)
            | i < length ctx = applyIf (not $ null ps) (ctx !! i) ps
            | i < 0          = error "negative PDB"
            | otherwise      = error "dangling PDB"
          prettyVar (ApplPVar (PFV v) ps) = applyIf (not $ null ps) (pretty v) ps
          applyIf p v args
            | p         = v <> parens (foldr1 (<>) (intersperse "," (map (go ctx d) args)))
            | otherwise = v

-- the only difference here is that the parentheses (isPlus) are missing (and some spacing)..
-- TODO is it possible to define just one instance?
instance Pretty (FPoly (ApplPVar Int) Int) where
  pretty = go [] (0 :: Int) where
    go ctx d (PLam p) = 
      let var = "y" <> pretty d
      in "λ" <> var <> "." <> go (var:ctx) (d+1) p
    go ctx d (PBase (Poly m))
      | M.null m  = "0"
      | otherwise = foldr1 (<+>) (intersperse "+" (map prettyMonomial assocs)) where
          assocs = sortOn fst (M.assocs m)
          prettyMonomial (ms,i)
            | MS.null ms = pretty i
            | i == 1     = rest
            | otherwise  = pretty i <> "*" <> rest where
                rest = foldr1 (\x y -> x <> "*" <> y) (map prettyVar (MS.elems ms))
          prettyVar (ApplPVar (PDB i) ps)
            | i < length ctx = applyIf (not $ null ps) (ctx !! i) ps
            | i < 0          = error "negative PDB"
            | otherwise      = error "dangling PDB"
          prettyVar (ApplPVar (PFV v) ps) = applyIf (not $ null ps) (pretty v) ps
          applyIf p v args
            | p         = v <> parens (foldr1 (<>) (intersperse "," (map (go ctx d) args)))
            | otherwise = v

instance (Ord v, Eq c, Num c) => Num (Poly v c) where
  (+) (Poly x) (Poly y) = normPoly . Poly $ M.unionWith (+) x y
  (*) (Poly x) (Poly y) =
    normPoly . Poly $ M.fromListWith (+) [ (vs1 `MS.union` vs2,c1 * c2)
                                     | (vs1,c1) <- M.assocs x, (vs2,c2) <- M.assocs y ]  
  fromInteger i = Poly $ M.singleton MS.empty (fromInteger i)
  negate (Poly x) = Poly $ M.map negate x
  abs = error "not implemented"
  signum = error "not implemented"

-- |Discard monomials with coefficient 0.
normPoly :: (Eq c, Num c) => Poly v c -> Poly v c 
normPoly (Poly m) = Poly $ M.filter (/= 0) m

-- |Discard monomials with coefficient 0.
normFPoly :: (Eq c, Num c) => FPoly v c -> FPoly v c
normFPoly (PLam fp) = PLam . normFPoly $ fp
normFPoly (PBase p) = PBase . normPoly $ p

-- |Discard monomials with coefficient 0.
normApplPVarPoly :: (Ord c, Num c) => Poly (ApplPVar c) c -> Poly (ApplPVar c) c
normApplPVarPoly (Poly m) = Poly . M.mapKeysMonotonic f $ M.filter (/= 0) m where
  f = MS.mapMonotonic g
  g (ApplPVar v args) = ApplPVar v (map normFPoly args)

-- |Discard monomials with coefficient 0.
normApplPVarFPoly :: (Ord c, Num c) => FPoly (ApplPVar c) c -> FPoly (ApplPVar c) c
normApplPVarFPoly (PLam fp) = PLam . normApplPVarFPoly $ fp
normApplPVarFPoly (PBase p) = PBase . normApplPVarPoly $ p

-- |Accessor for variable part of applied polynomial variable.
apvVar :: ApplPVar c -> PVar
apvVar (ApplPVar v _) = v

-- |Accessor for argument part of applied polynomial variable.
apvArgs :: ApplPVar c -> [FPoly (ApplPVar c) c]
apvArgs (ApplPVar _ fps) = fps
