{-# LANGUAGE OverloadedStrings #-}

-- |implementation of StarCPO
module Termination.StarCPO.Ordering where

import Prelude hiding ((&&),(||),and,or,not)

import Control.Monad (zipWithM)
import Control.Monad.Reader (Reader,runReader,asks)
import Data.List (permutations,delete)
import Language.Hasmtlib (Equatable(..),Orderable(..),Boolean(..),and,or,true,false,bool)

import Utils.Type (Accessor(..))
import Utils.SMT (Constraint,(<&&>),(<&&),(<||>))
import Typ.Type (Typ(..))
import Typ.Ops (arity,returnTyp,returnSort,argTyps,applyTyps)
import Term.Type (Term(..),Head(..))
import Term.Ops (hdToTerm,shiftDB,addLams)
import Subst.Ops (applyAbsToTerms)
import Termination.StarCPO.Type (CPOInfo(..),IsStatus(..))

type StatComp a b = [Term] -> [Term] -> Reader (CPOInfo a b) Constraint

-- |Remove leading abstractions from term
removeAbs :: Term -> Term
removeAbs s = s{nlams = 0, typ = returnTyp (typ s)}

-- |Given a starred non-abstraction s, adjust its type to a
-- * via changing the type of the starred function symbol as well as
-- * eta expansion.
adjustType :: Term -> Typ -> Term
adjustType s a = sShifted{nlams = n, typ = a, sp = sp sShifted ++ dbs} where
  n = arity a
  dbs = [hdToTerm b (DB $ n-i-1) | (b,i) <- zip (argTyps a) [0..]]
  sShifted = shiftDB n s

-- |Pull down u by applying it to appropriately typed versions of the starred term s
-- * and put it into the abstractions according to s
pullDown :: Term -> Term -> Term
pullDown u@(Term {typ = Typ bs _}) s = let
  ss = [adjustType s' b | b <- bs]
  s' = removeAbs s
  in case applyAbsToTerms u ss of
    Just v -> v{nlams = nlams s, typ = Typ (argTyps (typ s)) (returnSort (typ v))}
    Nothing -> error "impossible case"

-- |Given a starred term s = x_k.f*(s_n) and a type a which is an extension of the type of s,
-- extend s to x_k,y_l.f*(s_n,y_l)
extend :: Term -> Typ -> Term
extend s a = case applyTyps a (argTyps (typ s)) of
  Just b -> (adjustType (removeAbs s) b){nlams = arity a, typ = a}
  Nothing -> error "impossible case "

-- |A wrapper for StarCPO
scpoWrapper :: (Orderable a, IsStatus b, Equatable b) => CPOInfo a b -> Term -> Term -> Constraint
scpoWrapper cpoinfo s t = runReader (scpo s t) cpoinfo

scpoWeakWrapper :: (Orderable a, IsStatus b, Equatable b) => CPOInfo a b -> Term -> Term -> Constraint
scpoWeakWrapper cpoinfo s t = runReader (scpoWeak s t) cpoinfo

-- |Implementation of StarCPO
scpo :: (Orderable a, IsStatus b, Equatable b) => Term -> Term -> Reader (CPOInfo a b) Constraint
scpo s@(Term {hd = F f}) t = scpoWeak s{hd = FStar f (length (sp s))} t
scpo _ _ = pure false

scpoWeak :: (Orderable a, IsStatus b, Equatable b) => Term -> Term -> Reader (CPOInfo a b) Constraint
scpoWeak s@(Term {typ = Typ as a}) t@(Term {typ = Typ bs b})
  | as /= bs  = pure false
  | s == t    = pure true
  | otherwise = do
    sortPrec <- asks sPrec
    funPrec <- asks fPrec
    st <- asks stat
    sortPrec ! a >=? sortPrec ! b <&&  case hd s of
      F f -> scpoWeak s{hd = FStar f (length (sp s))} t <||> case hd t of -- <Put>
          F g -> (funPrec ! f === funPrec ! g && st ! f === st ! g) <&& mulLex scpoGMulWeak scpoGLexWeak (st ! f) sps' spt' -- <Fun>
          _ -> pure false
      FStar f n -> (or <$> traverse (\u -> scpoWeak (absSubt $ pullDown u s) t) (sp s)) <||> case hd t of -- <Select>
        F g -> (funPrec ! f >? funPrec ! g <&& (and <$> traverse (\u -> scpoWeak (extend s (typ u)) u) spt')) <||> -- <Copy>
               ((funPrec ! f === funPrec ! g && st ! f === st ! g) <&& -- <Stat>
                (and <$> traverse (\u -> (scpoWeak (extend s (typ u)) u)) spt') <&&> 
                mulLex scpoGMul scpoGLex (st ! f) (take n sps') spt') 
        _ -> pure false
      _ -> bool (hd s == hd t) <&& (and <$> zipWithM scpoWeak sps' spt') -- <Var>
  where
    sps' = (map absSubt (sp s))
    spt' = (map absSubt (sp t))
    absSubt = addLams as

mulLex :: (Orderable a, IsStatus b, Equatable b) => StatComp a b -> StatComp a b -> b -> [Term] -> [Term] ->
           Reader (CPOInfo a b) Constraint
mulLex mulComp lexComp status ss ts = (isMul status <&& mulComp ss ts) <||> (isLex status <&& lexComp ss ts)

scpoGLex :: (Orderable a, IsStatus b, Equatable b) => [Term] -> [Term] -> Reader (CPOInfo a b) Constraint
scpoGLex ss ts
  | length ss > length ts = and <$> zipWithM scpoWeak ss ts
  | otherwise             = go ss ts
  where
    go [] _ = pure false
    go _ [] = error "impossible case"
    go (si:ssr) (ti:ttr) = scpo si ti <||> (scpoWeak si ti <&&> go ssr ttr)

scpoGLexWeak :: (Orderable a, IsStatus b, Equatable b) => [Term] -> [Term] -> Reader (CPOInfo a b) Constraint
scpoGLexWeak ss ts
  | length ss == length ts = and <$> zipWithM scpoWeak ss ts
  | otherwise              = pure false

scpoGMul :: (Orderable a, IsStatus b, Equatable b) => [Term] -> [Term] -> Reader (CPOInfo a b) Constraint
scpoGMul ss ts = go ts ss [] where
  go (u:us) as bs = (or <$> traverse (\b -> scpo b u <&&> go us as bs) bs) <||>
                    (or <$> traverse (\a -> scpo a u <&&> go us (delete a as) (a:bs)) as) <||>
                    (or <$> traverse (\a -> scpoWeak a u <&&> go us (delete a as) bs) as)
  go [] _ [] = pure false
  go [] _ _ = pure true

scpoGMulWeak :: (Orderable a, IsStatus b, Equatable b) => [Term] -> [Term] -> Reader (CPOInfo a b) Constraint
scpoGMulWeak ss ts
  | length ss == length ts = or <$> traverse (\ss' -> and <$> zipWithM scpoWeak ss' ts) (permutations ss)
  | otherwise              = pure false
