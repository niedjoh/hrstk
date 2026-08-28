-- |implementation of StarCPO
module Termination.StarCPO.Ordering where

import Prelude hiding ((&&),(||),and,or,not)

import Control.Monad (zipWithM)
import Control.Monad.Reader (Reader,runReader,asks)
import Data.List (permutations,delete)
import Data.Set (Set)
import qualified Data.Set as S
import Language.Hasmtlib (Equatable(..),Orderable(..),Boolean(..),and,or,true,false,bool)

import Utils.Type (Accessor(..),Var,Id)
import Utils.Misc (allPossibilities)
import Utils.SMT (Constraint,(<&&>),(<&&),(<||>))
import Typ.Type (Typ(..))
import Typ.Ops (arity,returnTyp,returnSort,argTyps,equatableByTypApp,posOf)
import Term.Type (Term(..),Head(..))
import Term.Ops (hdToTerm,danglingDB,shiftDB,addLams)
import Subst.Ops (applyAbsToTerms)
import Termination.NCPO.Type (CPOInfo(..),IsStatus(..))

type StatComp a b = [Term] -> [Term] -> Reader (CPOInfo a b) Constraint
  
star :: Term -> Maybe Term
star s = case hd s of
  F f -> Just s{hd = FStar f (length (sp s))}
  _ -> Nothing

pullDown :: [Typ] -> Term -> Term -> Term -- TODO test
pullDown as u@(Term {typ = Typ bs _}) s = let
  ss = [(shiftDB n sAux){nlams = n, typ = b} | b <- bs, let n = arity b]
  sAux = s{nlams = 0, typ = returnTyp (typ s)}
  in case applyAbsToTerms u ss of
    Just v -> v{nlams = length as, typ = Typ as (returnSort (typ v))}
    Nothing -> error "impossible case"

extend :: Term -> Term -> Term -- TODO test
extend s u
  | n >= k = sAux'{nlams = n, typ = typ u, sp = sp sAux' ++ [hdToTerm a (DB $ n-k-i) | (a,i) <- zip (drop k (argTyps (typ u))) [0..]]}
  | otherwise = error "impossible case"
  where
    sAux' = (shiftDB (n-k) sAux)
    sAux = s{nlams = 0, typ = returnTyp (typ s)}
    k = nlams s
    n = nlams u

-- |A wrapper for StarCPO
scpoWrapper :: (Orderable a, IsStatus b, Equatable b) => CPOInfo a b -> Term -> Term -> Constraint
scpoWrapper cpoinfo s t = runReader (scpo s t) cpoinfo

scpoWeakWrapper :: (Orderable a, IsStatus b, Equatable b) => CPOInfo a b -> Term -> Term -> Constraint
scpoWeakWrapper cpoinfo s t = runReader (scpoWeak s t) cpoinfo

-- |Implementation of StarCPO
scpo :: (Orderable a, IsStatus b, Equatable b) => Term -> Term -> Reader (CPOInfo a b) Constraint
scpo s t = case star s of
  Just s' -> scpoWeak s' t
  Nothing -> pure false

scpoWeak :: (Orderable a, IsStatus b, Equatable b) => Term -> Term -> Reader (CPOInfo a b) Constraint
scpoWeak s@(Term {typ = Typ as a}) t@(Term {typ = Typ bs b})
  | as /= bs  = pure false
  | s == t    = pure true
  | otherwise = do
    sortPrec <- asks sPrec
    funPrec <- asks fPrec
    st <- asks stat
    sortPrec ! a >=? sortPrec ! b <&& case hd s of
      F f -> case hd t of
        F g -> (funPrec ! f === funPrec ! g && st ! f === st ! g) <&& mulLex scpoGMulWeak scpoGLexWeak (st ! f) sps' spt' -- <Fun>
        _ -> case star s of
          Just s' -> scpoWeak s' t -- <Put>
          Nothing -> error "impossible case"
      FStar f n ->  or <$> traverse (\u -> scpoWeak (pullDown as u s) t) (sp s) <||> case hd t of -- <Select>
        F g -> (funPrec ! f >? funPrec ! g <&& (and <$> traverse (\u -> scpoWeak (extend s u) u) (sp t))) <||> -- <Copy>
               ((funPrec ! f === funPrec ! g && st ! f === st ! g) <&& -- <Stat>
                (and <$> traverse (\u -> (scpoWeak (extend s u) u)) (sp t)) <&&> 
                mulLex scpoGMul scpoGLex (st ! f) (take n sps') spt') 
        _ -> pure false
      _ -> bool (hd s == hd t) <&& and <$> zipWithM scpoWeak sps' spt' -- <Var>
  where
    sps' = (map absSubt (sp s))
    spt' = (map absSubt (sp t))
    absSubt = addLams (argTyps . typ $ s)

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
  go [] as bs = pure true

scpoGMulWeak :: (Orderable a, IsStatus b, Equatable b) => [Term] -> [Term] -> Reader (CPOInfo a b) Constraint
scpoGMulWeak ss ts
  | length ss == length ts = or <$> traverse (\ss' -> and <$> zipWithM scpoWeak ss' ts) (permutations ss)
  | otherwise              = pure false

{-

-- |The two arguments are connected by the composition of the following relations:
-- * reflexive closure of basic subterm relation
-- * reflexive closure of accessibility relation
-- * weak orient with NCPO
--
-- Note that we only allow to proceed to subterms via "nonversatile paths"
bawo :: (Orderable a, IsStatus b, Equatable b) =>
  Bool -> Term -> Term -> ReaderT (CPOInfo a b) FreshM Constraint
bawo varRec s t = awo varRec s t <||> go s t where
  varCond u = not . bool $ danglingDB u
  go u@(Term {hd = F _, typ = Typ _ a}) v = do
      basic <- asks isBasic
      let u' = u{nlams = 0, typ = Typ [] a}
      ((basic ! a && varCond v) <&& awo varRec u' v) <||> (or <$> traverse (\w -> go w v) (sp u))
  go _ _ = pure false

-- |accessibility subterm relation with generic compare function for base case
accSubt :: CompareFun a b -> Term -> Term -> ReaderT (CPOInfo a b) FreshM Constraint
accSubt comp s@(Term {hd = F f}) t = do
  acc <- asks isAccessible
  or <$> traverse (\(u,i) -> acc ! (f,i) <&& (comp u t <||> accSubt comp u t))  (zip (sp s) [0..])
accSubt _ _ _ = pure false

-- |The two arguments are connected by the composition of the following relations:
-- * reflexive closure of accessibility relation
-- * weak orient with NCPO
--
-- Note that we only allow to proceed to subterms for applied function symbols
awo :: (Orderable a, IsStatus b, Equatable b) =>
  Bool -> Term -> Term -> ReaderT (CPOInfo a b) FreshM Constraint
awo varRec s t =
  ncpoWeak varRec Compare S.empty s t <||> accSubt (ncpoWeak varRec Compare S.empty) s t

-- |structurally smaller + orient with variable set reset
sso :: (Orderable a, IsStatus b, Equatable b) =>
  Bool -> Set (Var,Typ) -> Term -> Term -> ReaderT (CPOInfo a b) FreshM Constraint
sso varRec vars s@(Term {typ = Typ [] a}) t =
  ncpo varRec Compare S.empty s t <||> accSubt comp s t where
    comp u _ = case equatableByTypApp (typ s) (typ u) of
        Nothing -> pure false
        Just cs -> do
          let candidateVars = [filter ((== c) . snd) (S.toList vars) | c <- cs]
          if [] `elem` candidateVars || any (\c -> bool $ posOf a c /= S.empty) cs
            then pure false
            else do
              let possibleVarLists = allPossibilities candidateVars
                  toTerm (x,c) = hdToTerm c (FV x)
                  f xs = case applyAbsToTerms u (map toTerm xs) of
                    Just uxs -> pure . bool $ uxs == t
                    Nothing -> pure false
              or <$> traverse f possibleVarLists
sso varRec _ s t = ncpo varRec Compare S.empty s t

-}
