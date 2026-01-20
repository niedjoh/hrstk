{-# LANGUAGE OverloadedStrings #-}

-- |collection of useful functions for simply-typed terms
module Term.Ops where

import Data.List.Extra (dropEnd,splitAtEnd)
import Data.Map.Strict (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

import Utils.Misc (consIf)
import Utils.Type (Var)
import Typ.Type (Typ(..))
import Typ.Ops (order,liftTyp,arity,returnTyp)
import Term.Type (Term(..),Head(..),Subterm)

-- |Utility function for term creation.
mkTerm :: Head -> Typ -> [Term] -> Term
mkTerm h a ts = Term {nlams = arity a, hd = h, sp = ts, typ = a}

-- |Checks whether a head is a function symbol
isFun :: Head -> Bool
isFun (F _) = True
isFun (FV _) = False
isFun (DB _) = False

isFV :: Head -> Bool
isFV (F _) = False
isFV (FV _) = True
isFV (DB _) = False

-- |Computes the set of free variables of a term.
freeVars :: Term -> Set Var
freeVars s@(Term {hd = F _}) = S.unions (map freeVars (sp s))
freeVars s@(Term {hd = FV v}) = S.unions (S.singleton v : map freeVars (sp s))
freeVars s@(Term {hd = DB _}) = S.unions (map freeVars (sp s))

-- |Computes the free variables and their types of a term.
freeVarsTypMap :: Term -> Map Var Typ
freeVarsTypMap s@(Term {hd = F _}) = M.unions (map freeVarsTypMap (sp s))
freeVarsTypMap s@(Term {hd = FV v, typ = Typ _ a}) =
  M.unions $ M.singleton v (Typ (map typ $ sp s) a) : map freeVarsTypMap (sp s)
freeVarsTypMap s@(Term {hd = DB _}) = M.unions (map freeVarsTypMap (sp s))

-- |Determines whether the head of the term is a free variable.
isHeadedByFreeVar :: Term -> Bool
isHeadedByFreeVar (Term {hd = FV _}) = True
isHeadedByFreeVar _ = False

-- |Determines whether a given term only consists of De Bruijn indices.
isDBTerm :: Term -> Bool
isDBTerm s@(Term {hd = DB _}) = all isDBTerm (sp s)
isDBTerm _ = False

-- |Checks whether the term has at most order two.
-- More precicely, "second order" means hat all constants have types of order at most three,
-- free variables have types of order at most two and bound variables have order at most one.
secondOrder :: Term -> Bool
secondOrder s@(Term {hd = F _}) = all ((<= 2) . order . typ) (sp s) && all secondOrder (sp s)
secondOrder s@(Term {hd = FV _}) = all ((<= 1) . order . typ) (sp s) && all secondOrder (sp s)
secondOrder s@(Term {hd = DB _}) = null (sp s)

-- |Given a type and a head, this function returns the corresponding
-- term in lnf.
hdToTerm :: Typ -> Head -> Term
hdToTerm a@(Typ bs _) h =
  Term {nlams = k, hd = h', sp = [hdToTerm c (DB j) |(c,j) <- zip bs [k-1,k-2..]], typ = a} where
    k = length bs
    h' = case h of
      DB i -> DB $ i+k
      _ -> h

-- |Put a term in a given context of lambda abstractions
addLams :: [Typ] -> Term -> Term
addLams as s = s{nlams = length as + nlams s, typ = liftTyp as (typ s)}

-- |Determines whether the term contains DB's which are smaller than a given number
containsDBrel :: (Int -> Int -> Bool) -> Term -> Bool
containsDBrel rel = go 0 where
  go i s = let
    i' = i + nlams s
    recRes = any (go i') (sp s)
    in case hd s of
      DB j -> rel i' j || recRes
      _ -> recRes

-- |Determines whether the term contains a dangling De Bruijn index.
danglingDB :: Term -> Bool
danglingDB = containsDBrel (\i' j -> i' <= j)

-- |Shifts all De Bruijn indices in a given term by the given integer.
shiftDB :: Int -> Term -> Term
shiftDB = go 0 where
  go i k s@(Term {hd = DB j}) = let
    i' = i + nlams s
    j' = if i' <= j then j+k else j
    in s{hd = DB j', sp = map (go i' k) (sp s)}
  go i k s = let
    i' = i + nlams s
    in s{sp = map (go i' k) (sp s)}

-- |checks whether a given term is an eta-expansion of a term which is not an abstraction
expandedTerm :: Term -> Bool
expandedTerm s = occCond && dbTailCond where
  n = nlams s
  (ss,ts) = splitAtEnd n (sp s)
  occCond = not $ containsDBrel (\i' j -> i' <= j && j < n+i') s{nlams = 0, sp = ss}
  dbTailCond = and [t == hdToTerm (typ t) (DB i) | (t,i) <- zip (reverse ts) [0..]]

-- |checks whether a term t is an expanded subterm of s
expandedSubtermEqRel :: Term -> Term -> Bool
expandedSubtermEqRel s t = expandedTerm t && go 0 s where
  m = nlams t
  t' = shiftDB (-m) t{nlams = 0, sp = dropEnd m (sp t)}
  go i u
    | hd u == hd t'' = (all (uncurry (==)) $ zip (sp u) (sp t'')) || recRes
    | otherwise = recRes
    where
      i' = i + nlams u
      t'' = shiftDB i' t'
      recRes = or [go i' u' | u' <- sp u]

-- |Determines whether a given term is a deterministic higher-order pattern
-- (free variables only have distinct ground arguments which contain at least
--  one bound variable and their eta-nf is not an abstraction)
isDHP :: Term -> Bool
isDHP s@(Term {hd = FV _}) =
  all (\t -> danglingDB t && S.null (freeVars t) && expandedTerm t) (sp s) && localRestriction (sp s) where
    localRestriction ts = not $ any (uncurry expandedSubtermEqRel) [ (u,v)
                                                                   | (u,i) <- zip ts [0 :: Int ..]
                                                                   , (v,j) <- zip ts [0..]
                                                                   , i /= j ]
isDHP s = all isDHP $ sp s

-- |Returns all subterms which satisfy the given predicate.
-- Note that by definintion, subterms always have a sort type.
filteredSubterms :: (Term -> Bool) -> Term -> [Subterm]
filteredSubterms p = go id [] []  where
  go acc typs rp s@(Term {typ = Typ as _}) = let
    typs' = typs ++ as
    acc' = \x -> acc (Term {nlams = nlams s, hd = hd x, sp = sp x, typ = typ s})
    s' = s{nlams = 0, typ = returnTyp . typ $ s}
    in consIf (p s')
       (acc',typs',reverse rp,s')
       [r | (t,i) <- zip (sp s) [1..], r <- recurse acc' typs' rp s t i (splitAt (i-1) (sp s))]
  recurse acc typs rp s t i (ts1,_:ts2) = go (acc . (\x -> s{sp = (ts1 ++ (x:ts2))})) typs (i:rp) t
  recurse _ _ _ _ _ _ _ = error "impossible case"
