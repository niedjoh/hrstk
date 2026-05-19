-- |collection of useful functions for substitutions
module Subst.Ops where

import Data.List (stripPrefix)
import Data.List.Extra (dropEnd)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Set (Set)

import Utils.Type (Var)
import Typ.Type (Typ(..))
import Typ.Ops (returnTyp,arity,applyTyps)
import Term.Type (Term(..),Head(..))
import Term.Ops (hdToTerm,shiftDB)
import Subst.Type (Subst(..))

-- |Variable lookup for substitutions wrapped inside Maybe.
(!?) :: Subst -> Var -> Maybe Term
(Subst m) !? v = m M.!? v

infixl 9 !?

-- |The empty substitution.
empty :: Subst
empty = Subst M.empty

-- |A singleton substitution.
singleton :: Var -> Term -> Subst
singleton = (Subst .) . M.singleton

-- |Restrict a substituttion to a given set of variables.
restrictToVars :: Set Var -> Subst -> Subst
restrictToVars vars (Subst m) = Subst $ M.restrictKeys m vars

-- |Given a list [t1,...,tk] of terms, this function creates the map
-- k-i |-> ti
-- from De Bruijn indices to these terms.
dbMap :: [Term] -> Map Int Term
dbMap ts = M.fromDescList $ zip [k-1,k-2 .. 0] ts where
  k = length ts

-- |Applies a map from De Bruijn indices to terms to a term.
applyDBMap :: Int -> Map Int Term -> Term -> Term
applyDBMap j m s
      | DB i <- hd s, Just u <- m' M.!? i =
         (applyDBMap (nlams u) (dbMap recRess) u{nlams = 0, typ = returnTyp (typ u)}){nlams = nlams s, typ = typ s}
      | DB i <- hd s, i >= j' = s{hd = DB $ i - j, sp = recRess}
      | otherwise = s{sp = recRess}
      where
        k = nlams s
        j' = j+k
        m' = M.map (shiftDB k) $ M.mapKeysMonotonic (+ k) m
        recRess = map (applyDBMap j m') $ sp s

-- |The substitution function on terms.
apply :: Subst -> Term -> Term
apply = go 0 where
  go k subst s
    | FV v <- hd s, Just u <- subst !? v =
      (applyDBMap (nlams u) (dbMap recRess) (shiftDB k' u){nlams = 0, typ = returnTyp (typ s)}){nlams = nlams s, typ = typ s}
    | otherwise = s{sp = recRess}
    where
      k' = k + nlams s
      recRess = map (go k' subst) $ sp s

applyToPair :: Subst -> (Term,Term) -> (Term,Term)
applyToPair subst (s,t) = (apply subst s, apply subst t)

-- |Substitution composition.
compose :: Subst -> Subst -> Subst
compose subst@(Subst m) (Subst n) = Subst (M.union (M.map (apply subst) n) m)

-- |Apply an abstraction to a given variable
applyAbsToVar :: Term -> Var -> Term
applyAbsToVar s@(Term {typ = Typ (a:as) b}) v =
  applyDBMap 0 (M.singleton 0 (hdToTerm a $ FV v)) s{nlams = nlams s - 1, typ = Typ as b}
applyAbsToVar _ _ = error "term is not an abstraction"

-- |Apply an abstraction to a list of terms.
applyAbsToTerms :: Term -> [Term] -> Maybe Term
applyAbsToTerms s ts = do
  a <- applyTyps (typ s) (map typ ts)
  Just $ applyDBMap 0 (dbMap ts) s{nlams = arity a, typ = a}

-- |This function replaces subterms by  De Bruijn indices according to the association list.
-- DBs up to the first argument can only be constructed from the terms in the association list.
-- DBS above the first argument are normalized accordingly.
-- It is assumed that the eta-NFs of the terms in the association list are not abstractions.
discharge :: Int -> [(Term,Int)] -> Term -> Maybe Term
discharge k lu u = go lu 0 u where
  go ((s,i):xs) n t
    | hds' == hd t, Just us <- stripPrefix (dropEnd (nlams s) sps') (sp t) = do
        us' <- mapM (go lu n') us
        Just t{hd = DB $ i + n', sp = us'}
    | otherwise = go xs n t
    where
      n' = n + nlams t
      hds' = case hd s of
        DB j -> DB $ j - nlams s + n'
        _ -> hd s
      sps' = map (shiftDB (- nlams s + n')) (sp s)
  go [] n t = do
    let n' = n + nlams t
    ts <- mapM (go lu n') (sp t)
    let res = t{sp = ts}
    case hd t of
      DB j
        | j < n'    -> Just res
        | n'+k <= j -> Just res{hd = DB $ j-k+length lu}
        | otherwise -> Nothing
      _ -> Just res
