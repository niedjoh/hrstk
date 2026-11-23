module WellBehaved (checkWellBehavedness,etaReduceAnchorsAtRoot) where

import Data.List (partition)
import qualified Data.Set as S

import Utils.Type (Var(..))
import Term.Type (Term(..),Head(..))
import Term.Ops (freeVars, shiftDB, isBasic, containsDBrel)

-- | Computes the arities of all free variables.
getArities :: Term -> [(Var,Int)]
getArities term = case hd term of
  FV x -> (x, length $ sp term) : concatMap getArities (sp term)
  _ -> concatMap getArities (sp term)

-- |Checks if the arity of a function symbol is consistent through the whole term
checkArityConsitency :: [(Var,Int)] -> Bool
checkArityConsitency [] = True
checkArityConsitency ((v,i):xs) = all (\(_,i') -> i' == i) dups && checkArityConsitency rest where
  (dups,rest) = partition (\(v',_) -> v == v') xs

-- | Check if the lhs of an STMRS is well-behaved
checkWellBehavedness :: Term -> Bool
checkWellBehavedness s = checkArityConsitency arities && go s (freeVars s) arities where
  arities = getArities s
  go t w ar
    | FV v <- hd t, v `S.member` w = all (\child -> (nlams child == 0) && all (\grandchild -> go grandchild w ar) (sp child)) (sp t)
    | otherwise = isBasic t && all (\child -> go child w ar) (sp t)

-- | Eta-reduces, at the root, every anchor that is an abstraction.
-- All other subterms are only traversed, not changed, so they stay eta-long.
etaReduceAnchorsAtRoot :: Term -> Term
etaReduceAnchorsAtRoot s@(Term {hd = FV _}) = s{sp = map doAnchor (sp s)} where
  doAnchor u@(Term {nlams = n})
    | n > 0     = etaReduceRoot u
    | otherwise = etaReduceAnchorsAtRoot u
etaReduceAnchorsAtRoot s = s{sp = map etaReduceAnchorsAtRoot (sp s)}

etaReduceRoot :: Term -> Term
etaReduceRoot s@(Term {nlams = n})
  | n == 0 || null (sp s) = s
  | otherwise = let s' = s{sp = init (sp s) ++ [etaReduceRoot (last . sp $ s)]} in
      if isEtaReducible s'
        then etaReduceRoot (dropInnermostLambda s)
        else s

-- | Checks if a term is eta-reducible
isEtaReducible :: Term -> Bool
isEtaReducible Term{nlams = 0} = False
isEtaReducible Term{hd = DB 0} = False
isEtaReducible (Term {sp = []}) = False
isEtaReducible s@(Term{nlams = n})
 | not (isBareDB0 (last . sp $ s)) = False
 | otherwise = not $ containsDBrel (==) (n-1) s{nlams = 0, sp = init (sp s)}

isBareDB0 :: Term -> Bool
isBareDB0 Term{nlams = 0, hd = DB 0, sp = []} = True
isBareDB0 _ = False

-- | Removes the innermost lambda and the last argument:
--   Precondition: xn occurs nowhere else (checked by isEtaReducible).
dropInnermostLambda :: Term -> Term
dropInnermostLambda t = (shiftDB (-1) t {nlams = 0, sp = init (sp t)}){nlams = nlams t - 1}

