-- |implementation of matching for DHPs
module Subst.Match where

import qualified Data.Map.Strict as M
import Data.List (foldl')

import Typ.Ops (returnTyp,liftTyp)
import Term.Type (Term(..),Head(..))
import Subst.Type (Subst(..), SubstL)
import Subst.Ops (discharge)

-- |@match s t@ Computes the matching substitution @σ@ such that @sσ = t@ if possible
-- where @s@ is a DHP. The function returns 'Nothing' for non-DHPs @s@.
-- This function invokes the main function 'matchList' and then checks whether the resulting
-- list of singleton substitutions can be combined into a legal substitution which maps
-- variables to unique elements.
match :: Term -> Term -> Maybe Subst
match s t = do
  substl <- matchList s t
  Subst <$> foldl' combineFun (Just M.empty) substl where
    insertFun _ new _ = new
    combineFun (Just m) (k,v) = case M.insertLookupWithKey insertFun k v m of
      (Just v', _)
        | v == v'   -> Just m
        | otherwise -> Nothing
      (Nothing, m') -> Just m'
    combineFun Nothing _ = Nothing

-- |Main function of the matching algorithm. Produces a SubstL which is then converted into a proper
-- substitution if possible.
matchList :: Term -> Term -> Maybe SubstL
matchList = go 0 where
  go k s@(Term {hd = FV v}) t
    | nlams s == nlams t = do
        let n = length . sp $ s
            lu = [(u,n-i-1) | (u,i) <- zip (sp s) [0..]]
        u <- discharge (k+nlams s) lu t{nlams = 0, typ = returnTyp . typ $ t}
        return [(v,u{nlams = length lu, typ = liftTyp (map (typ . fst) lu) (typ u)})]
    | otherwise = Nothing
  go k s t
    | nlams s == nlams t && hd s == hd t = concat <$> mapM (uncurry $ go $ k + nlams s) (zip (sp s) (sp t))
    | otherwise = Nothing
