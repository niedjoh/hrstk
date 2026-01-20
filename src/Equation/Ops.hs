-- |collection of useful functions for substitutions
module Equation.Ops where

import qualified Data.Set as S

import Typ.Ops (sort)
import Term.Type (Term(..))
import Term.Ops (freeVars,isHeadedByFreeVar,isDHP)
import Subst.Ops (apply)
import Subst.Match (match)
import Equation.Type (Equation(..))

termMap :: (Term -> Term) -> Equation -> Equation
termMap f e = e{lhs = f (lhs e), rhs = f (rhs e)}

-- |Checks whether an equation fulfills the variable condition:
-- The right-hand side only uses free variables which are also present
-- in the left-hand side.
varCondition :: Equation -> Bool
varCondition e = freeVars (rhs e) `S.isSubsetOf` freeVars (lhs e)

-- |Checks whether the given equation fulfills the conditions to be a rule:
-- * both terms are of the same base type
-- * the left-hand side does not have a free variable as its head
-- * the variable condition holds
rule :: Equation -> Bool
rule e = (a == b) && sort a && not (isHeadedByFreeVar (lhs e)) && varCondition e where
  a = typ (lhs e)
  b = typ (rhs e)

-- |Checks whether the given equation fulfills the conditions to be a DHP rule:
-- * it is a valid rule
-- * the left-hand side is a DHP
dhpRule :: Equation -> Bool
dhpRule e = rule e && isDHP (lhs e)

-- |Tests whether two DHP rules are variants.
dhpRuleVariants :: Equation -> Equation -> Bool
dhpRuleVariants e1 e2
  | Just subst1 <- match (lhs e1) (lhs e2), Just subst2 <-match (lhs e2) (lhs e1) =
      apply subst1 (rhs e1) == (rhs e2) && apply subst2 (rhs e2) == (rhs e1)
  | otherwise = False

