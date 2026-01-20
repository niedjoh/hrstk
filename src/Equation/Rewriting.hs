{-# LANGUAGE OverloadedStrings #-}

-- |implementation of rewriting with DPRSs
module Equation.Rewriting where

import Data.List.NonEmpty (NonEmpty,(<|),singleton)
import qualified Data.List.NonEmpty as NEL
import Prettyprinter (Doc,vsep,pretty,line,align,(<+>))

import Utils.Pretty (prettySequence)
import Term.Type (Term(..),Subterm)
import Term.Ops (filteredSubterms,isFun)
import Equation.Type (ES,Equation(..))
import Subst.Ops (apply)
import Subst.Match (match)

-- |Computes the candidate subterms for root rewrite steps with necessary additional information.
rootReducibleSubterms :: Term -> [Subterm]
rootReducibleSubterms = filteredSubterms (isFun . hd)

-- |Given an equation and a term, this function tries to perform a
-- rewrite step wrt the equation at the root position of the term.
rootRewriteStep :: Equation -> Term -> Maybe Term
rootRewriteStep e s = do
  subst <- match (lhs e) s
  pure $ apply subst (rhs e)

-- |Computes the possible rewrite steps starting from
-- a term with respect to the given ES.
possibleSteps :: ES -> Term -> [Term]
possibleSteps es s =
  [ tctx t'
  | (tctx,_,_,t) <- rootReducibleSubterms s
  , e <- es
  , typ (lhs e) == typ t
  , Just t' <- [rootRewriteStep e t] ]

-- |Rewrites a given term to normal form with respect
-- to the given ES with an outermost strategy.
rewriteToNF :: ES -> Term -> Term
rewriteToNF es s = case possibleSteps es s of
  s':_ -> rewriteToNF es s'
  [] -> s

-- |Records the rewrite sequence to normal form starting from the
-- given term with respect to the given ES with an outermost strategy.
rewriteSequenceToNF :: ES -> Term -> NonEmpty Term
rewriteSequenceToNF es s = case possibleSteps es s of
  s':_ -> s <| rewriteSequenceToNF es s'
  [] -> singleton s

-- | Determines whether an equation is joinable. In our setting,
-- this simply means that both sides rewrite to the same normal form
-- (under some strategy which is fixed in rewriteToNF).
joinable :: ES -> Equation -> Bool
joinable es e = rewriteToNF es (lhs e) == rewriteToNF es (rhs e)

-- |Computes the joining sequence of an equation with respect to a given ES
-- by reducing both sides to normal form.
joiningSequence :: ES -> Equation -> (NonEmpty Term, NonEmpty Term)
joiningSequence es e = (rewriteSequenceToNF es (lhs e), rewriteSequenceToNF es (rhs e))

-- |Prettyprinter of joinability of conjectures given axioms
joinabilityDoc :: ES -> ES -> Doc a
joinabilityDoc es1 es2 = (vsep . map jd $ zip es2 [1 :: Int ..]) <> line <> line where
  jd (e,i) = let
    (ls,rs) = joiningSequence es1 e
    lNF = NEL.last ls
    rNF = NEL.last rs
    in line <> "#" <> pretty i <+> align (pretty e <> line <> line <>
          if lNF == rNF
          then "joinable" <> prettySequence ls <> prettySequence rs
          else "not joinable" <> prettySequence ls <> prettySequence rs)
