{-# LANGUAGE OverloadedStrings #-}

-- |implementation of rewriting with DPRSs
module Equation.Rewriting where

import Data.List (intersect)
import Data.List.NonEmpty (NonEmpty,(<|),singleton)
import qualified Data.List.NonEmpty as NEL
import Prettyprinter (Doc,vsep,hcat,pretty,line,align,(<+>))

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

-- |Rewrites a given term to its normal forms with respect
-- to the given ES
rewriteToNFs :: ES -> Term -> [Term]
rewriteToNFs es s = case possibleSteps es s of
  [] -> [s]
  ts -> [u | t <- ts, u <- rewriteToNFs es t]

-- |Records the rewrite sequence to normal form starting from the
-- given term with respect to the given ES with an outermost strategy.
rewriteSequencesToNF :: ES -> Term -> [NonEmpty Term]
rewriteSequencesToNF es s = case possibleSteps es s of
  [] -> [singleton s]
  ts -> [s <| us | t <- ts, us <- rewriteSequencesToNF es t]

-- | Determines whether an equation is joinable. In our setting,
-- this simply means that both sides rewrite to the same normal form
-- (under some strategy which is fixed in rewriteToNF).
joinable :: ES -> Equation -> Bool
joinable es e = not . null $ intersect (rewriteToNFs es (lhs e)) (rewriteToNFs es (rhs e))

-- |Prettyprinter of joinability of conjectures given axioms
joinabilityDoc :: ES -> ES -> Doc a
joinabilityDoc es1 es2 = (vsep . map jd $ zip es2 [1 :: Int ..]) <> line <> line where
  jd (e,i) = let
    (lseqs,rseqs) = (rewriteSequencesToNF es1 (lhs e), rewriteSequencesToNF es1 (rhs e))
    in line <> "#" <> pretty i <+>
       align (pretty e <> line <> line <>
             case [(ls,rs) | ls <- lseqs, rs <- rseqs, NEL.last ls == NEL.last rs] of
               (lseq,rseq):_ -> "joinable" <> prettySequence lseq <> prettySequence rseq
               [] -> "not joinable" <> hcat (map prettySequence lseqs) <> hcat (map prettySequence rseqs)
             )
