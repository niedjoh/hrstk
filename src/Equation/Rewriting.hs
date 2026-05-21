{-# LANGUAGE OverloadedStrings #-}

-- |implementation of rewriting with DPRSs
module Equation.Rewriting where

import Data.List (intersect)
import Data.List.Extra (nubOrdOn)
import Data.List.NonEmpty (NonEmpty,(<|),singleton)
import qualified Data.List.NonEmpty as NEL
import Prettyprinter (Doc,vsep,hcat,pretty,line,align,(<+>))

import Utils.Misc (allPossibilities)
import Utils.Pretty (prettySequence)
import Typ.Ops (returnTyp)
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

possibleRootMultiSteps :: ES -> Term -> [Term]
possibleRootMultiSteps es s = [apply subst (rhs e) | (Just subst,e) <- matches ] where
  matches = [ (msubst,e) | e <- es, let msubst = match (lhs e) s ]

possibleMultiSteps :: ES -> Term -> [Term]
possibleMultiSteps es s@(Term {nlams = 0}) = us ++ concatMap (possibleRootMultiSteps es) us where
  us = [ s{sp = ts}
       | ts <- allPossibilities $ map (possibleMultiSteps es) (sp s)
       ]
possibleMultiSteps es s = [ t{nlams = nlams s, typ = typ s}
                          | t <- possibleMultiSteps es s{nlams = 0, typ = returnTyp (typ s)}
                          ]

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

-- | Determines whether an equation is "multistep-joinable", i.e., development closed.
msJoinable :: ES -> Equation -> Bool
msJoinable es e = rhs e `elem` possibleMultiSteps es (lhs e)

-- |Prettyprinter of joinability of conjectures given axioms
joinabilityDoc :: ES -> ES -> Doc ann
joinabilityDoc es1 es2 = (vsep . map jd $ zip es2 [1 :: Int ..]) where
  jd (e,i) = let
    (lseqs,rseqs) = (nubOrdOn NEL.last $ rewriteSequencesToNF es1 (lhs e), nubOrdOn NEL.last $ rewriteSequencesToNF es1 (rhs e))
    in line <> "#" <> pretty i <+>
       align (pretty e <> line <> line <>
             case [(ls,rs) | ls <- lseqs, rs <- rseqs, NEL.last ls == NEL.last rs] of
               (lseq,rseq):_ -> "joinable" <> prettySequence lseq <> prettySequence rseq
               [] -> "not joinable" <> hcat (map prettySequence lseqs) <> hcat (map prettySequence rseqs)
             )

msJoinabilityDoc :: ES -> ES -> Doc ann
msJoinabilityDoc es1 es2 = (vsep . map jd $ zip es2 [1 :: Int ..]) where
  jd (e,i) = line <> "#" <> pretty i <+>
       align (pretty e <> line <> line <>
              (if rhs e `elem` possibleMultiSteps es1 (lhs e)
                 then "connected by right multistep"
                 else "not connected by right multistep"
              ))
