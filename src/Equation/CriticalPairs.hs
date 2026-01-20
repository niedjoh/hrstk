{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

-- |implementation of critical pairs for DPRSs
module Equation.CriticalPairs where

import Control.Monad.Trans.Maybe (MaybeT)
import qualified Data.Map.Strict as M
import Data.Maybe (isNothing)
import qualified Data.Set as S
import Prettyprinter (Doc,vsep,pretty,line,tupled)

import Utils.FreshMonad (MonadFresh,FreshM,freshVar)
import Utils.Pretty (prettyNList)
import Typ.Type (Typ)
import Typ.Ops (returnTyp,liftTyp)
import Term.Type (Term(..),Head(..),Context,Subterm)
import Term.Ops (freeVars,hdToTerm,isDBTerm,addLams,filteredSubterms,shiftDB)
import Subst.Ops (empty,singleton,apply,(!?))
import Subst.Match (match)
import Subst.Unif (unif)
import Equation.Type
import Equation.Ops (termMap,dhpRuleVariants)
import Equation.Rewriting (joinable,joinabilityDoc)

-- |Renames the free variables in the given rule (the variable condition is assumed) to fresh names
-- and lifts them to the bound variable context specified in the first argument
-- (Mayr & Nipkow 1998: "xk-lifter away")
renameAndLift :: MonadFresh m => [Typ] -> [Term] -> Equation -> m Equation
renameAndLift as ts e = do
  varMap <- M.fromAscList <$>
    traverse (\v -> freshVar >>= \w -> return (v,w)) (S.elems (freeVars (lhs e)))
  let  go d s@(Term {hd = FV v}) = case varMap M.!? v of
         Just w -> let d' = d + nlams s
                   in s{ hd = FV w
                       , sp = map (shiftDB d') ts ++ map (go d') (sp s)
                       }
         Nothing -> error "impossible case"
       go d s = s{sp = map (go (d + nlams s)) (sp s)}
  return . termMap (addLams as . go 0) $ e

-- |Computes all possible overlaps of the whole first term with the second term
overlaps :: Term -> Term -> [Subterm]
overlaps s = filteredSubterms p where
  p t@(Term {hd = F _}) = hd s == hd t
  p t@(Term {hd = FV _}) = not $ all isDBTerm (sp t) -- optimization to discard Miller's patterns immediately
  p _ = False

-- |Computes the critical pairs for a given position if unifiers exist.
criticalPairsFixedPos :: Equation -> (Context,[Typ],Term) -> Term -> MaybeT FreshM [Equation]
criticalPairsFixedPos e1 (l2pctx,bvctx,l2p) r2 = do
  let n = length bvctx
  e1r <- renameAndLift bvctx (zipWith (\i a -> hdToTerm a (DB i)) [n-1,n-2..0] bvctx) e1
  (l2p',l2pctx',gamma) <- case hd l2p of
    FV v -> do
      let as = map typ $ sp l2p
          m = length as
          dbs = zip [m-1,m-2..0] as
          dbTerms = map (\(i,c) -> hdToTerm c (DB i)) dbs
          b = returnTyp $ typ $ lhs $ e1r
          a = returnTyp $ typ $ l2p
      v' <- freshVar
      v'' <- freshVar
      return ( l2p{hd = FV v', typ = b}
             , \x -> l2pctx (Term { nlams = 0
                                  , hd = FV v''
                                  , sp = x{nlams = 0, typ = b} : sp l2p
                                  , typ = a
                                  }
                            )
             , singleton v (Term { nlams = length (sp l2p)
                                 , hd = FV v''
                                 , sp = Term { nlams = 0
                                             , hd = FV v'
                                             , sp = dbTerms
                                             , typ = b
                                             }
                                        : dbTerms
                                 , typ = liftTyp (map typ $ sp l2p) a
                                 }
                           )
             )
    _ -> return (l2p,l2pctx,empty)
  msubsts <- unif (lhs e1r) (addLams bvctx l2p')
  let filteredSubsts = case hd l2p' of
        FV v ->  filter (\s -> case s !? v of
                          Just t -> (not $ apply s l2p' `elem` (sp l2p')) &&
                                    (isNothing $ match (lhs e1) t{nlams=0})
                          Nothing -> error "impossible case"
                        )
                        msubsts
        _ -> msubsts
  return [ Equation { lhs = apply subst $ apply gamma $ l2pctx' $ rhs e1r
                    , rhs = apply subst $ apply gamma r2
                    , isRule = False}
         | subst <- filteredSubsts
         ]

-- |Computes the critical pairs between two DPRSs. Note that the definition of critical pairs
-- is not symmetric. In particular, the root step is always performed with rules from
-- the second DPRS.
criticalPairs :: ES -> ES -> MaybeT FreshM [CriticalPair]
criticalPairs es1 es2 = do
  cpss <- sequence
           [ map (, p, e1, e2) <$> criticalPairsFixedPos e1 (l2pctx,bvctx,l2p) (rhs e2)
           | e1 <- es1, e2 <- es2
           , (l2pctx,bvctx,p,l2p) <- overlaps (lhs e1) (lhs e2)
           , p /= [] || not (dhpRuleVariants e1 e2)
           ]
  return . concat $ cpss

-- |checks joinability of critical pairs (second argument) with respect to a DPRS (first argument)
checkJoinability :: ES -> [CriticalPair] -> Bool
checkJoinability dprs = all (joinable dprs . fst4) where
  fst4 (x,_,_,_) = x

-- |document describing the result of 'checkJoinability'
resultDoc :: ES -> [CriticalPair] -> Doc ann
resultDoc dprs cpairs = let
  in line <> "input DPRS:" <> line <> line <> vsep (map pretty dprs) <> line <>
  line <> "critical pairs:" <> line <>
  if null cpairs
    then "none" <> line <> line
    else line <>
         prettyNList
         (map (\(e,p,r1,r2) -> tupled [pretty r1, pretty p, pretty r2] <> line <> line <> pretty e <> line) cpairs) <>
         line <> line <> "naive joinability tests: " <> line <>
         joinabilityDoc dprs (map (\(e,_,_,_) -> e) cpairs)
