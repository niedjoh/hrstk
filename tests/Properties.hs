{-# LANGUAGE OverloadedStrings #-}

module Properties where

import Control.Monad.State (evalState)
import Control.Monad.Trans.Maybe (runMaybeT)
import qualified Data.Map.Strict as M
import Hedgehog (Property, (===), (/==), label, property, eval, forAllWith, assert, annotate)

import Data.Foldable (traverse_)
import Prettyprinter (pretty)
import Test.Tasty.Hedgehog (testProperty)
import Test.Tasty.Providers (TestTree)

import Typ.Ops (returnSort)
import Term.Ops (isDHP, freeVarsTypMap)
import Subst.Ops (apply)
import Subst.Match (match)
import Subst.Unif (unif)
import Gen (typClosure, availMap, genTyp,  genDHP, genArbitraryTerm, genTermPair, genSubst)

-- all properties

props :: [TestTree] 
props = [ testProperty "DHP generator yields DHPs" prop_genDHP_DHP
        , testProperty "unification produces unifier" prop_unif
        , testProperty "matching produces matching substitution" prop_match
        ]

-- properties of generators

prop_genDHP_DHP :: Property
prop_genDHP_DHP = property $ do
  a <- forAllWith (show . pretty) genTyp
  let as = typClosure a
  let availM = availMap as
  let gen = genDHP as availM (returnSort a)
  s <- forAllWith (show . pretty) gen
  assert $ isDHP s

-- unification / matching produce substitutions which solve the problem

prop_unif :: Property
prop_unif = property $ do
  a <- forAllWith (show . pretty) genTyp
  let as = typClosure a
  let availM = availMap as
  let gen = genTermPair as availM genDHP genDHP (returnSort a)
  (s,t) <- forAllWith (show . pretty) gen
  msubsts <- eval $ evalState (runMaybeT $ unif s t) 0
  case msubsts of
    Nothing -> do
      label "unifiable, MCSU not computed"
    Just [] ->  do
      label "not unifiable"
      let test = genSubst availM $ freeVarsTypMap s `M.union` freeVarsTypMap t
      subst <- forAllWith (show . pretty) test
      apply subst s /== apply subst t
    Just substs ->
      do
      label "unifiable"
      annotate (show $ pretty substs)
      traverse_ (\subst -> apply subst s === apply subst t) substs

prop_match :: Property
prop_match = property $ do
  a <- forAllWith (show . pretty) genTyp
  let as = typClosure a
  let availM = availMap as
  let gen = genTermPair as availM genDHP genArbitraryTerm (returnSort a)
  (s,t) <- forAllWith (show . pretty) gen
  msubst <- eval $ match s t
  case msubst of
    Just subst -> do
      label "match"
      annotate (show $ pretty subst)
      apply subst s === t
    _ -> do
      label "no match"
      let test = genSubst availM $ freeVarsTypMap s `M.union` freeVarsTypMap t
      subst <- forAllWith (show . pretty) test
      apply subst s /== t
