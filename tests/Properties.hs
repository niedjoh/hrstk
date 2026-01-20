{-# LANGUAGE OverloadedStrings #-}

module Properties where

import Control.Monad.State (evalState)
import Control.Monad.Trans.Maybe (runMaybeT)
import qualified Data.Map.Strict as M
import Hedgehog (Property, (===), (/==), label, property, eval, forAllWith, assert, annotate, success)

import Data.Foldable (traverse_)
import Data.Tuple.Extra (fst3)
import Hedgehog (Size)
import qualified Hedgehog.Gen as Gen
import Prettyprinter (pretty)
import Test.Tasty.Hedgehog (testProperty)
import Test.Tasty.Providers (TestTree)

import Term.Ops (isDHP, freeVarsTypMap)
import Subst.Ops (apply)
import Subst.Match (match)
import Subst.Unif (unif)
import Gen (runGenM, runGenMWith, genTyp, genAlmostDHP, genDHP, genDHPPair, genDHPAndTerm, genSubst)

-- all properties

genSize :: Size
genSize = 50

props :: [TestTree] 
props = [ testProperty "almostDHP generator yields DHPs" prop_genAlmostDHP_DHP
        , testProperty "DHP generator yields DHPs" prop_genDHP_DHP
        , testProperty "unification produces unifier" prop_unif
        , testProperty "matching produces matching substitution" prop_match
        ]

-- properties of generators

prop_genAlmostDHP_DHP :: Property
prop_genAlmostDHP_DHP = property $ do
  a <- forAllWith (show . pretty) genTyp
  let gen = runGenM $ Gen.resize genSize $ genAlmostDHP M.empty a
  (s,_,_) <- forAllWith (show . pretty . fst3) gen
  case isDHP s of
    True -> do
      label "DHP"
      success
    False -> do
      label "non-DHP"
      success

prop_genDHP_DHP :: Property
prop_genDHP_DHP = property $ do
  a <- forAllWith (show . pretty) genTyp
  let gen = runGenM $ Gen.resize genSize $ genDHP a
  (s,_,_) <- forAllWith (show . pretty . fst3) gen
  assert $ isDHP s

-- unification / matching produce substitutions which solve the problem

prop_unif :: Property
prop_unif = property $ do
  a <- forAllWith (show . pretty) genTyp
  let gen = runGenM $ Gen.resize genSize $ genDHPPair a
  ((s,t),availMap,i) <- forAllWith (show . pretty . fst3) gen
  msubsts <- eval $ evalState (runMaybeT $ unif s t) 0
  case msubsts of
    Nothing -> do
      label "unifiable, MCSU not computed"
    Just [] ->  do
      label "not unifiable"
      let test = runGenMWith availMap i (Gen.resize genSize $ genSubst $ freeVarsTypMap s `M.union` freeVarsTypMap t)
      (subst,_,_) <- forAllWith (show . pretty . fst3) test
      apply subst s /== apply subst t
    Just substs ->
      do
      label "unifiable"
      annotate (show $ pretty substs)
      traverse_ (\subst -> apply subst s === apply subst t) substs

prop_match :: Property
prop_match = property $ do
  a <- forAllWith (show . pretty) genTyp
  let gen = runGenM $ Gen.resize genSize $ genDHPAndTerm a
  ((s,t),availMap,i) <- forAllWith (show . pretty . fst3) gen
  msubst <- eval $ match s t
  case msubst of
    Just subst -> do
      label "match"
      success
      apply subst s === t
    _ -> do
      label "no match"
      success
      let test = runGenMWith availMap i (Gen.resize genSize $ genSubst $ freeVarsTypMap s `M.union` freeVarsTypMap t)
      (subst,_,_) <- forAllWith (show . pretty . fst3) test
      apply subst s /== t
