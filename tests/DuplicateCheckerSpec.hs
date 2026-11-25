{-# LANGUAGE OverloadedStrings #-}

module DuplicateCheckerSpec (duplicateCheckerSpecs) where

import qualified Data.Map.Strict as M

import Test.Hspec (Spec, describe, it, shouldBe)

import qualified Predefined.Typ as Typ

import Utils.Type (Id(..))
import DuplicateChecker (toTypSkeletonFunsMap)

spec_toTypSkeletonFunsMap :: Spec
spec_toTypSkeletonFunsMap =
  describe "toTypSkeletonFunsMap" $ do
    let fId = Id "f"
        gId = Id "g"
        hId = Id "h"

        fTyM = M.fromList [(fId,Typ.aCaaToa),(gId,Typ.ab),(hId,Typ.bCbbTob)]
        tsfM = M.fromList [(Typ.uu, [gId]),(Typ.uCuuTou, [hId, fId])]
    it "merges symbols correctly" $
      toTypSkeletonFunsMap fTyM `shouldBe` tsfM

duplicateCheckerSpecs :: Spec
duplicateCheckerSpecs = describe "toTypeSkeletonFunsMap" $ do
  spec_toTypSkeletonFunsMap
