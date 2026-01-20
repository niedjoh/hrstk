{-# LANGUAGE OverloadedStrings #-}

module TypOpsSpec (typOpsSpecs) where

import Test.Hspec (Spec, describe, it, shouldBe)

import qualified Data.Set as S

import qualified Predefined.Sort as Sort
import qualified Predefined.Typ as Typ

import Typ.Type (Typ(..))

import Typ.Ops

spec_order :: Spec
spec_order =
  describe "order" $ do
    let a1 = Typ [] Sort.b
        a2 = Typ [Typ.a, Typ.b] Sort.a
        a3 = Typ [Typ [Typ.a] Sort.a, Typ.a] Sort.a
        a4 = Typ [Typ.b, Typ [Typ [Typ.b] Sort.b] Sort.b] Sort.b
    it "recognizes order 1" $
      order a1 `shouldBe` 1
    it "recognizes order 2" $
      order a2 `shouldBe` 2
    it "recognizes order 3" $
      order a3 `shouldBe` 3
    it "recognizes order 4" $
      order a4 `shouldBe` 4
  
spec_applyTyps :: Spec
spec_applyTyps =
  describe "applyTyps" $ do
    let a1 = Typ [Typ.b] Sort.a
        a2 = Typ [Typ.a, a1] Sort.b
    it "computes example correctly" $
      applyTyps a2 [Typ.a] `shouldBe` Just (Typ [a1] Sort.b)
    it "fails appropriately on an example" $
      applyTyps a2 [Typ.b] `shouldBe` Nothing
    it "computes another example correctly" $
      applyTyps a2 [Typ.a, a1] `shouldBe` Just Typ.b

spec_equatableByTypApp :: Spec
spec_equatableByTypApp =
  describe "equatableByTypApp" $ do
    let a1 = Typ [Typ.a] Sort.b
        a2 = Typ [Typ.b, Typ.a] Sort.b
        a3 = Typ [Typ [Typ.a] Sort.a, Typ.b, Typ.a] Sort.b
    it "computes example correctly" $
      equatableByTypApp a1 a2 `shouldBe` Just [Typ.b]
    it "is not symmetric" $
      equatableByTypApp a2 a1 `shouldBe` Nothing
    it "computes another example correctly" $
      equatableByTypApp a1 a3 `shouldBe` Just [Typ [Typ.a] Sort.a, Typ.b]

spec_pos :: Spec
spec_pos =
  describe "pos" $ do
    let a1 = Typ [Typ [Typ.a] Sort.a, Typ.a] Sort.a
    it "computes example correctly" $
      pos a1 `shouldBe` S.fromList [[1,1],[1,2],[2],[3]]


spec_posOf :: Spec
spec_posOf =
  describe "posOf" $ do
    let a1 = Typ [Typ [Typ.a] Sort.b, Typ.a] Sort.b
    it "computes example correctly" $
      posOf Sort.a a1 `shouldBe` S.fromList [[1,1],[2]]
    it "computes example correctly" $
      posOf Sort.b a1 `shouldBe` S.fromList [[1,2],[3]]

spec_posPos :: Spec
spec_posPos =
  describe "posPos" $ do
    let a1 = Typ [Typ [Typ.a] Sort.a, Typ.a] Sort.a
    it "computes example correctly" $
      posPos a1 `shouldBe` S.fromList [[1,1],[3]]

spec_posNeg :: Spec
spec_posNeg =
  describe "posNeg" $ do
    let a1 = Typ [Typ [Typ.a] Sort.a, Typ.a] Sort.a
    it "computes example correctly" $
      posNeg a1 `shouldBe` S.fromList [[1,2],[2]]

typOpsSpecs :: Spec
typOpsSpecs = describe "Typ.Ops" $ do
  spec_order
  spec_applyTyps
  spec_equatableByTypApp
  spec_pos
  spec_posOf
  spec_posPos
  spec_posNeg
