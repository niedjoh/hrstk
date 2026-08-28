{-# LANGUAGE OverloadedStrings #-}

module StarCPOSpec (scpoSpecs) where

import Test.Hspec (Spec, describe, it, shouldBe)

import qualified Predefined.Sort as Sort
import qualified Predefined.Typ as Typ 
import qualified Predefined.DB as DB
import qualified Predefined.Var as Var
import qualified Predefined.Fun as Fun

import Typ.Type (Typ(..))
import Term.Ops (mkTerm)
import Termination.StarCPO.Ordering

spec_adjustType :: Spec
spec_adjustType =
  describe "adjustType" $ do
    let s1 = mkTerm Fun.f Typ.a [ mkTerm DB.one Typ.aa []
                                , mkTerm Fun.g Typ.a [ mkTerm DB.zero Typ.a [] ]
                                ]
        a1 = Typ [Typ.aa, Typ.a] Sort.a
        t1 = mkTerm Fun.f a1 [ mkTerm DB.three Typ.aa []
                             , mkTerm Fun.g Typ.a [ mkTerm DB.two Typ.a [] ]
                             , mkTerm DB.two Typ.aa [ mkTerm DB.zero Typ.a [] ]
                             , mkTerm DB.zero Typ.a []
                             ]
    it "computes an example correctly" $
      adjustType s1 a1 `shouldBe` t1

spec_pullDown :: Spec
spec_pullDown =
  describe "pullDown" $ do
    let a1 = Typ [Typ.a, Typ.aa] Sort.a
        b1 = Typ [Typ.aa, Typ.a] Sort.a
        u1 = mkTerm Fun.g a1 [ mkTerm DB.three Typ.a [ mkTerm DB.one Typ.a [] ]
                             , mkTerm DB.zero Typ.a [ mkTerm DB.two Typ.a [] ]
                             , mkTerm Var.x Typ.a []
                             ]
        s1 a = mkTerm Fun.f a [ mkTerm Fun.g Typ.a [ mkTerm Var.x Typ.a [] ] ]
        t1 = mkTerm Fun.g b1 [ mkTerm DB.one Typ.a [ s1 Typ.a ]
                             , mkTerm Fun.f Typ.a [ mkTerm Fun.g Typ.a [ mkTerm Var.x Typ.a [] ]
                                                  , mkTerm DB.zero Typ.a []
                                                  ]
                             , mkTerm Var.x Typ.a []
                             ]
    it "computes an example correctly" $
      pullDown u1 (s1 b1) `shouldBe` t1

spec_extend :: Spec
spec_extend =
  describe "extend" $ do
    let a1 = Typ [Typ.a, Typ.aa] Sort.a
        b1 = Typ [Typ.a, Typ.aa, Typ.a, Typ.aa] Sort.a
        s1 = mkTerm Fun.f a1 [ mkTerm DB.two Typ.aa []
                             , mkTerm DB.zero Typ.a [ mkTerm Fun.h Typ.a [] ]
                             ]
        t1 = mkTerm Fun.f b1 [ mkTerm DB.four Typ.aa []
                             , mkTerm DB.two Typ.a [ mkTerm Fun.h Typ.a [] ]
                             , mkTerm DB.one Typ.a []
                             , mkTerm DB.one Typ.aa [ mkTerm DB.zero Typ.a [] ]
                             ]
    it "computes an example correclty" $
      extend s1 b1 `shouldBe` t1

scpoSpecs :: Spec
scpoSpecs = describe "Termination.StarCPO.Ordering" $ do
  spec_adjustType
  spec_pullDown
  spec_extend
