{-# LANGUAGE OverloadedStrings #-}

module TermOpsSpec (termOpsSpecs) where

import qualified Data.Map.Strict as M

import Test.Hspec (Spec, describe, it, shouldNotSatisfy, shouldSatisfy, shouldBe)

import qualified Predefined.Sort as Sort
import qualified Predefined.Typ as Typ 
import qualified Predefined.DB as DB
import qualified Predefined.Var as Var
import qualified Predefined.Fun as Fun

import Utils.Type (Id(..),Var(..))
import Typ.Type (Typ(..))
import Term.Type (Term(..))
import Term.Ops

spec_freeVarsTypMap :: Spec
spec_freeVarsTypMap =
  describe "freeVarsTypMap" $ do
    let t1 = mkTerm Var.z Typ.aa [ mkTerm DB.zero Typ.a []
                                 , mkTerm Fun.c Typ.aa [mkTerm DB.zero Typ.a []]
                                 , mkTerm Var.x Typ.a []
                                 ]
    it "computes an example correctly" $
      freeVarsTypMap t1 `shouldBe` M.fromList [ (Named . Id $ "x", Typ.a)
                                              , (Named . Id $ "z", Typ [Typ.a, Typ.aa, Typ.a] Sort.a)
                                              ]

spec_secondOrder :: Spec
spec_secondOrder =
  describe "secondOrder" $ do
    let t1 = mkTerm Fun.c Typ.a [ mkTerm Var.x Typ.a [] ]
        t2 = mkTerm Fun.c Typ.a [ mkTerm Var.x Typ.aa [] ]
        t3 = mkTerm Var.x Typ.a [ mkTerm Fun.c Typ.aa [] ]
    it "accepts first-order term" $
      t1 `shouldSatisfy` secondOrder
    it "accepts second-order term" $
      t2 `shouldSatisfy` secondOrder
    it "rejects third-order term" $
      t3 `shouldNotSatisfy` secondOrder

spec_linear :: Spec
spec_linear =
  describe "linear" $ do
    let t1 = mkTerm Fun.f Typ.a [ mkTerm Var.x Typ.a []
                                , mkTerm Var.y Typ.a []
                                ]
        t2 = mkTerm Fun.f Typ.a [ mkTerm Var.x Typ.a []
                                , mkTerm Fun.g Typ.a [ mkTerm Var.x Typ.a [] ]
                                ]
        t3 = mkTerm Fun.f Typ.a [ mkTerm Var.x Typ.aa [ mkTerm Var.x Typ.aa [ mkTerm Fun.c Typ.a [] ] ] ]
    it "accepts first-order term" $
      t1 `shouldSatisfy` linear
    it "rejects parallel counterexample" $
      t2 `shouldNotSatisfy` linear
    it "rejects nested counterexample" $
      t3 `shouldNotSatisfy` linear

spec_hdToTerm :: Spec
spec_hdToTerm =
  describe "hdToTerm" $ do
    let a1 = Typ.aaa
        a2 = Typ [Typ.a, Typ.b] Sort.a
        a3 = Typ [Typ.a, Typ.aa] Sort.a
    it "does not add lambdas to heads of sort type" $
      hdToTerm Typ.a Fun.c `shouldBe` mkTerm Fun.c Typ.a []
    it "computes first-order example correctly" $
      hdToTerm a1 Fun.c `shouldBe` mkTerm Fun.c a1 [ mkTerm DB.one Typ.a []
                                                   , mkTerm DB.zero Typ.a []
                                                   ]
    it "can handle different sorts" $
      hdToTerm a2 Var.x `shouldBe` mkTerm Var.x a2 [ mkTerm DB.one Typ.a []
                                                   , mkTerm DB.zero Typ.b []
                                                   ]
    it "computes second-order example correctly" $
      hdToTerm a3 Fun.c `shouldBe` mkTerm Fun.c a3 [ mkTerm DB.one Typ.a []
                                                   , mkTerm DB.one Typ.aa [ mkTerm DB.zero Typ.a [] ]
                                                   ]

spec_danglingDB :: Spec
spec_danglingDB =
  describe "danglingDB" $ do
    let t1 = mkTerm Fun.c Typ.aaa [ mkTerm DB.zero Typ.a []
                                  , mkTerm Fun.d Typ.aa [ mkTerm DB.zero Typ.a []
                                                        , mkTerm DB.two Typ.a []
                                                        ]
                                  , mkTerm DB.one Typ.a []
                                  ]
        t2 = mkTerm Fun.c Typ.aa [ mkTerm DB.zero Typ.a []
                                 , mkTerm Fun.d Typ.aa [ mkTerm DB.two Typ.a [] ]
                                 ]
    it "rejects terms without dangling DBs" $
      t1 `shouldNotSatisfy` danglingDB
    it "accepts terms with dangling DB" $
      t2 `shouldSatisfy` danglingDB

spec_shiftDB :: Spec
spec_shiftDB =
  describe "shiftDB" $ do
    let t1 = mkTerm Fun.c Typ.a [ mkTerm Var.x Typ.aa [ mkTerm DB.two Typ.a []
                                                      , mkTerm DB.zero Typ.a []]
                                , mkTerm DB.one Typ.a []
                                ]
        t2 = mkTerm Fun.c Typ.a [ mkTerm Var.x Typ.aa [ mkTerm DB.one Typ.a []
                                                      , mkTerm DB.zero Typ.a []]
                                , mkTerm DB.zero Typ.a []
                                ]
    it "computes an example correctly" $
      shiftDB (-1) t1 `shouldBe` t2

spec_expandedTerm :: Spec
spec_expandedTerm =
  describe "expandedTerm" $ do
  let a1 = (Typ [Typ.aa, Typ.a] Sort.a)
      t1 = mkTerm Fun.c a1  [ mkTerm DB.two Typ.aa [ mkTerm DB.zero Typ.a [] ]
                            , mkTerm DB.zero Typ.a []
                            ]
      t2 = mkTerm Fun.c Typ.a [ mkTerm Var.x Typ.a [] ]
      t3 = mkTerm Fun.c Typ.aaa [ mkTerm DB.zero Typ.a []
                                , mkTerm DB.one Typ.a []
                                ]
      t4 = mkTerm Fun.c Typ.aa [ mkTerm DB.zero Typ.a []
                               , mkTerm DB.one Typ.a []
                               ]
      t5 = mkTerm DB.zero Typ.aa []
  it "accepts eta-expansion at root" $
    t1 `shouldSatisfy` expandedTerm 
  it "accepts first-order term" $
    t2 `shouldSatisfy` expandedTerm 
  it "rejects when variables are shuffled" $
    t3 `shouldNotSatisfy` expandedTerm 
  it "rejects when variables are used" $
    t4 `shouldNotSatisfy` expandedTerm 
  it "rejects identity function" $
    t5 `shouldNotSatisfy` expandedTerm 

spec_expandedSubtermRelEq :: Spec
spec_expandedSubtermRelEq =
  describe "expandedSubtermRelEq" $ do
    let t1 = mkTerm DB.zero Typ.a []
        t2 = mkTerm DB.one Typ.a [] 
        t3 = mkTerm Fun.c Typ.aaa [t2, t1]
        t4 = mkTerm Var.x Typ.a []
        t5 = mkTerm Fun.c Typ.a [t1, t4]
        t6 = mkTerm Fun.c Typ.aa [t2, t1]
        t7 = mkTerm Fun.c Typ.aa [t4, t1]
        t8 = mkTerm Fun.c Typ.aa [ mkTerm DB.one Typ.a []
                                 , mkTerm DB.zero Typ.a []
                                 ]
        t9 = mkTerm DB.one Typ.a []
    it "accepts eta-expanded first argument of application" $
      (t5,t3) `shouldSatisfy` (uncurry expandedSubtermEqRel)
    it "accepts middle element of application" $  
      (t5,t1) `shouldSatisfy` (uncurry expandedSubtermEqRel)
    it "accepts last element of application" $
      (t5,t4) `shouldSatisfy` (uncurry expandedSubtermEqRel)
    it "accepts eta-expaned prefix of application" $
      (t5,t6) `shouldSatisfy` (uncurry expandedSubtermEqRel)
    it "rejects eta-expanded non-prefix" $
      (t5,t7) `shouldNotSatisfy` (uncurry expandedSubtermEqRel)
    it "rejects DB shifted subterms" $
      (t8,t9) `shouldNotSatisfy` (uncurry expandedSubtermEqRel)

spec_isPattern :: Spec
spec_isPattern =
  describe "isPattern" $ do
    let t1 = mkTerm Var.z Typ.aaa [ mkTerm DB.zero Typ.a []
                                  , mkTerm DB.one Typ.a []
                                  ]
        t2 = mkTerm Var.z Typ.aaa [ mkTerm DB.zero Typ.a []
                                  , mkTerm DB.zero Typ.a []
                                  ]
        t3 = mkTerm Var.z Typ.aaa [ mkTerm DB.one Typ.a []
                                  , mkTerm Fun.c Typ.a []
                                  ]
        t4 = mkTerm Var.z Typ.aaa [ mkTerm Fun.c Typ.a [ mkTerm DB.zero Typ.a []] ]
        t5 = mkTerm Var.z (Typ [Typ.aa,Typ.a] Sort.a)
               [ mkTerm DB.one Typ.aa [ mkTerm DB.zero Typ.a [] ]
               , mkTerm DB.one Typ.a []
               ]
    it "accepts second-order example" $
      t1 `shouldSatisfy` isPattern
    it "rejects duplicate arguments" $
      t2 `shouldNotSatisfy` isPattern
    it "rejects constant arguments" $
      t3 `shouldNotSatisfy` isPattern
    it "rejects proper DHPs" $
      t4 `shouldNotSatisfy` isPattern
    it "accepts third-order example" $
      t5 `shouldSatisfy` isPattern

spec_isDHP :: Spec
spec_isDHP =
  describe "isDHP" $ do
    let t1 = mkTerm Fun.c Typ.aa [ mkTerm DB.zero Typ.a [] ]
        t2 = mkTerm Var.z Typ.aa [ mkTerm Fun.c Typ.a [mkTerm DB.zero Typ.a []]
                                 , mkTerm Fun.d Typ.a [mkTerm DB.zero Typ.a []]
                                 ]
        t3 = mkTerm Var.z Typ.aa [ mkTerm DB.zero Typ.aa [] ]
        t4 = mkTerm Var.z Typ.a [ mkTerm Fun.c Typ.a [] ]
        t5 = mkTerm Var.z Typ.aa [ mkTerm DB.one Typ.aa [mkTerm DB.zero Typ.a []] ]
        t6 = mkTerm Var.z Typ.aa [ mkTerm Var.z Typ.a [mkTerm DB.zero Typ.a []] ]
        t7 = mkTerm Fun.c Typ.aa [ mkTerm Var.x Typ.a [mkTerm DB.zero Typ.a []]
                                 , mkTerm Var.y Typ.a [mkTerm DB.zero Typ.a []]
                                 ]
        t8 = mkTerm Var.z Typ.aa [ mkTerm Fun.c Typ.a [mkTerm DB.zero Typ.a []]
                                 , mkTerm DB.zero Typ.a []
                                 ]
        t9 = mkTerm Var.z (Typ [Typ.aa, Typ.a] Sort.a) [ mkTerm Fun.c Typ.aa [ mkTerm DB.one Typ.a []
                                                                             , mkTerm DB.zero Typ.a []
                                                                             ]
                                                       , mkTerm DB.one Typ.a []
                                                       ]
        t10 = mkTerm Var.z Typ.a [ mkTerm Fun.c Typ.aa [ mkTerm DB.zero Typ.a [] ] ]
    it "accepts terms without free variables" $
      t1 `shouldSatisfy` isDHP
    it "accepts two different subterms" $
      t2 `shouldSatisfy` isDHP
    it "rejects real lambda abstraction arguments" $
      t3 `shouldNotSatisfy` isDHP
    it "rejects constant argument" $
      t4 `shouldNotSatisfy` isDHP
    it "accepts eta-expanded non-abstraction arguments" $
      t5 `shouldSatisfy` isDHP
    it "rejects nested free variables" $
      t6 `shouldNotSatisfy` isDHP
    it "accepts patterns occuring in parallel" $
      t7 `shouldSatisfy` isDHP
    it "rejects terms which do not satisfy local condition" $
      t8 `shouldNotSatisfy` isDHP
    it "can handle DB shifting in local condition" $
      t9 `shouldSatisfy` isDHP
    it "rejects non-expanded terms" $
      t10 `shouldNotSatisfy` isDHP

spec_filteredSubterms :: Spec
spec_filteredSubterms =
  describe "filteredSubterms" $ do
    let t1 = mkTerm Var.x Typ.aaa [ mkTerm DB.zero Typ.bb []
                                  , mkTerm Fun.c Typ.a [ mkTerm DB.zero Typ.a []
                                                       , mkTerm DB.one Typ.a []
                                                       ]
                                  ]
        f (ctx,as,p,subt) = (ctx subt, subt, as, p)
        res = map f $ filteredSubterms ((== Typ.b) . typ) t1
    it "computes example correctly" $
       res `shouldBe` [(t1, mkTerm DB.zero Typ.b [], [Typ.a,Typ.a,Typ.b],[1])]
       
termOpsSpecs :: Spec
termOpsSpecs = describe "Term.Ops" $ do
  spec_freeVarsTypMap
  spec_secondOrder
  spec_linear
  spec_hdToTerm
  spec_danglingDB
  spec_shiftDB
  spec_expandedTerm
  spec_expandedSubtermRelEq
  spec_isPattern
  spec_isDHP
  spec_filteredSubterms
