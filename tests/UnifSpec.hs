{-# LANGUAGE OverloadedStrings #-}

module UnifSpec (unifSpecs) where

import Control.Monad.State (evalState)
import Control.Monad.Trans.Maybe (runMaybeT)
import Test.Hspec (Spec, describe, it, shouldBe)

import qualified Data.Map.Strict as M

import qualified Predefined.Sort as Sort
import qualified Predefined.Typ as Typ 
import qualified Predefined.DB as DB
import qualified Predefined.Var as Var
import qualified Predefined.Fun as Fun

import Utils.Type (Id(..),Var(..))
import Typ.Type (Typ(..))
import Term.Type (Term)
import Term.Ops (mkTerm)
import Subst.Type (Subst(..))
import Subst.Unif

x :: Var
x = Named . Id $ "x"

y :: Var
y = Named . Id $ "y"

z :: Var
z = Named . Id $ "z"

ts1 :: [Term]
ts1 =  [ mkTerm Fun.f Typ.a [ mkTerm DB.one Typ.a [] ]
       , mkTerm Fun.f Typ.a [ mkTerm DB.zero Typ.a [] ] 
       ]

t1 :: Term
t1 = mkTerm Var.x Typ.aaa ts1


t2 :: Term
t2 = mkTerm Fun.f Typ.aaa [ mkTerm Var.y Typ.a [ mkTerm DB.zero Typ.a []
                                               , mkTerm DB.one Typ.a []
                                               ] ]

spec_partialBinding :: Spec
spec_partialBinding =
  describe "partialBinding" $ do
    let a1 = Typ [Typ.a, Typ.aa] Sort.a
        bs1 = [Typ.aa, a1]
        create a h bs = evalState (partialBinding a h bs) 0
        res1 =  mkTerm Fun.f a1 [ mkTerm Var.fresh0 Typ.aa [ mkTerm DB.two Typ.a []
                                                           , mkTerm DB.two Typ.aa [ mkTerm DB.zero Typ.a [] ]
                                                           , mkTerm DB.zero Typ.a []
                                                           ]
                                , mkTerm Var.fresh1 a1 [ mkTerm DB.three Typ.a []
                                                       , mkTerm DB.three Typ.aa [ mkTerm DB.zero Typ.a [] ]
                                                       , mkTerm DB.one Typ.a []
                                                       , mkTerm DB.one Typ.aa [ mkTerm DB.zero Typ.a [] ]
                                                       ]
                                ]
    it "computes example correctly" $
      create a1 Fun.f bs1 `shouldBe` res1

spec_prj :: Spec
spec_prj =
  describe "prj" $ do
    let applyPrj v a i ss = evalState (prj v a i ss) 0
        ss1 = [ mkTerm DB.one Typ.aa [ mkTerm DB.zero Typ.a [] ]
              , mkTerm Fun.c Typ.a []
              ]
        a1 = Typ [Typ.aa, Typ.a] Sort.a
        res1 = [ Subst $ M.fromList [(x, mkTerm DB.one a1 [ mkTerm Var.fresh0 Typ.a [ mkTerm DB.two Typ.aa [ mkTerm DB.zero Typ.a [] ]
                                                                                    , mkTerm DB.zero Typ.a []
                                                                                    ] ] )] ]
    it "computes example correctly" $
      applyPrj x a1 0 ss1 `shouldBe` res1

spec_imtPrj :: Spec
spec_imtPrj =
  describe "imtPrj" $ do
    let applyImtPrj v a as f ss = evalState (imtPrj v a as f ss) 0
        res1 =
          [ Subst $ M.fromList [ (x, mkTerm Fun.f Typ.aaa [ mkTerm Var.fresh0 Typ.a [ mkTerm DB.one Typ.a []
                                                                                    , mkTerm DB.zero Typ.a []
                                                                                    ]
                                                          ]
                                 )
                               ]
          , Subst $ M.fromList [ (x, mkTerm DB.one Typ.aaa []) ]
          , Subst $ M.fromList [ (x, mkTerm DB.zero Typ.aaa []) ]
          ]
    it "computes example correctly" $
      applyImtPrj x Typ.aaa [Typ.a] (Id "f") ts1 `shouldBe` res1

spec_ffe :: Spec
spec_ffe =
  describe "ffe" $ do
    let applyFFE v a ss ts = evalState (ffe v a ss ts) 0
        a1 = Typ [Typ.aa, Typ.a] Sort.a
        ss1 = [ mkTerm Fun.c Typ.aa [ mkTerm DB.zero Typ.a [] ]
              , mkTerm DB.zero Typ.a []
              ]
        ss2 = [ mkTerm Fun.c Typ.aa [ mkTerm DB.one Typ.a [] ]
              , mkTerm DB.zero Typ.a []
              ]
        res1 = Subst $ M.fromList
          [ ( x
            , mkTerm Var.fresh0 a1 [ mkTerm DB.zero Typ.a [] ]
            )
          ] 
        res2 = Subst $ M.fromList
          [ ( x
            , mkTerm Var.fresh0 Typ.aaa []
            )
          ]
    it "filters out unequal arguments" $
      applyFFE (Named . Id $ "x") Sort.a ss1 ss2 `shouldBe` res1
    it "does not allow argument permutations" $
      applyFFE (Named . Id $ "x") Sort.a ts1 (reverse ts1) `shouldBe` res2

spec_ffn :: Spec
spec_ffn =
  describe "ffn" $ do
    let applyFFN v1 v2 k a ss ts = evalState (ffn v1 v2 k a ss ts) 0
        ss1 = [ mkTerm Fun.c Typ.a [ mkTerm DB.zero Typ.a [] ]
              , mkTerm Fun.d Typ.a [ mkTerm DB.zero Typ.a [] ]
              ]
        s2 = mkTerm Fun.c Typ.a [ mkTerm DB.zero Typ.a [] ]
        s2' = mkTerm Fun.c Typ.a [ mkTerm Fun.c Typ.a [ mkTerm DB.zero Typ.a [] ] ]
        s3 = mkTerm Fun.c Typ.a [ mkTerm DB.one Typ.a []
                                , mkTerm DB.zero Typ.a []
                                ]
        ss3' = [ mkTerm DB.zero Typ.a []
               , mkTerm DB.one Typ.a []
               ]
        s4 = mkTerm Fun.c Typ.a [ mkTerm DB.zero Typ.a []
                                , mkTerm DB.one Typ.a []
                                ]
        ss4' = [ mkTerm Fun.c Typ.aa [ mkTerm DB.one Typ.a []
                                     , mkTerm DB.zero Typ.a []
                                     ]
               , mkTerm DB.one Typ.a []
               ]
        a4 = Typ [Typ.aa, Typ.a] Sort.a
        s5 = mkTerm Fun.c Typ.a [ mkTerm DB.zero Typ.a [], mkTerm DB.one Typ.a [] ]
        s5' = mkTerm DB.zero Typ.a []
        ss6 = [ mkTerm Fun.g Typ.a [ mkTerm DB.one Typ.a [] ]
              , mkTerm DB.zero Typ.a []
              ]
        ss6' = [ mkTerm DB.one Typ.a []
               , mkTerm Fun.g Typ.a [ mkTerm DB.zero Typ.a [] ]
               ]
        res1 = Subst $ M.fromList
          [ ( x
            , mkTerm Var.fresh0 Typ.aaa [ mkTerm DB.one Typ.a []
                                        , mkTerm DB.zero Typ.a []
                                        ]
            )
          , ( y
            , mkTerm Var.fresh0 Typ.aaa [ mkTerm DB.zero Typ.a []
                                        , mkTerm DB.one Typ.a []
                                        ]
            )
          ]
        res2 = Subst $ M.fromList
          [ ( x
            , mkTerm Var.fresh0 Typ.aa [ mkTerm Fun.c Typ.a [ mkTerm DB.zero Typ.a [] ] ]
            )
          , ( y
            , mkTerm Var.fresh0 Typ.aa [ mkTerm DB.zero Typ.a [] ]
            )
          ]
        res3 = Subst $ M.fromList
          [ ( x
            , mkTerm Var.fresh0 Typ.aa [ mkTerm DB.zero Typ.a [] ]
            )
          , ( y
            , mkTerm Var.fresh0 Typ.aaa [ mkTerm Fun.c Typ.a [ mkTerm DB.zero Typ.a []
                                                             , mkTerm DB.one Typ.a []
                                                             ]
                                        ]
            )
          ]
        res4 = Subst $ M.fromList
          [ ( x
            , mkTerm Var.fresh0 Typ.aa [ mkTerm DB.zero Typ.a [] ]
            )
          , ( y
            , mkTerm Var.fresh0 a4 [ mkTerm DB.one Typ.a [ mkTerm DB.zero Typ.a [] ] ]
            )
          ]
        res5 = Subst $ M.fromList
          [ ( x
            , mkTerm Var.fresh0 Typ.aa []
            )
          , ( y
            , mkTerm Var.fresh0 Typ.aa []
            )
          ]
        res6 = Subst $ M.fromList
          [ ( x
            , mkTerm Var.fresh0 Typ.aaa [ mkTerm DB.one Typ.a []
                                        , mkTerm Fun.g Typ.a [ mkTerm DB.zero Typ.a [] ]
                                        ]
            )
          , ( y
            , mkTerm Var.fresh0 Typ.aaa [ mkTerm Fun.g Typ.a [ mkTerm DB.one Typ.a [] ]
                                        , mkTerm DB.zero Typ.a []
                                        ]
            )
          ]
    it "can permute arguments" $
      applyFFN x y 1 Sort.a ss1 (reverse ss1) `shouldBe` res1
    it "can extend arguments" $
      applyFFN x y 1 Sort.a [s2] [s2'] `shouldBe` res2
    it "can assemble arguments" $
      applyFFN x y 2 Sort.a [s3] ss3' `shouldBe` res3
    it "can assemble higher-order arguments" $
      applyFFN x y 2 Sort.a [s4] ss4' `shouldBe` res4
    it "removes non-buildable arguments" $
      applyFFN x y 2 Sort.a [s5] [s5'] `shouldBe` res5
    it "can mutually assemble arguments" $
      applyFFN x y 2 Sort.a ss6 ss6' `shouldBe` res6

spec_unif :: Spec
spec_unif =
  describe "unif" $ do
    let unify s t = evalState (runMaybeT $ unif s t) 0
        t3 = mkTerm Var.z Typ.aa [ mkTerm Fun.g Typ.a [ mkTerm DB.zero Typ.a [] ] ]
        t4 = mkTerm Fun.f Typ.a [ mkTerm Fun.g Typ.a [ mkTerm Var.x Typ.a [] ] ]
        t4' = mkTerm Fun.f Typ.aa [ mkTerm Fun.g Typ.a [ mkTerm Var.x Typ.a [ mkTerm DB.zero Typ.a [] ] ] ]
        t5 = mkTerm Fun.c Typ.aa [ mkTerm Var.x Typ.aa [ mkTerm DB.one Typ.a []
                                                       , mkTerm Fun.g Typ.a [ mkTerm DB.zero Typ.a [] ]
                                                       ] ] 
        t6 = mkTerm Var.y Typ.aa [ mkTerm Fun.g Typ.a [ mkTerm DB.zero Typ.a [] ] ]
        t7 = mkTerm Var.x Typ.a []
        t8 = mkTerm Fun.f Typ.a [ mkTerm Var.x Typ.a []]
        t9 = mkTerm Var.x Typ.aa [ mkTerm Fun.f Typ.a [ mkTerm Fun.f Typ.a [ mkTerm DB.zero Typ.a [] ] ] ]
        t10 = mkTerm Fun.f Typ.aa [ mkTerm Var.x Typ.a [ mkTerm Fun.f Typ.a [ mkTerm DB.zero Typ.a [] ] ] ]
        res1 = [ Subst $ M.fromList
                   [ ( x
                     , mkTerm Fun.f Typ.aaa [ mkTerm Var.fresh1 Typ.a [ mkTerm DB.one Typ.a []
                                                                      , mkTerm DB.zero Typ.a []
                                                                      ]
                                            ]
                     )
                   , ( y
                     , mkTerm Var.fresh1 Typ.aaa [ mkTerm Fun.f Typ.a [ mkTerm DB.zero Typ.a [] ]
                                                 , mkTerm Fun.f Typ.a [ mkTerm DB.one Typ.a [] ]
                                                 ]
                     )
                   ]
               , Subst $ M.fromList
                   [ ( x
                     , mkTerm DB.one Typ.aaa []
                     )
                   , ( y
                     , mkTerm DB.zero Typ.aaa []
                     )
                   ]
               , Subst $ M.fromList
                   [ ( x
                     , mkTerm DB.zero Typ.aaa []
                     )
                   , ( y
                     , mkTerm DB.one Typ.aaa []
                     )
                   ]
               ]
        res3 = [ Subst $ M.fromList
                   [ ( x
                     , mkTerm Var.fresh1 Typ.aa [ mkTerm Fun.g Typ.a [ mkTerm DB.zero Typ.a [] ] ] 
                     )
                   , ( z
                     , mkTerm Fun.f Typ.aa [ mkTerm Fun.g Typ.a [ mkTerm Var.fresh1 Typ.a [ mkTerm DB.zero Typ.a [] ] ] ]
                     )
                   ]
               , Subst $ M.fromList
                   [ ( x
                     , mkTerm DB.zero Typ.aa []
                     )
                   , ( z
                     , mkTerm Fun.f Typ.aa [ mkTerm DB.zero Typ.a [] ]
                     )
                   ]
               ]
        res4 = [ Subst $ M.fromList
                   [ ( x
                     , mkTerm Var.fresh1 Typ.aaa [ mkTerm Fun.g Typ.a [ mkTerm DB.one Typ.a [] ]
                                                 , mkTerm DB.zero Typ.a []
                                                 ]
                     )
                   , ( y
                     , mkTerm Fun.c Typ.aa [ mkTerm Var.fresh1 Typ.aa [ mkTerm DB.one Typ.a []
                                                                      , mkTerm Fun.g Typ.a [ mkTerm DB.zero Typ.a [] ]
                                                                      ]
                                           ]
                     )
                   ]
               ]
    it "can handle classic DHP non-unitary example" $
      unify t1 t2 `shouldBe` Just res1
    it "fails without lifter" $
      unify t3 t4 `shouldBe` Just []
    it "can handle variable overlap" $
      unify t3 t4' `shouldBe` Just res3
    it "can handle self-overlap" $
      unify t5 t6 `shouldBe` Just res4
    it "can handle recursively occuring variable" $
      unify t7 t8 `shouldBe` Just []
    it "can handle recursively occuring variable with args" $
      unify t9 t10 `shouldBe` Nothing

unifSpecs :: Spec
unifSpecs = describe "Subst.Unif" $ do
  spec_partialBinding
  spec_prj
  spec_imtPrj
  spec_ffe
  spec_ffn
  spec_unif
