{-# LANGUAGE OverloadedStrings #-}

module SubstOpsSpec (substOpsSpecs) where

import qualified Data.Map.Strict as M

import Test.Hspec (Spec, describe, it, shouldBe)

import qualified Predefined.Sort as Sort
import qualified Predefined.Typ as Typ 
import qualified Predefined.DB as DB
import qualified Predefined.Var as Var
import qualified Predefined.Fun as Fun

import Utils.Type (Id(..),Var(..))
import Typ.Type (Typ(..))
import Term.Ops (mkTerm)
import Subst.Type (Subst(..))
import Subst.Ops

x :: Var
x = Named . Id $ "x"

y :: Var
y = Named . Id $ "y"

z :: Var
z = Named . Id $ "z"

spec_dbMap :: Spec
spec_dbMap =
  describe "dbMap" $ do
    let ts = [ mkTerm Fun.c Typ.a [], mkTerm Var.x Typ.a [], mkTerm DB.zero Typ.aa [] ]
    it "computes an example correctly" $
      dbMap ts `shouldBe` M.fromList [ (2, mkTerm Fun.c Typ.a [])
                                     , (1, mkTerm Var.x Typ.a [])
                                     , (0, mkTerm DB.zero Typ.aa [])
                                     ]

spec_applyDBMap :: Spec
spec_applyDBMap =
  describe "applyDBMap" $ do
    let m1 = M.fromList [ (0, mkTerm Fun.f Typ.aa [ mkTerm Var.x Typ.a []
                                                  , mkTerm DB.zero Typ.a []
                                                  ])
                        , (1, mkTerm Fun.g Typ.aa [ mkTerm DB.zero Typ.a []
                                                  , mkTerm Var.y Typ.a []
                                                  ])
                        ]
        t1 = mkTerm Fun.h Typ.aa [ mkTerm DB.one Typ.a [ mkTerm Fun.c Typ.a [] ]
                                 , mkTerm DB.two Typ.a [ mkTerm Fun.d Typ.a [] ]
                                 , mkTerm DB.zero Typ.a []
                                 ]
        t1' = mkTerm Fun.h Typ.aa [ mkTerm Fun.f Typ.a [ mkTerm Var.x Typ.a []
                                                       , mkTerm Fun.c Typ.a []
                                                       ]
                                  , mkTerm Fun.g Typ.a [ mkTerm Fun.d Typ.a []
                                                       , mkTerm Var.y Typ.a []
                                                       ]
                                  , mkTerm DB.zero Typ.a []
                                  ]
    it "computes an example correctly" $
      applyDBMap 0 m1 t1 `shouldBe` t1'

spec_apply :: Spec
spec_apply =
  describe "apply" $ do
    let s1 = Subst $ M.fromList [ ( x
                                  , mkTerm DB.one (Typ [Typ.aa, Typ.a] Sort.a)
                                      [mkTerm DB.zero Typ.a []]
                                  )
                                , ( y
                                  , mkTerm Fun.g Typ.aa [ mkTerm DB.zero Typ.a []
                                                        , mkTerm Fun.d Typ.a []
                                                        ]
                                  )
                                ]
        t1 = mkTerm Fun.f Typ.a [ mkTerm Var.x Typ.a [ mkTerm Var.y Typ.aa [ mkTerm DB.zero Typ.a []]
                                                     , mkTerm Fun.c Typ.a [] ] ]
        t1' = mkTerm Fun.f Typ.a [ mkTerm Fun.g Typ.a [ mkTerm Fun.c Typ.a []
                                                      , mkTerm Fun.d Typ.a []
                                                      ] ]
        a2 = Typ [Typ.aa] Sort.a
        s2 = Subst $ M.fromList $
          [ ( x
            , mkTerm DB.zero a2 [ mkTerm Fun.c Typ.a [] ]
            )
          ]
        t2 = mkTerm Var.x a2 [ mkTerm DB.one Typ.aa [ mkTerm DB.zero Typ.a [] ] ]
        t2' = mkTerm DB.zero a2 [ mkTerm Fun.c Typ.a [] ]
        t3 = mkTerm Var.x Typ.b []
        t3' = mkTerm Fun.f Typ.b [ mkTerm Var.y Typ.ab [ mkTerm DB.one Typ.aa [] ] ]
        s3 = Subst . M.fromList $
          [ ( x
            , t3'
            )
          ]
        t4 = mkTerm Fun.f Typ.a [ mkTerm Fun.g Typ.ba [ mkTerm DB.zero Typ.b [] ]
                                , mkTerm Fun.h Typ.bb [ mkTerm Var.x Typ.abb [ mkTerm DB.one Typ.a []
                                                                             , mkTerm DB.zero Typ.b []
                                                                             ]
                                                      , mkTerm Var.y Typ.b []
                                                      , mkTerm DB.zero Typ.b []
                                                      ]
                                , mkTerm Var.z Typ.b []
                                ]
        t4' = mkTerm Fun.f Typ.a [ mkTerm Fun.g Typ.ba [ mkTerm DB.zero Typ.b [] ]
                                 , mkTerm Fun.h Typ.bb [ mkTerm (Var.fresh 32) Typ.abb [ mkTerm DB.four Typ.a []
                                                                                       , mkTerm DB.three Typ.a []
                                                                                       , mkTerm DB.one Typ.a []
                                                                                       , mkTerm DB.zero Typ.b []
                                                                                       ]
                                                       , mkTerm (Var.fresh 33) Typ.b [ mkTerm DB.two Typ.a []
                                                                                     , mkTerm DB.one Typ.a []
                                                                                     ]
                                                       , mkTerm DB.zero Typ.b []
                                                       ]
                                , mkTerm (Var.fresh 31) Typ.b [ mkTerm DB.one Typ.a []
                                                              , mkTerm DB.zero Typ.a []
                                                              ]
                                ]
        s4 = Subst . M.fromList $
         [ ( x
            , mkTerm (Var.fresh 32) Typ.abb [ mkTerm DB.three Typ.a []
                                            , mkTerm DB.two Typ.a []
                                            , mkTerm DB.one Typ.a []
                                            , mkTerm DB.zero Typ.b []
                                            ]
            )
          , ( y
            , mkTerm (Var.fresh 33) Typ.b [ mkTerm DB.one Typ.a []
                                          , mkTerm DB.zero Typ.a []
                                          ]
            )
          , ( z
            , mkTerm (Var.fresh 31) Typ.b [ mkTerm DB.one Typ.a []
                                          , mkTerm DB.zero Typ.a []
                                          ]
            )
          ]
    it "computes an example correctly" $
      apply s1 t1 `shouldBe` t1'
    it "shifts DBs of eta-expanded arguments" $
      apply s2 t2 `shouldBe` t2'
    it "does not shift DBs if abstractions stay" $
      apply s3 t3 `shouldBe` t3'
    it "normalizes DBs correctly" $
      apply s4 t4 `shouldBe` t4'
      

spec_compose :: Spec
spec_compose =
  describe "compose" $ do
    let ym = (y, mkTerm Fun.g Typ.aa [ mkTerm DB.zero Typ.a []] )
        s1 = Subst $ M.fromList [ ym , (x, mkTerm DB.zero Typ.aa []) ]
        s2 = Subst $ M.fromList [ ( x
                                  , mkTerm Fun.f Typ.aa [ mkTerm Var.y Typ.a [ mkTerm Fun.c Typ.a [] ]
                                                        , mkTerm DB.zero Typ.a []
                                                        ]
                                  )
                                ]
        s3 = Subst $ M.fromList [ ( x
                                  , mkTerm Fun.f Typ.aa [ mkTerm Fun.g Typ.a [ mkTerm Fun.c Typ.a [] ]
                                                        , mkTerm DB.zero Typ.a []
                                                        ]
                                  )
                                , ym
                                ]
    it "computes an exampe correctly" $
      compose s1 s2 `shouldBe` s3

spec_applyAbsToVar :: Spec
spec_applyAbsToVar =
  describe "applyAbsToVar" $ do
    let t1 = mkTerm Fun.c Typ.aaa [mkTerm DB.one Typ.a [], mkTerm DB.zero Typ.a []]
        t1' = mkTerm Fun.c Typ.aa [mkTerm Var.z Typ.a [], mkTerm DB.zero Typ.a []]
        t2 = mkTerm Fun.c Typ.aa [mkTerm DB.zero Typ.a []]
        t2' = mkTerm Fun.c Typ.a [mkTerm Var.z Typ.a []]
    it "computes an example correctly" $
      applyAbsToVar t1 (Named . Id $ "z")  `shouldBe` t1'
    it "removes final abstraction" $
      applyAbsToVar t2 (Named . Id $ "z") `shouldBe` t2'

spec_applyAbsToTerms :: Spec
spec_applyAbsToTerms =
  describe "applyAbsToTerms" $ do
    let t1 = mkTerm DB.one (Typ [Typ.aa, Typ.a] Sort.a) [ mkTerm DB.zero Typ.a [] ]
        t2 = mkTerm DB.zero Typ.aa []
        t3 = mkTerm Fun.c Typ.a []
    it "computes positive example correctly" $
      applyAbsToTerms t1 [t2,t3] `shouldBe` Just t3
    it "computes negative example correctly" $
      applyAbsToTerms t1 [t2,t3,t3] `shouldBe` Nothing
    it "can handle partial application" $
      applyAbsToTerms t1 [t2] `shouldBe` (Just $  mkTerm DB.zero Typ.aa [])

spec_discharge :: Spec
spec_discharge =
  describe "discharge" $ do
  let tis = [ (mkTerm Fun.g Typ.aa [ mkTerm DB.one Typ.a [], mkTerm DB.zero Typ.a [] ], 1)
            , (mkTerm Fun.h Typ.a [ mkTerm DB.zero Typ.a [] ], 0)
            ]
      t1 = mkTerm Fun.f Typ.a [ mkTerm Fun.g Typ.aa [ mkTerm DB.one Typ.a []
                                                     , mkTerm DB.zero Typ.a []
                                                     ]
                               , mkTerm Fun.h Typ.a [ mkTerm DB.zero Typ.a [] ]
                               ]
      t1' = mkTerm Fun.f Typ.a [ mkTerm DB.two Typ.aa [ mkTerm DB.zero Typ.a [] ]
                               , mkTerm DB.zero Typ.a []
                               ]
      t2 = mkTerm Fun.f Typ.a [ mkTerm DB.one Typ.aa []
                              , mkTerm Fun.h Typ.a [ mkTerm DB.zero Typ.a [] ]
                              ]
      tis' = [ ( mkTerm Fun.f Typ.aa [ mkTerm DB.one Typ.a []
                                     , mkTerm DB.zero Typ.a []
                                     ]
               , 1
               )
             , ( mkTerm DB.one Typ.a []
               , 0
               )
             ]
      t3 = mkTerm Fun.f Typ.a [ mkTerm DB.zero Typ.a []
                              , mkTerm DB.one Typ.a []
                              ]
      t3' = mkTerm DB.one Typ.a [ mkTerm DB.zero Typ.a []]
  it "computes a positive example correctly" $
    discharge 1 tis t1 `shouldBe` Just t1'
  it "computes a negative example correctly" $
    discharge 1 tis t2 `shouldBe` Nothing
  it "computes a composite example correctly" $
    discharge 2 tis' t3 `shouldBe` Just t3'

substOpsSpecs :: Spec
substOpsSpecs = describe "Subst.Ops" $ do
  spec_dbMap
  spec_applyDBMap
  spec_apply
  spec_compose
  spec_applyAbsToVar
  spec_applyAbsToTerms
  spec_discharge
