{-# LANGUAGE OverloadedStrings #-}

module MatchSpec (matchSpecs) where

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
import Subst.Match

x :: Var
x = Named . Id $ "x"

y :: Var
y = Named . Id $ "y"

z :: Var
z = Named . Id $ "z"

lhs1 :: Term
lhs1 = mkTerm Fun.h Typ.a [ mkTerm Fun.h Typ.a [ mkTerm Var.y Typ.a [] ] ]

lhs2 :: Term
lhs2 = mkTerm Fun.f Typ.a [ mkTerm Var.x Typ.aa [ mkTerm Fun.h Typ.a [ mkTerm DB.zero Typ.a [] ] ]
                          , mkTerm Var.y Typ.a []
                          , mkTerm Var.y Typ.a []
                          ]

t1 :: Term
t1 =  mkTerm Fun.h Typ.a [ mkTerm Fun.h Typ.a [ mkTerm Fun.h Typ.a [ mkTerm Var.y Typ.a [] ] ] ]

t1' :: Term
t1' =  mkTerm Fun.h Typ.a [ mkTerm Fun.h Typ.a [ mkTerm Fun.h Typ.a [ mkTerm DB.zero Typ.a [] ] ] ]

t2 :: Term
t2 = mkTerm Fun.f Typ.a [ mkTerm Fun.h Typ.aa [ mkTerm Fun.h Typ.a [ mkTerm DB.zero Typ.a [] ] ]
                        , mkTerm Var.y Typ.a []
                        , mkTerm Var.y Typ.a []
                        ]

t2' :: Term
t2' = mkTerm Fun.f Typ.a [ mkTerm Fun.h Typ.aa [ mkTerm Fun.h Typ.a [ mkTerm DB.zero Typ.a [] ] ]
                        , mkTerm Var.y Typ.a []
                        , mkTerm Fun.c Typ.a []
                        ]

spec_matchList :: Spec
spec_matchList =
  describe "matchList" $ do
    it "computes a first-order example correctly" $
      matchList lhs1 t1 `shouldBe` Just [ ( y
                                          , mkTerm Fun.h Typ.a [ mkTerm Var.y Typ.a [] ]
                                          )
                                        ]
    it "handles dangling DBs accordingly" $
      matchList lhs1 t1' `shouldBe` Just [ ( y
                                           , mkTerm Fun.h Typ.a [ mkTerm DB.zero Typ.a [] ]
                                           )
                                         ]                      
    it "computes a higher-order example correctly" $
      matchList lhs2 t2 `shouldBe` Just [ ( x
                                          , mkTerm Fun.h Typ.aa [ mkTerm DB.zero Typ.a [] ]
                                          )
                                        , ( y
                                          , mkTerm Var.y Typ.a []
                                          )
                                        , ( y
                                          , mkTerm Var.y Typ.a []
                                          )
                                        ]
    it "maps vars to different terms" $
      matchList lhs2 t2' `shouldBe` Just [ ( x
                                           , mkTerm Fun.h Typ.aa [ mkTerm DB.zero Typ.a [] ]
                                           )
                                         , ( y
                                           , mkTerm Var.y Typ.a []
                                           )
                                         , ( y
                                           , mkTerm Fun.c Typ.a []
                                           )
                                         ]

spec_match :: Spec
spec_match =
  describe "match" $ do
    let a3 = Typ [Typ.aa] Sort.a
        lhs3 = mkTerm Var.x a3 [ mkTerm DB.one Typ.aa [ mkTerm DB.zero Typ.a [] ] ]
        t3 = mkTerm DB.zero a3 [ mkTerm Fun.c Typ.a [] ]
        lhs4 = mkTerm Fun.f Typ.a [ mkTerm Fun.g Typ.ba [ mkTerm DB.zero Typ.b [] ]
                                  , mkTerm Fun.h Typ.bb [ mkTerm Var.x Typ.abb [ mkTerm DB.one Typ.a []
                                                                               , mkTerm DB.zero Typ.b []
                                                                               ]
                                                        , mkTerm Var.y Typ.b []
                                                        , mkTerm DB.zero Typ.b []
                                                        ]
                                  , mkTerm Var.z Typ.b []
                                  ]
        t4 = mkTerm Fun.f Typ.a [ mkTerm Fun.g Typ.ba [ mkTerm DB.zero Typ.b [] ]
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
        res1 = Subst . M.fromList $
          [ ( x
            , mkTerm Fun.h Typ.aa [ mkTerm DB.zero Typ.a [] ]
            )
          , ( y
            , mkTerm Var.y Typ.a []
            )
          ]
        res3 = Subst . M.fromList $
          [ ( x
            , mkTerm DB.zero a3 [ mkTerm Fun.c Typ.a [] ]
            )
          ]
        res4 = Subst . M.fromList $
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
    it "computes positive example correctly" $
      match lhs2 t2 `shouldBe` Just res1
    it "computes negative example correctly" $
      match lhs2 t2' `shouldBe` Nothing
    it "computes abstraction example correctly" $
      match lhs3 t3 `shouldBe` Just res3
    it "normalizes DBs correctly" $
      match lhs4 t4 `shouldBe` Just res4

matchSpecs :: Spec
matchSpecs = describe "Subst.Match" $ do
  spec_matchList
  spec_match
