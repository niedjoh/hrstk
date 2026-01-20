{-# LANGUAGE OverloadedStrings #-}

module CriticalPairsSpec (criticalPairsSpecs) where

import Control.Monad.State (evalState)
import Control.Monad.Trans.Maybe (runMaybeT)
import Test.Hspec (Spec, describe, it, shouldBe)

import qualified Predefined.Sort as Sort
import qualified Predefined.Typ as Typ 
import qualified Predefined.DB as DB
import qualified Predefined.Var as Var
import qualified Predefined.Fun as Fun

import Typ.Type (Typ(..))
import Term.Type (Term(..),Head)
import Term.Ops (mkTerm, shiftDB)
import Equation.Type (Equation(..),ES)
import Equation.CriticalPairs

t11 :: Term
t11 = mkTerm Fun.f Typ.a [ mkTerm Fun.g Typ.a [ mkTerm Var.x Typ.a [] ] ]

t12 :: Term
t12 = mkTerm Fun.f Typ.a [ mkTerm Var.x Typ.a [] ]

t21 :: Term
t21 = mkTerm Fun.h Typ.b [ mkTerm Fun.g Typ.a [ mkTerm Var.x Typ.a [] ] ]

t22 :: Term
t22 = mkTerm Fun.h Typ.b [ mkTerm Var.x Typ.a [] ]

t31_1 :: Term
t31_1 = mkTerm Var.z Typ.aa [ mkTerm Fun.g Typ.a [ mkTerm DB.zero Typ.a [] ] ]

t31 :: Term
t31 = mkTerm Fun.c Typ.a [ t31_1 ]

t32 :: Term
t32 = mkTerm Var.z Typ.a [ mkTerm Fun.d Typ.a [] ]

e11 :: Equation
e11 = Equation { lhs = t11, rhs = t12, isRule = True}

e12 :: Equation
e12 = Equation { lhs = t21, rhs = t22, isRule = True}

e13 :: Equation
e13 = Equation { lhs = t31, rhs = t32, isRule = True}

es1 :: ES
es1 = [e11, e12, e13]

cpse11e13 :: [Equation]
cpse11e13 =
  [ Equation { lhs = mkTerm Fun.c Typ.a [ mkTerm Var.fresh2 Typ.aa [ mkTerm Fun.f Typ.a [ mkTerm DB.zero Typ.a [] ]
                                                                   , mkTerm Fun.g Typ.a [ mkTerm DB.zero Typ.a [] ]
                                                                   ] ]
             , rhs = mkTerm Var.fresh2 Typ.a [ mkTerm Fun.f Typ.a [ mkTerm Fun.d Typ.a [] ]
                                             , mkTerm Fun.d Typ.a []
                                             ]
             , isRule = False
             }
  ]

cpse12e13 :: Head -> [Equation]
cpse12e13  v'' =
  [ Equation { lhs = mkTerm Fun.c Typ.a [ mkTerm v'' Typ.aa [ mkTerm Fun.h Typ.b [ mkTerm DB.zero Typ.a [] ]
                                                            , mkTerm Fun.g Typ.a [ mkTerm DB.zero Typ.a [] ]
                                                            ] ]
             , rhs = mkTerm v'' Typ.a [ mkTerm Fun.h Typ.b [ mkTerm Fun.d Typ.a [] ]
                                      , mkTerm Fun.d Typ.a []
                                      ]
             , isRule = False
             }
  ]

s11 :: Term
s11 = mkTerm Fun.f Typ.a [ mkTerm Var.x Typ.aa [ mkTerm Fun.h Typ.a [ mkTerm DB.zero Typ.a [] ] ]
                         , mkTerm Var.y Typ.a []
                         ]

s12 :: Term
s12 = mkTerm Var.x Typ.a [ s42 ]

s21 :: Term
s21 = mkTerm Fun.f Typ.a [ mkTerm Var.x Typ.aa [ mkTerm DB.zero Typ.a [] ]
                         , mkTerm Var.y Typ.a []
                         ]

s22 :: Term
s22 = mkTerm Var.x Typ.a [ mkTerm Var.y Typ.a [] ]

s31 :: Term
s31 = mkTerm Fun.h Typ.a [ s41 ]

s32 :: Term
s32 = mkTerm Var.y Typ.a []

s41 :: Term
s41 = mkTerm Fun.h Typ.a [ mkTerm Var.y Typ.a [] ]

s42 :: Term
s42 = mkTerm Fun.g Typ.a [ mkTerm Var.y Typ.a []
                         , mkTerm Fun.c Typ.a []
                         ]

s51 :: Term
s51 = mkTerm Fun.h Typ.a [ s42 ]

s61 :: Term
s61 = mkTerm Fun.g Typ.a [ s42
                         , mkTerm Fun.c Typ.a []
                         ] 

e21 :: Equation
e21 = Equation { lhs = s11, rhs = s12, isRule = True}

e22 :: Equation
e22 = Equation { lhs = s21, rhs = s22, isRule = True}

e23 :: Equation
e23 = Equation { lhs = s31, rhs = s32, isRule = True}

e24 :: Equation
e24 = Equation { lhs = s41, rhs = s42, isRule = True}

e25 :: Equation
e25 = Equation { lhs = s51, rhs = s32, isRule = True}

e26 :: Equation
e26 = Equation { lhs = s61, rhs = s32, isRule = True}

es2 :: ES
es2 = [e21, e22, e23, e24, e25, e26]

cpses2 :: [Equation]
cpses2 =
  [ Equation { lhs = mkTerm (Var.fresh 8) Typ.a [ mkTerm Fun.g Typ.a [ mkTerm (Var.fresh 9) Typ.a []
                                                                      , mkTerm Fun.c Typ.a []
                                                                      ] ]
             , rhs = mkTerm (Var.fresh 8) Typ.a [ mkTerm Fun.h Typ.a [ mkTerm (Var.fresh 9) Typ.a [] ] ]
             , isRule = False
             }
  , Equation { lhs = mkTerm (Var.fresh 12) Typ.a [ mkTerm Fun.h Typ.a [ mkTerm (Var.fresh 11) Typ.a [] ] ]
             , rhs = mkTerm (Var.fresh 12) Typ.a [ mkTerm Fun.g Typ.a [ mkTerm (Var.fresh 11) Typ.a []
                                                                      , mkTerm Fun.c Typ.a []
                                                                      ] ]
             , isRule = False
             }
  , Equation { lhs = mkTerm Fun.f Typ.a [ mkTerm (Var.fresh 23) Typ.aa [ mkTerm DB.zero Typ.a []
                                                                       , mkTerm Fun.h Typ.a [ mkTerm DB.zero Typ.a [] ]
                                                                       ]
                                        , mkTerm Var.y Typ.a [] ]
             , rhs = mkTerm (Var.fresh 23) Typ.a [ mkTerm Fun.h Typ.a [ s42 ]
                                                 , s42
                                                 ]
             , isRule = False
             }
  , Equation { lhs = mkTerm Fun.h Typ.a [ mkTerm (Var.fresh 28) Typ.a [] ]
             , rhs = mkTerm Fun.h Typ.a [ mkTerm (Var.fresh 28) Typ.a [] ]
             , isRule = False
             }
  , Equation { lhs = mkTerm (Var.fresh 29) Typ.a []
             , rhs = mkTerm Fun.g Typ.a [ mkTerm Fun.h Typ.a [ mkTerm (Var.fresh 29) Typ.a [] ]
                                        , mkTerm Fun.c Typ.a [] ] 
             , isRule = False
             }
  , Equation { lhs = mkTerm Fun.f Typ.a [ mkTerm Var.x Typ.aa [ mkTerm Fun.g Typ.a [ mkTerm DB.zero Typ.a []
                                                                                   , mkTerm Fun.c Typ.a []
                                                                                   ]
                                                              ]
                                        , mkTerm Var.y Typ.a [] ]
             , rhs = mkTerm Var.x Typ.a [ s42 ]
             , isRule = False
             }
  , Equation { lhs = mkTerm Fun.g Typ.a [ mkTerm Fun.h Typ.a [ mkTerm Var.y Typ.a [] ]
                                        , mkTerm Fun.c Typ.a []
                                        ] 
             , rhs = mkTerm Var.y Typ.a []
             , isRule = False
             }
  , Equation { lhs = mkTerm Fun.h Typ.a [ mkTerm Fun.g Typ.a [ mkTerm (Var.fresh 38) Typ.a []
                                                             , mkTerm Fun.c Typ.a []
                                                             ] ]
             , rhs = mkTerm (Var.fresh 38) Typ.a []
             , isRule = False
             }
  , Equation { lhs = mkTerm Fun.g Typ.a [ mkTerm Fun.g Typ.a [ mkTerm Var.y Typ.a []
                                                             , mkTerm Fun.c Typ.a []
                                                             ]
                                        , mkTerm Fun.c Typ.a []
                                        ]
             , rhs = mkTerm Var.y Typ.a []
             , isRule = False
             }
  , Equation { lhs = mkTerm Fun.h Typ.a [ mkTerm (Var.fresh 49) Typ.a [] ]
             , rhs = mkTerm Fun.g Typ.a [ mkTerm (Var.fresh 49) Typ.a []
                                        , mkTerm Fun.c Typ.a []
                                        ]
             , isRule = False
             }
  , Equation { lhs = mkTerm (Var.fresh 50) Typ.a []
             , rhs = mkTerm Fun.g Typ.a [ mkTerm Fun.g Typ.a [ mkTerm (Var.fresh 50) Typ.a []
                                                             , mkTerm Fun.c Typ.a []
                                                             ]
                                        , mkTerm Fun.c Typ.a []
                                        ]
             , isRule = False
             }
  , Equation { lhs = mkTerm Fun.h Typ.a [ mkTerm (Var.fresh 59) Typ.a [] ]
             , rhs = mkTerm Fun.g  Typ.a [ mkTerm (Var.fresh 59) Typ.a []
                                         , mkTerm Fun.c Typ.a []
                                         ]
             , isRule = False
             }
  , Equation { lhs = mkTerm Fun.g Typ.a [ mkTerm (Var.fresh 60) Typ.a []
                                        , mkTerm Fun.c Typ.a []
                                        ]
             , rhs = mkTerm Fun.g Typ.a [ mkTerm (Var.fresh 60) Typ.a []
                                        , mkTerm Fun.c Typ.a []
                                        ]
             , isRule = False
             }
  ]

spec_renameAndLift :: Spec
spec_renameAndLift =
  describe "renameAndLift" $ do
    let rn as ts e = evalState (renameAndLift as ts e) 0
        as1 = [Typ.aa,Typ.a]
        ts1 = [ mkTerm DB.two Typ.aa [ mkTerm DB.zero Typ.a [] ]
              , mkTerm DB.zero Typ.a [] ]
        a1 = Typ as1 Sort.a
        l1 = mkTerm Fun.f Typ.a [ mkTerm Fun.g Typ.aa [ mkTerm Var.x Typ.a [ mkTerm DB.zero Typ.a [] ] ] 
                                , mkTerm Var.y Typ.a []
                                ]
        r1 = mkTerm Fun.g Typ.a [ mkTerm Fun.f Typ.a [ mkTerm Var.y Typ.a [] ] ]
        l1' = mkTerm Fun.f a1 [ mkTerm Fun.g Typ.aa [ mkTerm Var.fresh0 Typ.a (map (shiftDB 1) ts1 ++ [ mkTerm DB.zero Typ.a [] ]) ] 
                              , mkTerm Var.fresh1 Typ.a ts1
                              ]

        r1' = mkTerm Fun.g a1 [ mkTerm Fun.f Typ.a [ mkTerm Var.fresh1 Typ.a ts1 ] ]
        eq1 = Equation { lhs = l1, rhs = r1, isRule = False}
        eq1' = Equation { lhs = l1', rhs = r1', isRule = False}
    it "computes example correctly" $
      rn as1 ts1 eq1 `shouldBe` eq1'
          
spec_overlaps :: Spec
spec_overlaps =
  describe "overlaps" $ do
    let u1 = mkTerm Fun.f Typ.a [ mkTerm Var.z Typ.a [] ]
        u221 = mkTerm Fun.f Typ.a [ mkTerm Fun.c Typ.a []
                                  , mkTerm DB.zero Typ.a []
                                  ]
        u22 = mkTerm Var.y Typ.a [u221]
        u2 = mkTerm Fun.f Typ.aa [ mkTerm Var.x Typ.a [ mkTerm DB.zero Typ.a [] ]
                                 , u22
                                 ]
        compute = map (\(ctx,as,p,t) -> (ctx t,as,p,t)) (overlaps u1 u2)
        res = [ (u2, [Typ.a], [], u2{nlams = 0, typ = Typ.a})
              , (u2, [Typ.a], [2], u22)
              , (u2, [Typ.a], [2,1], u221) 
              ]
    it "computes example correctly" $
      compute `shouldBe` res

spec_criticalPairsFixedPos :: Spec
spec_criticalPairsFixedPos =
  describe "criticalPairsFixedPos" $ do
    let cpsfp e subt t = evalState (runMaybeT $ criticalPairsFixedPos e subt t) 0
        subterm = ( \x -> mkTerm Fun.c Typ.a [ Term { nlams = 1, hd = hd x, sp = sp x, typ = Typ.aa} ] 
                  , [Typ.a]
                  , t31_1{nlams = 0, typ = Typ.a}
                  )
    it "can handle variable overlap" $
      cpsfp e11 subterm t32 `shouldBe` Just cpse11e13
    it "can handle different types in variable overlap" $
      cpsfp e12 subterm t32  `shouldBe` Just (cpse12e13 Var.fresh2)

spec_criticalPairs :: Spec
spec_criticalPairs =
  describe "criticalPairs" $ do
    let critp x y = map (\(z,_,_,_) -> z) <$> evalState (runMaybeT $ criticalPairs x y) 0
    it "computes CPs of toy example correctly" $
      critp es1 es1 `shouldBe` Just (cpse11e13 ++ cpse12e13 (Var.fresh 8))
    it "computes CPS of repl example correctly" $
      critp es2 es2 `shouldBe` Just cpses2

criticalPairsSpecs :: Spec
criticalPairsSpecs = describe "Equation.CriticalPairs" $ do
  spec_renameAndLift
  spec_overlaps
  spec_criticalPairsFixedPos
  spec_criticalPairs
