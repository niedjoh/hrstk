{-# LANGUAGE OverloadedStrings #-}

module EquationOpsSpec (equationOpsSpecs) where

import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy, shouldNotSatisfy)

import qualified Predefined.Typ as Typ 
import qualified Predefined.DB as DB
import qualified Predefined.Var as Var
import qualified Predefined.Fun as Fun

import Term.Ops (mkTerm)
import Equation.Type (Equation(..))
import Equation.Ops

spec_rule :: Spec
spec_rule =
  describe "rule" $ do
    let r1 = Equation { lhs = mkTerm Fun.f Typ.a [ mkTerm Var.x Typ.aa [ mkTerm DB.zero Typ.a []]]
                      , rhs = mkTerm Var.x Typ.a [ mkTerm Fun.c Typ.a [] ]
                      , isRule = True
                      }
        r2 = Equation { lhs = mkTerm Fun.c Typ.a []
                      , rhs = mkTerm Fun.d Typ.b []
                      , isRule = True
                      }
        r3 = Equation { lhs = mkTerm Fun.f Typ.aa [ mkTerm DB.zero Typ.a [] ]
                      , rhs = mkTerm DB.zero Typ.aa []
                      , isRule = True
                      }
        r4 = Equation { lhs = mkTerm Var.x Typ.a [ mkTerm Fun.c Typ.a [] ]
                      , rhs = mkTerm Fun.d Typ.a []
                      , isRule = True
                      }
        r5 = Equation { lhs = mkTerm Fun.f Typ.a [ mkTerm Var.x Typ.a [] ]
                      , rhs = mkTerm Fun.g Typ.a [ mkTerm Var.y Typ.a [] ]
                      , isRule = True
                      }
    it "accepts well-formed rule" $
      r1 `shouldSatisfy` rule
    it "rejects when sorts do not match" $
      r2 `shouldNotSatisfy` rule
    it "rejects when rule has nonsort type" $
      r3 `shouldNotSatisfy` rule
    it "rejects lhs headed by var" $
      r4 `shouldNotSatisfy` rule 
    it "rejects when var condition is not fulfilled" $
      r5 `shouldNotSatisfy` rule

spec_dhpRuleVariants :: Spec
spec_dhpRuleVariants =
  describe "dhpRuleVariants" $ do
    let r1 = Equation { lhs = mkTerm Fun.f Typ.a [ mkTerm Var.z Typ.aaa [ mkTerm DB.one Typ.a []
                                                                        , mkTerm DB.zero Typ.a []
                                                                        ]
                                                 ]
                      , rhs = mkTerm Fun.f Typ.a [ mkTerm Var.z Typ.aaa [ mkTerm DB.zero Typ.a []
                                                                        , mkTerm DB.one Typ.a []
                                                                        ]
                                                 ]
                      , isRule = True
                      }
        r2 = Equation { lhs = rhs r1
                      , rhs = lhs r1
                      , isRule = True
                      }
 
        r3 = Equation { lhs = rhs r1
                      , rhs = rhs r1
                      , isRule = True
                      }
        r4 = Equation { lhs = mkTerm Fun.f Typ.a [ mkTerm Var.z Typ.aa [ mkTerm Fun.g Typ.a [ mkTerm DB.one Typ.a [] ]
                                                                       , mkTerm Fun.c Typ.a []
                                                                       ]
                                                 ]
                      , rhs = mkTerm Fun.h Typ.a [ mkTerm Var.z Typ.aa [ mkTerm DB.one Typ.a []
                                                                       , mkTerm Fun.c Typ.a []
                                                                       ]
                                                 ]
                      , isRule = True
                      }
        r5 = Equation { lhs = mkTerm Fun.f Typ.a [ mkTerm Var.zp Typ.aa [ mkTerm Fun.c Typ.a []
                                                                        , mkTerm Fun.g Typ.a [ mkTerm DB.one Typ.a [] ]
                                                                        ]
                                                 ]
                      , rhs = mkTerm Fun.h Typ.a [ mkTerm Var.zp Typ.aa [ mkTerm Fun.c Typ.a []
                                                                        , mkTerm DB.one Typ.a []
                                                                        ]
                                                 ]
                      , isRule = True
                      }
        r6 = Equation { lhs = lhs r5
                      , rhs = mkTerm Fun.h Typ.a [ mkTerm Var.z Typ.aa [ mkTerm Fun.c Typ.a []
                                                                       , mkTerm DB.one Typ.a []
                                                                       ]
                                                 ]
                      , isRule = True
                      }
        r7 = Equation { lhs = lhs r5
                      , rhs = mkTerm Fun.h Typ.a [ mkTerm Var.zp Typ.aa [ mkTerm DB.one Typ.a []
                                                                        , mkTerm Fun.c Typ.a []
                                                                        ]
                                                 ]
                      , isRule = True
                      }
    it "accepts permutative variants" $
      (r1,r2)  `shouldSatisfy` (uncurry dhpRuleVariants)
    it "is symmetric" $
      (r2,r1) `shouldSatisfy` (uncurry dhpRuleVariants)
    it "rejects non-variants" $
      (r1,r3) `shouldNotSatisfy` (uncurry dhpRuleVariants)
    it "accepts renamed & permutative variants" $
      (r4,r5) `shouldSatisfy` (uncurry dhpRuleVariants)
    it "rejects inconsistency wrt. renaming" $
      (r4,r6) `shouldNotSatisfy` (uncurry dhpRuleVariants)
    it "rejects inconsistency wrt. argument order" $
      (r4,r7) `shouldNotSatisfy` (uncurry dhpRuleVariants)
                               
spec_canonicalFVrename :: Spec
spec_canonicalFVrename =
  describe "canonicalFVrename" $ do
    let l1 =  mkTerm Fun.f Typ.b [ mkTerm Var.x Typ.aaa []
                                 , mkTerm Var.y Typ.aaa []
                                 , mkTerm Fun.g Typ.b [ mkTerm Var.z Typ.a []
                                                      , mkTerm Var.xp Typ.b []
                                                      ]
                                 , mkTerm Var.yp Typ.a []
                                 ]
        r1 = mkTerm Fun.g Typ.b [ mkTerm Var.x Typ.a [ mkTerm Var.z Typ.a []
                                                     , mkTerm Var.yp Typ.a []
                                                     ]
                                , mkTerm Fun.f Typ.b [ mkTerm Var.x Typ.aaa []
                                                     , mkTerm Var.y Typ.aaa []
                                                     , mkTerm Var.xp Typ.b []
                                                     , mkTerm Var.y Typ.a [ mkTerm Var.z Typ.a []
                                                                          , mkTerm Var.yp Typ.a []
                                                                          ]
                                                     ]
                                ]        
        l2 =  mkTerm Fun.f Typ.b [ mkTerm Var.fresh0 Typ.aaa []
                                 , mkTerm Var.fresh1 Typ.aaa []
                                 , mkTerm Fun.g Typ.b [ mkTerm Var.fresh2 Typ.a []
                                                      , mkTerm Var.fresh3 Typ.b []
                                                      ]
                                 , mkTerm Var.fresh4 Typ.a []
                                 ]
        r2 = mkTerm Fun.g Typ.b [ mkTerm Var.fresh0 Typ.a [ mkTerm Var.fresh2 Typ.a []
                                                          , mkTerm Var.fresh4 Typ.a []
                                                          ]
                                , mkTerm Fun.f Typ.b [ mkTerm Var.fresh0 Typ.aaa []
                                                     , mkTerm Var.fresh1 Typ.aaa []
                                                     , mkTerm Var.fresh3 Typ.b []
                                                     , mkTerm Var.fresh1 Typ.a [ mkTerm Var.fresh2 Typ.a []
                                                                               , mkTerm Var.fresh4 Typ.a []
                                                                               ]
                                                     ]
                                ]        
        rule1 = Equation { lhs = l1
                         , rhs = r1
                         , isRule = True
                         }        
        rule2 = Equation { lhs = l2
                         , rhs = r2
                         , isRule = True
                         }
    it "computes example correctly" $
      canonicalFVrename rule1 `shouldBe` rule2

equationOpsSpecs :: Spec
equationOpsSpecs = describe "Equation.Ops" $ do
  spec_rule
  spec_dhpRuleVariants
  spec_canonicalFVrename
