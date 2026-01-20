{-# LANGUAGE OverloadedStrings #-}

module RewritingSpec (rewritingSpecs) where

import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy, shouldNotSatisfy)

import qualified Predefined.Typ as Typ 
import qualified Predefined.DB as DB
import qualified Predefined.Var as Var
import qualified Predefined.Fun as Fun

import Term.Type (Term)
import Term.Ops (mkTerm)
import Equation.Type (Equation(..),ES)
import Equation.Rewriting

e1 :: Equation
e1 = Equation { lhs = mkTerm Fun.f Typ.a [ mkTerm Var.x Typ.aa
                                             [ mkTerm Fun.h Typ.a [ mkTerm DB.zero Typ.a [] ] ]
                                         , mkTerm Var.y Typ.a []
                                         ]
              , rhs = mkTerm Var.x Typ.a [ mkTerm Fun.g Typ.a [ mkTerm Var.y Typ.a []
                                                              , mkTerm Fun.c Typ.a []
                                                              ] ]
              , isRule = True
              }
     
e2 :: Equation
e2 = Equation { lhs = mkTerm Fun.h Typ.a [ mkTerm Fun.h Typ.a [ mkTerm Var.y Typ.a [] ] ]
              , rhs = mkTerm Var.y Typ.a []
              , isRule = True
              }

e3 :: Equation
e3 = Equation { lhs = mkTerm Fun.c Typ.a []
              , rhs = mkTerm Fun.d Typ.a []
              , isRule = True
              }

es :: ES
es = [e1, e2, e3]

t1 :: Term
t1 = mkTerm Fun.h Typ.a [ mkTerm Fun.h Typ.a [ mkTerm Fun.h Typ.a [ mkTerm Var.y Typ.a [] ] ] ]

t1' :: Term
t1' = mkTerm Fun.h Typ.a [ mkTerm Var.y Typ.a [] ]

t2 :: Term
t2 = mkTerm Fun.f Typ.a [ mkTerm Fun.h Typ.aa [ mkTerm Fun.h Typ.a [ mkTerm DB.zero Typ.a [] ] ]
                        , mkTerm Var.y Typ.a []
                        ]
t2' :: Term
t2' = mkTerm Fun.h Typ.a [ mkTerm Fun.g Typ.a [ mkTerm Var.y Typ.a []
                                                      , mkTerm Fun.c Typ.a []
                                                      ] ]
t2'' :: Term
t2'' = mkTerm Fun.f Typ.a [ mkTerm DB.zero Typ.aa []
                          , mkTerm Var.y Typ.a []
                          ]

t2'nf :: Term
t2'nf = mkTerm Fun.h Typ.a [ mkTerm Fun.g Typ.a [ mkTerm Var.y Typ.a []
                                                      , mkTerm Fun.d Typ.a []
                                                      ] ] 
       
t3 :: Term
t3 = mkTerm Fun.f Typ.a [ mkTerm DB.zero Typ.aa [] , mkTerm Var.y Typ.a [] ]

t4 :: Term
t4 = mkTerm Fun.f Typ.a [ mkTerm Fun.h Typ.aa [ mkTerm DB.zero Typ.a [] ]
                        , mkTerm Var.y Typ.a []
                        ]

t5 :: Term    
t5 = mkTerm Fun.f Typ.a [ mkTerm Fun.h Typ.aa [ mkTerm Fun.h Typ.a [ mkTerm Fun.h Typ.a [ mkTerm
                                                                                          DB.zero
                                                                                          Typ.a
                                                                                          []
                                                                                        ] ] ]
                        , mkTerm Var.y Typ.a []
                        ]

spec_rootReducibleSubterms :: Spec
spec_rootReducibleSubterms =
  describe "rootReducibleSubterms" $ do
    let  res = map (\(_,as,p,subt) -> (subt,as,p)) $ rootReducibleSubterms t2
    it "computes an example correctly" $
       res `shouldBe` [ ( t2
                        , []
                        , []
                        )
                      , ( mkTerm Fun.h Typ.a [ mkTerm Fun.h Typ.a [ mkTerm DB.zero Typ.a [] ] ]
                        , [Typ.a]
                        , [1]
                        )
                      , ( mkTerm Fun.h Typ.a [ mkTerm DB.zero Typ.a [] ]
                        , [Typ.a]
                        , [1,1]
                        )
                      ]

spec_rootRewriteStep :: Spec
spec_rootRewriteStep =
  describe "rootRewriteStep" $ do
    it "computes positive example correctly" $
     rootRewriteStep e1 t2  `shouldBe` Just t2'
    it "computes negative example correctly" $
     rootRewriteStep e1 t3  `shouldBe` Nothing

spec_possibleSteps :: Spec
spec_possibleSteps =
  describe "possibleSteps" $ do
    it "computes a first-order example correctly" $
      possibleSteps es t1 `shouldBe` [ t1', t1' ]
    it "computes a higher-order example correctly" $
     possibleSteps es t2 `shouldBe` [ t2', t2'' ]
    
spec_rewriteToNF :: Spec
spec_rewriteToNF =
  describe "rewriteToNF" $ do
    it "computes an example correctly" $
      rewriteToNF es t2 `shouldBe` t2'nf

spec_joinable :: Spec
spec_joinable =
  describe "joinable" $ do
    let 
    it "accepts joinable pair" $
      Equation {lhs = t4, rhs = t5, isRule = False} `shouldSatisfy` joinable es
    it "is symmetric" $
      Equation {lhs = t5, rhs = t4, isRule = False} `shouldSatisfy` joinable es
    it "rejects non-joinable pair" $
      Equation {lhs = t4, rhs = t2, isRule = False} `shouldNotSatisfy` joinable es

rewritingSpecs :: Spec
rewritingSpecs = describe "Equation.Rewriting" $ do
  spec_rootReducibleSubterms
  spec_rootRewriteStep
  spec_possibleSteps
  spec_rewriteToNF
  spec_joinable
