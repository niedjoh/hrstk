{-# LANGUAGE OverloadedStrings #-}

module RewritingSpec (rewritingSpecs) where

import Data.List (sort)
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy, shouldNotSatisfy)

import qualified Predefined.Typ as Typ 
import qualified Predefined.DB as DB
import qualified Predefined.Var as Var
import qualified Predefined.Fun as Fun

import Term.Type (Term,Head)
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

es2 :: ES
es2 = [ Equation { lhs = mkTerm Fun.f Typ.a []
                 , rhs = mkTerm Fun.g Typ.a []
                 , isRule = True
                 }
      ]

es3 :: ES
es3 = [ Equation { lhs = mkTerm Fun.g Typ.a [ mkTerm Var.x Typ.a [] ]
                 , rhs = mkTerm Fun.h Typ.a [ mkTerm Var.x Typ.a [] ]
                 , isRule = True
                 }
      , Equation { lhs = mkTerm Fun.f Typ.a [ mkTerm Var.y Typ.aa [ mkTerm DB.zero Typ.a [] ]
                                            , mkTerm Var.z Typ.a [] ]
                 , rhs = mkTerm Var.y Typ.a [ mkTerm Var.z Typ.a [] ]
                 , isRule = True
                 }
      ]

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

u1 :: Head -> Term
u1 h = mkTerm h Typ.aa [ mkTerm DB.zero Typ.a [] ]

u2 :: Head -> Term
u2 h = mkTerm h Typ.a [ mkTerm Var.x Typ.a [] ]

u3 :: Head -> Head -> Term
u3 h g = mkTerm h Typ.a [ mkTerm g Typ.a [ mkTerm Var.x Typ.a [] ] ]
                         
t6 :: Term
t6 = mkTerm Fun.f Typ.a [ u1 Fun.g, u2 Fun.g ]

t6res :: [Term]
t6res = [ t6
        , mkTerm Fun.f Typ.a [ u1 Fun.h, u2 Fun.g ]
        , mkTerm Fun.f Typ.a [ u1 Fun.g, u2 Fun.h ]
        , mkTerm Fun.f Typ.a [ u1 Fun.h, u2 Fun.h ]
        , u3 Fun.g Fun.g
        , u3 Fun.h Fun.g
        , u3 Fun.g Fun.h
        , u3 Fun.h Fun.h
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

spec_possibleRootMultiSteps :: Spec
spec_possibleRootMultiSteps =
  describe "possibleRootMultiSteps" $ do
    it "handles ground example correctly" $
      possibleRootMultiSteps es2 (mkTerm Fun.f Typ.a []) `shouldBe` [ mkTerm Fun.g Typ.a [] ]

spec_possibleMultiSteps :: Spec
spec_possibleMultiSteps =
  describe "possibleMultiSteps" $ do
    it "handles abstractions correctly" $
      possibleMultiSteps es2 (mkTerm Fun.f Typ.aaa []) `shouldBe` [ mkTerm Fun.f Typ.aaa []
                                                                  , mkTerm Fun.g Typ.aaa []
                                                                  ]
    it "computes example correctly" $ do
      sort (possibleMultiSteps es3 t6) `shouldBe` sort t6res
    
spec_rewriteToNFs :: Spec
spec_rewriteToNFs =
  describe "rewriteToNFs" $ do
    it "computes an example correctly" $
      rewriteToNFs es t2 `shouldBe` [t2'nf,t2'']

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
  spec_possibleRootMultiSteps
  spec_possibleMultiSteps
  spec_rewriteToNFs
  spec_joinable
