{-# LANGUAGE OverloadedStrings #-}

module WellBehavedSpec (wbSpecs) where

import Data.Text (Text)
import Test.Hspec (Spec, describe, it, shouldBe)

import Utils.Type (Id(..),Var(..))
import Term.Type (Term(..),Head(..))
import Typ.Type (Typ(..))
import WellBehaved (checkWellBehavedness,etaReduceAnchorsAtRoot)

dummyTyp :: Typ
dummyTyp = Typ [] (Id "N")

-- Creates a De Bruijn index variable: DB n
db :: Int -> Term
db n = Term { nlams = 0, hd = DB n, sp = [], typ = dummyTyp }

-- Creates a Free Variable: FV "name"
fv :: Text -> Term
fv name = Term { nlams = 0, hd = FV (Named (Id name)), sp = [], typ = dummyTyp }

-- Creates a standard Function Symbol: F "name"
func :: Text -> Term
func name = Term { nlams = 0, hd = F (Id name), sp = [], typ = dummyTyp }

-- Applies a list of argument terms to a head term (builds the spine)
app :: Term -> [Term] -> Term
app t args = t { sp = args }

-- Wraps a term in 'n' lambdas
lam :: Int -> Term -> Term
lam n t = t { nlams = n }

term1 :: Term
term1 = app (func "f") [fv "F", fv "x"]

term2 :: Term
term2 = app (func "f") [lam 1 (app (fv "F") [db 0]), fv "x"]

term3 :: Term
term3 = app (func "f") [app (fv "G") [(func "g")], fv "x"]

term4 :: Term
term4 = app (func "f") [lam 1 (app (fv "G") [func "g", db 0]), fv "x"]

term5 :: Term
term5 = app (func "f") [app (fv "G") [lam 1 (app (func "g") [db 0])], fv "x"]

term6 :: Term
term6 = app (func "f") [lam 1 (app (fv "G") [lam 1 (app (func "g") [db 0]), db 0]), fv "x"]

example11 :: [Term]
example11 = [term1, term2, term3, term4, term5, term6]

spec_checkWellBehavedness :: Spec
spec_checkWellBehavedness = do
  let nonBasicBody = app (func "f") [(lam 1 (app (func "h") [db 0])) { typ = Typ [dummyTyp, dummyTyp] (Id "N") }]
  describe "checkWellBehavedness" $ do
    it "identifies well-behaved terms" $ do
      let wellBehavedTerms = take 4 example11
      mapM_ (\term -> checkWellBehavedness term `shouldBe` True) wellBehavedTerms
    it "identifies non-well-behaved terms" $ do
      let nonWellBehavedTerms = drop 4 example11
      mapM_ (\term -> checkWellBehavedness term `shouldBe` False) nonWellBehavedTerms
    it "rejects a lambda with non-basic body" $ do
      checkWellBehavedness nonBasicBody `shouldBe` False

spec_etaReduceAnchorsAtRoot :: Spec
spec_etaReduceAnchorsAtRoot = do
  let nestedLamdba = app (func "f") [app (fv "F") [lam 1 (app (func "g") [lam 1 (app (db 1) [db 0])])]]
      nestedLambdaReduced = app (func "f") [app (fv "F") [func "g"]]
      doubleLambda = app (func "f") [app (fv "F") [ lam 1 (app (func "g") [db 0])
                                                  , lam 1 (app (func "g") [db 0])
                                                  , app (func "g") [app (func "g") []]] ]
      doubleLambdaReduced = app (func "f") [app (fv "F") [ func "g"
                                                         , func "g", app (func "g") [app (func "g") []]] ]
      nothingToReduce = app (func "f") [app (fv "F") [app (func "g") [lam 1 (app (func "g") [db 0])]]]
      appliedBoundVar = app (func "f") [app (fv "F") [lam 1 (app (func "g") [app (db 0) [func "a"]])]]
      innerBinder = app (func "f") [app (fv "F") [lam 1 (app (func "g") [lam 1 (db 0)])]]
      greedyInner = app (func "f") [app (fv "F") [lam 1 (app (func "h") [lam 1 (app (func "k") [db 0]), db 0])]]
      greedyInnerExpected = app (func "f") [app (fv "F") [app (func "h") [lam 1 (app (func "k") [db 0])]]]
  describe "etaReduceAnchorsAtRoot " $ do
    it "well-behaved terms stay the same" $ do
      ([term1, term2, term3, term4] == (map etaReduceAnchorsAtRoot  [term1, term2, term3, term4])) `shouldBe` True 
    it "terms are well-behaved after transformation" $ do
      (all id $ map (checkWellBehavedness . etaReduceAnchorsAtRoot ) example11) `shouldBe` True
    it "nested lambda gets transformed" $ do
      (etaReduceAnchorsAtRoot  nestedLamdba) `shouldBe` nestedLambdaReduced
    it "lambdas get reduced at multiple argument positions" $ do
      (etaReduceAnchorsAtRoot  doubleLambda) `shouldBe` doubleLambdaReduced
    it "lambdas at non-FV argument position do not get reduced" $ do
      (etaReduceAnchorsAtRoot  nothingToReduce) `shouldBe` nothingToReduce
    it "does not reduce when the bound variable is applied" $ do
      etaReduceAnchorsAtRoot  appliedBoundVar `shouldBe` appliedBoundVar
    it "does not reduce when the last argument has its own binder" $ do
      etaReduceAnchorsAtRoot  innerBinder `shouldBe` innerBinder
    it "keeps lambdas under function symbols" $ do
      etaReduceAnchorsAtRoot  greedyInner `shouldBe` greedyInnerExpected

wbSpecs :: Spec
wbSpecs = describe "WellBehaved" $ do
    spec_checkWellBehavedness
    spec_etaReduceAnchorsAtRoot

