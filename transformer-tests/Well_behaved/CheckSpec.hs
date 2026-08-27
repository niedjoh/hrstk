{-# LANGUAGE OverloadedStrings #-}
module Well_behaved.CheckSpec where

import Test.Hspec
import WellBehaved
import Term.Type
import Utils.Type
import Typ.Type
import Data.Text (Text)


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

-- Example 11, from "Towards an HRS Category in TermCOMP"
term1 = app (func "f") [fv "F", fv "x"]

term2 = app (func "f") [lam 1 (app (fv "F") [db 0]), fv "x"]

term3 = app (func "f") [app (fv "G") [(func "g")], fv "x"]

term4 = app (func "f") [lam 1 (app (fv "G") [func "g", db 0]), fv "x"]

term5 = app (func "f") [app (fv "G") [lam 1 (app (func "g") [db 0])], fv "x"]

term6 = app (func "f") [lam 1 (app (fv "G") [lam 1 (app (func "g") [db 0]), db 0]), fv "x"]

example11 = [term1, term2, term3, term4, term5, term6]

nestedLamdba = app (func "f") [app (fv "F") [lam 1 (app (func "g") [lam 1 (app (db 1) [db 0])])]]

nestedLambdaReduced = app (func "f") [app (fv "F") [func "g"]]

doubleLambda = app (func "f") [app (fv "F") [lam 1 (app (func "g") [db 0]), lam 1 (app (func "g") [db 0]), app (func "g") [app (func "g") []]]]

doubleLambdaReduced = app (func "f") [app (fv "F") [func "g" , func "g", app (func "g") [app (func "g") []]]]

nothingToReduce = app (func "f") [app (fv "F") [app (func "g") [lam 1 (app (func "g") [db 0])]]]

spec :: Spec
spec = do
    describe "Environment Check" $ do
        it "successfully imports the module and runs a test" $ do
            True `shouldBe` True
    
    describe "Test checkWellBehavedness" $ do
        it "not all terms of Example 11 are well-behaved" $ do
            (all id $ map checkWellBehavedness example11) `shouldBe` False

        it "evaluates terms 1-4 as well-behaved" $ do
            let wellBehavedTerms = take 4 example11
            mapM_ (\term -> checkWellBehavedness term `shouldBe` True) wellBehavedTerms

        it "evaluates terms 5 and 6 as NOT well-behaved" $ do
            let nonWellBehavedTerms = drop 4 example11
            mapM_ (\term -> checkWellBehavedness term `shouldBe` False) nonWellBehavedTerms

    describe "Test etaReduceFVLambdas" $ do
        it "Well-behaved terms stay the same" $ do
            ([term1, term2, term3, term4] == (map etaReduceFVLambdas [term1, term2, term3, term4])) `shouldBe` True
        
        it "Terms are well-behaved after transformation" $ do
            (all id $ map (checkWellBehavedness . etaReduceFVLambdas) example11) `shouldBe` True

        it "Nested lambda gets transformed" $ do
            (etaReduceFVLambdas nestedLamdba) `shouldBe` nestedLambdaReduced

        it "Lambdas get reduced at multiple argument positions" $ do
            (etaReduceFVLambdas doubleLambda) `shouldBe` doubleLambdaReduced

        it "Lambdas at non-FV argument position do not get reduced" $ do
            (etaReduceFVLambdas nothingToReduce) `shouldBe` nothingToReduce

