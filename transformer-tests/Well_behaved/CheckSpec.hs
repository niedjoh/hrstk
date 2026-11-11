{-# LANGUAGE OverloadedStrings #-}
module Well_behaved.CheckSpec where

import Test.Hspec
import WellBehaved
import Term.Type
import Utils.Type
import Typ.Type
import Data.Text (Text)
import qualified Data.Text.IO as TIO
import Equation.Type
import ARI.Parse
import System.FilePath ((</>), takeExtension, takeDirectory, splitFileName, makeRelative, dropTrailingPathSeparator, takeFileName)
import Ari
import Control.Monad (forM_)
import Utils.InputProcessing
import Utils.Parse

import Data.List (nub)
import Data.Maybe (fromMaybe)

-- free variables in order of first occurrence
varsInOrder :: Term -> [Var]
varsInOrder t = [v | FV v <- [hd t]] ++ concatMap varsInOrder (sp t)

renameFVs :: [(Var, Var)] -> Term -> Term
renameFVs m t = t { hd = h', sp = map (renameFVs m) (sp t) }
  where
    h' = case hd t of
           FV v -> FV (fromMaybe v (lookup v m))
           h    -> h

-- rename the free variables of a rule to Fresh 0, Fresh 1, ...
canonical :: Equation -> Equation
canonical e = e { lhs = renameFVs m (lhs e), rhs = renameFVs m (rhs e) }
  where
    vs = nub (varsInOrder (lhs e) ++ varsInOrder (rhs e))
    m  = zip vs (map Fresh [0 ..])

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


-- Edge case 1: the bound variable is applied to something: λw. g (w a)
-- Not an η-redex, must stay unchanged.
appliedBoundVar = app (func "f") [app (fv "F") [lam 1 (app (func "g") [app (db 0) [func "a"]])]]

-- Edge case 2: the last argument has its own binder: λw. g (λv. v)
-- DB 0 inside refers to v, not w, so this is not η-reducible either.
innerBinder = app (func "f") [app (fv "F") [lam 1 (app (func "g") [lam 1 (db 0)])]]

-- Edge case 3: greedy mode. λw. h (λv. k v) w
-- The outer lambda is η-reducible, but λv. k v is an argument of the function symbol h
-- and should stay η-long. Expected: F (h (λv. k v)), not F (h k).
greedyInner = app (func "f") [app (fv "F") [lam 1 (app (func "h") [lam 1 (app (func "k") [db 0]), db 0])]]

greedyInnerExpected = app (func "f") [app (fv "F") [app (func "h") [lam 1 (app (func "k") [db 0])]]]

-- Edge case 4: lambda whose body does not have a sort type (needs real types).
-- λx. h x where h x : N -> N, so the whole lambda has type N -> N -> N.
nonSortBody = app (func "f") [(lam 1 (app (func "h") [db 0])) { typ = Typ [dummyTyp, dummyTyp] (Id "N") }]


parseFileForTest :: FilePath -> IO (Int,[Sort],FunTypMap,Bool,Bool,ES,ES)
parseFileForTest path = do
    input <- TIO.readFile path
    
    let result = processInput path input HRS False False False (parseProblem scARI parser)
    
    case result of
        Left e  -> fail $ "Failed to parse test file " ++ path ++ ": " ++ show e
        Right r -> return r

-- Because the transformer only eta-reduces terms and parsing eta-expands, parsed HRSs should stay the same after parse -> transform -> parse 
spec_roundtrip :: Spec
spec_roundtrip = describe "Round-trip test for the transformer" $ do
  files <- runIO (getAriFiles "transformer-tests/Higher_Order_Rewriting")
  forM_ files $ \file ->
    it file $ do
      (_, _, _, _, _, before, _) <- parseFileForTest file
      let outPath = "roundtrip-tmp" </> takeFileName file
      _ <- transform file outPath
      (_, _, _, _, _, after, _) <- parseFileForTest outPath
      map canonical after `shouldBe` map canonical before
    


spec_single_transform :: Spec
spec_single_transform = do
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

    describe "Edge cases of etaReduceFVLambdas" $ do
        it "does not reduce when the bound variable is applied" $ do
            etaReduceFVLambdas appliedBoundVar `shouldBe` appliedBoundVar

        it "does not reduce when the last argument has its own binder" $ do
            etaReduceFVLambdas innerBinder `shouldBe` innerBinder

        it "keeps lambdas under function symbols η-long" $ do
            etaReduceFVLambdas greedyInner `shouldBe` greedyInnerExpected

    describe "Edge cases of checkWellBehavedness" $ do
        it "rejects a lambda whose body does not have a sort type" $ do
            checkWellBehavedness nonSortBody `shouldBe` False


spec :: Spec
spec = describe "Transform " $ do
    spec_roundtrip
    spec_single_transform

