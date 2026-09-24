{-# LANGUAGE OverloadedStrings #-}

module DPSpec(dpSpecs) where

import qualified Data.Text.IO as TIO
import Test.Hspec (Spec, describe, it, shouldBe, shouldNotBe, runIO)
import qualified ARI
import Equation.Type
import Term.Type
import Typ.Type
import Utils.SMT
import Termination.AFP.Solver
import Utils.Parse
import Utils.Type
import Utils.InputProcessing
import Control.Monad (forM_)
import Termination.DPStatic.Solver
import Control.Monad.State (evalState)

example_8_result = [Candidate {term = Term {nlams = 0, hd = F (Id "rec"), sp = [Term {nlams = 0, hd = FV (Named (Id "H")), sp = [Term {nlams = 0, hd = DB 0, sp = [], typ = Typ [] (Id "nat")}], typ = Typ [] (Id "ord")},Term {nlams = 0, hd = FV (Named (Id "K")), sp = [], typ = Typ [] (Id "nat")},Term {nlams = 2, hd = FV (Named (Id "F")), sp = [Term {nlams = 0, hd = DB 1, sp = [], typ = Typ [] (Id "ord")},Term {nlams = 0, hd = DB 0, sp = [], typ = Typ [] (Id "nat")}], typ = Typ [Typ [] (Id "ord"),Typ [] (Id "nat")] (Id "nat")},Term {nlams = 2, hd = FV (Named (Id "G")), sp = [Term {nlams = 1, hd = DB 2, sp = [Term {nlams = 0, hd = DB 0, sp = [], typ = Typ [] (Id "nat")}], typ = Typ [Typ [] (Id "nat")] (Id "ord")},Term {nlams = 1, hd = DB 1, sp = [Term {nlams = 0, hd = DB 0, sp = [], typ = Typ [] (Id "nat")}], typ = Typ [Typ [] (Id "nat")] (Id "nat")}], typ = Typ [Typ [Typ [] (Id "nat")] (Id "ord"),Typ [Typ [] (Id "nat")] (Id "nat")] (Id "nat")}], typ = Typ [] (Id "nat")}, condition = [(FV (Named (Id "G")),2)]}]

example_26_metafied = Term {nlams = 0, hd = F (Id "rec"), sp = [Term {nlams = 0, hd = FV (Named (Id "H")), sp = [Term {nlams = 0, hd = FV (Fresh 0), sp = [], typ = Typ [] (Id "nat")}], typ = Typ [] (Id "ord")},Term {nlams = 0, hd = FV (Named (Id "K")), sp = [], typ = Typ [] (Id "nat")},Term {nlams = 2, hd = FV (Named (Id "F")), sp = [Term {nlams = 0, hd = DB 1, sp = [], typ = Typ [] (Id "ord")},Term {nlams = 0, hd = DB 0, sp = [], typ = Typ [] (Id "nat")}], typ = Typ [Typ [] (Id "ord"),Typ [] (Id "nat")] (Id "nat")},Term {nlams = 2, hd = FV (Named (Id "G")), sp = [Term {nlams = 1, hd = DB 2, sp = [Term {nlams = 0, hd = DB 0, sp = [], typ = Typ [] (Id "nat")}], typ = Typ [Typ [] (Id "nat")] (Id "ord")},Term {nlams = 1, hd = DB 1, sp = [Term {nlams = 0, hd = DB 0, sp = [], typ = Typ [] (Id "nat")}], typ = Typ [Typ [] (Id "nat")] (Id "nat")}], typ = Typ [Typ [Typ [] (Id "nat")] (Id "ord"),Typ [Typ [] (Id "nat")] (Id "nat")] (Id "nat")}], typ = Typ [] (Id "nat")}

example_29_sdps = [SDP {rule = Equation {lhs = Term {nlams = 0, hd = F (Id "rec#"), sp = [Term {nlams = 0, hd = F (Id "s"), sp = [Term {nlams = 0, hd = FV (Named (Id "X")), sp = [], typ = Typ [] (Id "ord")}], typ = Typ [] (Id "ord")},Term {nlams = 0, hd = FV (Named (Id "K")), sp = [], typ = Typ [] (Id "nat")},Term {nlams = 2, hd = FV (Named (Id "F")), sp = [Term {nlams = 0, hd = DB 1, sp = [], typ = Typ [] (Id "ord")},Term {nlams = 0, hd = DB 0, sp = [], typ = Typ [] (Id "nat")}], typ = Typ [Typ [] (Id "ord"),Typ [] (Id "nat")] (Id "nat")},Term {nlams = 2, hd = FV (Named (Id "G")), sp = [Term {nlams = 1, hd = DB 2, sp = [Term {nlams = 0, hd = DB 0, sp = [], typ = Typ [] (Id "nat")}], typ = Typ [Typ [] (Id "nat")] (Id "ord")},Term {nlams = 1, hd = DB 1, sp = [Term {nlams = 0, hd = DB 0, sp = [], typ = Typ [] (Id "nat")}], typ = Typ [Typ [] (Id "nat")] (Id "nat")}], typ = Typ [Typ [Typ [] (Id "nat")] (Id "ord"),Typ [Typ [] (Id "nat")] (Id "nat")] (Id "nat")}], typ = Typ [] (Id "nat")}, rhs = Term {nlams = 0, hd = F (Id "rec#"), sp = [Term {nlams = 0, hd = FV (Named (Id "X")), sp = [], typ = Typ [] (Id "ord")},Term {nlams = 0, hd = FV (Named (Id "K")), sp = [], typ = Typ [] (Id "nat")},Term {nlams = 2, hd = FV (Named (Id "F")), sp = [Term {nlams = 0, hd = DB 1, sp = [], typ = Typ [] (Id "ord")},Term {nlams = 0, hd = DB 0, sp = [], typ = Typ [] (Id "nat")}], typ = Typ [Typ [] (Id "ord"),Typ [] (Id "nat")] (Id "nat")},Term {nlams = 2, hd = FV (Named (Id "G")), sp = [Term {nlams = 1, hd = DB 2, sp = [Term {nlams = 0, hd = DB 0, sp = [], typ = Typ [] (Id "nat")}], typ = Typ [Typ [] (Id "nat")] (Id "ord")},Term {nlams = 1, hd = DB 1, sp = [Term {nlams = 0, hd = DB 0, sp = [], typ = Typ [] (Id "nat")}], typ = Typ [Typ [] (Id "nat")] (Id "nat")}], typ = Typ [Typ [Typ [] (Id "nat")] (Id "ord"),Typ [Typ [] (Id "nat")] (Id "nat")] (Id "nat")}], typ = Typ [] (Id "nat")}, isRule = True}, sdpCondition = [(FV (Named (Id "F")),2)]},SDP {rule = Equation {lhs = Term {nlams = 0, hd = F (Id "rec#"), sp = [Term {nlams = 0, hd = F (Id "lim"), sp = [Term {nlams = 1, hd = FV (Named (Id "H")), sp = [Term {nlams = 0, hd = DB 0, sp = [], typ = Typ [] (Id "nat")}], typ = Typ [Typ [] (Id "nat")] (Id "ord")}], typ = Typ [] (Id "ord")},Term {nlams = 0, hd = FV (Named (Id "K")), sp = [], typ = Typ [] (Id "nat")},Term {nlams = 2, hd = FV (Named (Id "F")), sp = [Term {nlams = 0, hd = DB 1, sp = [], typ = Typ [] (Id "ord")},Term {nlams = 0, hd = DB 0, sp = [], typ = Typ [] (Id "nat")}], typ = Typ [Typ [] (Id "ord"),Typ [] (Id "nat")] (Id "nat")},Term {nlams = 2, hd = FV (Named (Id "G")), sp = [Term {nlams = 1, hd = DB 2, sp = [Term {nlams = 0, hd = DB 0, sp = [], typ = Typ [] (Id "nat")}], typ = Typ [Typ [] (Id "nat")] (Id "ord")},Term {nlams = 1, hd = DB 1, sp = [Term {nlams = 0, hd = DB 0, sp = [], typ = Typ [] (Id "nat")}], typ = Typ [Typ [] (Id "nat")] (Id "nat")}], typ = Typ [Typ [Typ [] (Id "nat")] (Id "ord"),Typ [Typ [] (Id "nat")] (Id "nat")] (Id "nat")}], typ = Typ [] (Id "nat")}, rhs = Term {nlams = 0, hd = F (Id "rec#"), sp = [Term {nlams = 0, hd = FV (Named (Id "H")), sp = [Term {nlams = 0, hd = FV (Fresh 0), sp = [], typ = Typ [] (Id "nat")}], typ = Typ [] (Id "ord")},Term {nlams = 0, hd = FV (Named (Id "K")), sp = [], typ = Typ [] (Id "nat")},Term {nlams = 2, hd = FV (Named (Id "F")), sp = [Term {nlams = 0, hd = DB 1, sp = [], typ = Typ [] (Id "ord")},Term {nlams = 0, hd = DB 0, sp = [], typ = Typ [] (Id "nat")}], typ = Typ [Typ [] (Id "ord"),Typ [] (Id "nat")] (Id "nat")},Term {nlams = 2, hd = FV (Named (Id "G")), sp = [Term {nlams = 1, hd = DB 2, sp = [Term {nlams = 0, hd = DB 0, sp = [], typ = Typ [] (Id "nat")}], typ = Typ [Typ [] (Id "nat")] (Id "ord")},Term {nlams = 1, hd = DB 1, sp = [Term {nlams = 0, hd = DB 0, sp = [], typ = Typ [] (Id "nat")}], typ = Typ [Typ [] (Id "nat")] (Id "nat")}], typ = Typ [Typ [Typ [] (Id "nat")] (Id "ord"),Typ [Typ [] (Id "nat")] (Id "nat")] (Id "nat")}], typ = Typ [] (Id "nat")}, isRule = True}, sdpCondition = [(FV (Named (Id "G")),2)]}]

example_47_scc = [[SDP {rule = Equation {lhs = Term {nlams = 0, hd = F (Id "map#"), sp = [Term {nlams = 1, hd = FV (Named (Id "Z")), sp = [Term {nlams = 0, hd = DB 0, sp = [], typ = Typ [] (Id "nat")}], typ = Typ [Typ [] (Id "nat")] (Id "nat")},Term {nlams = 0, hd = F (Id "cons"), sp = [Term {nlams = 0, hd = FV (Named (Id "H")), sp = [], typ = Typ [] (Id "nat")},Term {nlams = 0, hd = FV (Named (Id "T")), sp = [], typ = Typ [] (Id "list")}], typ = Typ [] (Id "list")}], typ = Typ [] (Id "list")}, rhs = Term {nlams = 0, hd = F (Id "map#"), sp = [Term {nlams = 1, hd = FV (Named (Id "Z")), sp = [Term {nlams = 0, hd = DB 0, sp = [], typ = Typ [] (Id "nat")}], typ = Typ [Typ [] (Id "nat")] (Id "nat")},Term {nlams = 0, hd = FV (Named (Id "T")), sp = [], typ = Typ [] (Id "list")}], typ = Typ [] (Id "list")}, isRule = True}, sdpCondition = []}]]

parseFileForTest :: FilePath -> IO (Int,[Sort],FunTypMap,Bool,Bool,ES,ES)
parseFileForTest path = do
    input <- TIO.readFile path
    
    let result = processInput path input HRS False False False (parseProblem scARI (ARI.parser))
    
    case result of
        Left e  -> fail $ "Failed to parse test file " ++ path ++ ": " ++ show e
        Right r -> return r


spec_Candidate :: Spec
spec_Candidate = describe "Candidate Unit Tests" $ do
    let testCases = 
            [("./examples/afp/example8.ari", example_8_result)]
    
    forM_ testCases $ \(path, expected) -> 
        it ("computes candidates for" ++ path) $ do
            (_, _, _, _, _, hrs, _) <- parseFileForTest path
            let candidateResult = candidates (rhs $ last hrs) [] (buildMinarMap hrs) (definedSymbols hrs)
            candidateResult `shouldBe` expected

spec_Metafy :: Spec
spec_Metafy = describe "Metafy Unit Tests" $ do
    let t = term $ head example_8_result
    let result = evalState (metafy t) 0
    it "Compute Example 26 metafied" $ do
        result `shouldBe` example_26_metafied

spec_SDP :: Spec
spec_SDP = describe "SDP Unit Tests" $ do

  describe "example8.ari" $ do
    sdps <- runIO $ do
        (_, _, _, _, _, hrs, _) <- parseFileForTest "./examples/afp/example8.ari"
        pure (runStaticDependencyPairs hrs)

    it "produces exactly two SDPs" $
        length sdps `shouldBe` 2

    it "produces the correct SDPs" $
        sdps `shouldBe` example_29_sdps


spec_Graph :: Spec
spec_Graph = describe "Dependency Graph Unit Tests" $ do
    describe "example6.ari" $ do
        sdps <- runIO $ do
            (_, _, _, _, _, hrs, _) <- parseFileForTest "./examples/afp/example6_2.ari"
            pure (runStaticDependencyPairs hrs)
        
        let computedSCCs = nonTrivialSCCs sdps
        
        it "produces three SDPs" $
            length sdps `shouldBe` 3
        
        it "has exactly one SCC" $
            length computedSCCs `shouldBe` 1

        it "computes the SCC correctly" $
            computedSCCs `shouldBe` example_47_scc



dpSpecs :: Spec
dpSpecs = describe "DP" $ do
  spec_Candidate
  spec_Metafy
  spec_SDP
  spec_Graph