{-# LANGUAGE OverloadedStrings #-}

module AfpSpec(afpSpecs) where

import qualified Data.Text.IO as TIO
import Test.Hspec (Spec, describe, it, shouldBe, shouldNotBe)
import qualified ARI
import Equation.Type
import Term.Type
import Typ.Type
import Utils.SMT
import Termination.AFP.Solver
import Utils.Parse
import Utils.InputProcessing
import Control.Monad (forM_)


parseFileForTest :: FilePath -> IO (Int,[Sort],FunTypMap,Bool,Bool,ES,ES)
parseFileForTest path = do
    input <- TIO.readFile path
    
    let result = processInput path input HRS False False False (parseProblem scARI (ARI.parser))
    
    case result of
        Left e  -> fail $ "Failed to parse test file " ++ path ++ ": " ++ show e
        Right r -> return r

spec_Afp :: Spec
spec_Afp =
  describe "AFP Constraints Integration Tests" $ do
  let testCases = 
       [ ("./examples/afp/notAFP.ari", False)
       , ("./examples/afp/example6.ari", True)
       , ("./examples/afp/example8.ari", True)
       , ("./examples/afp/example17.ari", True)
       , ("./examples/afp/noFVonRHS.ari", True)
       , ("./examples/afp/notAFP2.ari", False)
       , ("./examples/afp/notAFP3.ari", False)]

  forM_ testCases $ \(path, expected) -> 
    it ("computes " ++ path ++ " correctly") $ do
      (_, sorts, _, _, _, hrs, _) <- parseFileForTest path
      afpResult <- checkAFP cvc5 sorts hrs
      afpResult `shouldBe` expected



afpSpecs :: Spec
afpSpecs = describe "AFP" $ do
  spec_Afp