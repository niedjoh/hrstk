{-# LANGUAGE OverloadedStrings #-}

module PolySpec (polySpecs) where

import Test.Hspec (Spec, describe, it, shouldBe)

import qualified Data.Map.Strict as M
import qualified Data.MultiSet as MS
import Data.Text (Text)

import Utils.Type (Id(..),Var(..))
import Termination.Poly.Type
import Termination.Poly.Interpretation

pvar :: Text -> PVar
pvar = PFV . Named . Id 

spec_polyMul :: Spec
spec_polyMul =
  describe "polynomial multiplication" $ do
    let p1 = Poly $ M.fromList [ (MS.fromOccurList [(pvar "x",1),(pvar "z",1)],1 :: Int)
                               , (MS.fromOccurList [(pvar "y",2)],3)
                               ]
        p2 = Poly $ M.fromList [ (MS.fromOccurList [(pvar "x",2),(pvar "y",2)],2)
                               , (MS.fromOccurList [(pvar "y",1),(pvar "z",1)],1)
                               ]
        res1 = Poly $ M.fromList [ (MS.fromOccurList [(pvar "x",3),(pvar "y",2),(pvar "z",1)],2)
                                 , (MS.fromOccurList [(pvar "x",1),(pvar "y",1),(pvar "z",2)],1)
                                 , (MS.fromOccurList [(pvar "x",2),(pvar "y",4)],6)
                                 , (MS.fromOccurList [(pvar "y",3),(pvar "z",1)],3)
                                 ]
    it "works on binomial example" $
      p1 * p2 `shouldBe` res1

spec_pBeta :: Spec
spec_pBeta =
  describe "beta-reduction in functional polynomials" $ do
    let par i = Poly $ M.singleton (MS.singleton (Par i)) 1
        fp1 = PLam . PLam . PBase . Poly $ M.singleton (MS.fromOccurList [ (ApplPVar (PDB 1) [],1)
                                                                         , (ApplPVar (PDB 0) [],1) ]
                                                       )
                                                       (par 1)
        fp2 = PLam . PBase . Poly $ M.singleton (MS.fromOccurList [ (ApplPVar (PDB 0) [], 1)
                                                                  , (ApplPVar (PDB 0) [], 1) ]
                                                )
                                                (par 1)
        fp3 = PLam . PBase . Poly $ M.singleton (MS.singleton (ApplPVar (PDB 0) [PBase . Poly $ M.singleton MS.empty (par 3)])) (par 2)
        res1 = PLam . PBase . Poly $ M.singleton (MS.fromOccurList [ (ApplPVar (PDB 0) [],1) ]) (par 1 * par 2)
        res2 = PBase . Poly $ M.singleton MS.empty (par 1 * par 2 * par 3)
        res3 = PBase . Poly $ M.singleton MS.empty (par 1 * par 2 * par 2)
        res4 = PBase . Poly $ M.singleton MS.empty (par 1 * par 2 * par 3)
        res5 = PBase . Poly $ M.singleton MS.empty (par 1 * par 2 * par 3 * par 3)
    it "can do one step" $
      pBeta fp1 (PBase . Poly $ M.singleton MS.empty (par 2)) `shouldBe` res1
    it "can do iterated step" $
      pBeta res1 (PBase . Poly $ M.singleton MS.empty (par 3)) `shouldBe` res2
    it "can do duplicated step" $
      pBeta fp2 (PBase . Poly $ M.singleton MS.empty (par 2)) `shouldBe ` res3
    it "can do HO step" $
      pBeta fp3 (PLam . PBase . Poly $ M.singleton (MS.singleton (ApplPVar (PDB 0) [])) (par 1)) `shouldBe` res4
    it "can do duplicating HO step" $
      pBeta fp3 (PLam . PBase . Poly $ M.singleton (MS.fromOccurList [(ApplPVar (PDB 0) [],2)]) (par 1)) `shouldBe` res5
  

polySpecs :: Spec
polySpecs = describe "Termination.Poly" $ do
  spec_polyMul
  spec_pBeta
