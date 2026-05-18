{-# LANGUAGE OverloadedStrings #-}

module NCPOSpec (ncpoSpecs) where

import Prelude hiding ((&&),(||),and,or,not)

import Control.Monad.State (evalState)
import Control.Monad.Trans.Reader (runReaderT)

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Language.Hasmtlib (true,false)
import Test.Hspec (Spec, describe, it, shouldBe)

import qualified Predefined.Sort as Sort
import qualified Predefined.Typ as Typ 
import qualified Predefined.DB as DB
import qualified Predefined.Var as Var
import qualified Predefined.Fun as Fun

import Utils.Type (Id(..),Var(..))
import Term.Ops (mkTerm)
import Termination.NCPO.Type
import Termination.NCPO.Ordering

spec_ncpo :: Spec
spec_ncpo =
  describe "ncpo" $ do
    let cpoinfo = CPOInfo { sorts = [Sort.a]
                          , sPrec = Prec $ M.fromList [(Sort.a,0 :: Int)]
                          , stat = Stat $ M.fromList [(Id "f",Lex),(Id "g",Lex)]
                          , fPrec = Prec $ M.fromList [(Id "f",0),(Id "g",1)]
                          , isBasic = Basic $ M.fromList [(Sort.a,false)]
                          , isAccessible = Acc $ M.fromList [ ((Id "f",0),false)
                                                            , ((Id "g",0),false)
                                                            , ((Id "g",1),false)
                                                            ]
                          }
        comp vars c s t = evalState (runReaderT (ncpo False c vars s t) cpoinfo) 0        
        s1 = mkTerm Fun.f Typ.aa [ mkTerm Var.x Typ.a [ mkTerm DB.zero Typ.a [] ] ]
        t1 = mkTerm Var.x Typ.aa [ mkTerm DB.zero Typ.a [] ]
        s2 = mkTerm Fun.g Typ.a [ s1, mkTerm Var.y Typ.a [] ]
        t2 = mkTerm Fun.g Typ.a [ t1, mkTerm Var.z Typ.a [] ]
        u1 x = mkTerm x Typ.aa [ mkTerm DB.zero Typ.a [] ]
        u1' x y = mkTerm x Typ.a [ mkTerm y Typ.a [] ]
        u2 x = mkTerm Fun.f Typ.a [ u1 x ]
    it "is not reflexive" $
      comp S.empty Compare s1 s1 `shouldBe` false
    it "computes an example correctly" $
      comp (S.singleton (Named . Id $ "z",Typ.a)) NoCompare s2 t2 `shouldBe` true
    it "computes another example correctly" $
      comp (S.singleton (Named . Id $ "z",Typ.a)) NoCompare (u2 Var.x) (u1' Var.x Var.z)  `shouldBe` true
ncpoSpecs :: Spec
ncpoSpecs = describe "Termination.NCPO.Ordering" $ do
  spec_ncpo
