{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Termination where

import Data.Kind (Type)
import Data.Singletons.TH
import Prettyprinter (Doc)

import Utils.SMT (SMTSolver)
import Term.Type (FunTypMap)
import Equation.Type (ES)
import Equation.Ops (secondOrderEq)
import Typ.Type (Sort)
import qualified Termination.NCPO as NCPO
import qualified Termination.Poly as Poly
import qualified Termination.StarCPO as StarCPO

$(singletons [d|
  data TermMethod = NCPO | Poly | StarCPO
  |])

instance Show TermMethod where
  show NCPO = "ncpo"
  show Poly = "poly"
  show StarCPO = "starcpo"

type family TermRes (a :: TermMethod) where
  TermRes NCPO = NCPO.NCPORes
  TermRes StarCPO = StarCPO.CPORes
  TermRes Poly = Poly.PolyIntRes

data SomeTermRes :: Type where
  MkSomeTermRes :: Sing a -> TermRes a -> SomeTermRes

terminationStatus :: SomeTermRes -> Bool
terminationStatus (MkSomeTermRes SNCPO res) = NCPO.status res
terminationStatus (MkSomeTermRes SPoly res) = Poly.status res
terminationStatus (MkSomeTermRes SStarCPO res) = StarCPO.status res

checkTermination :: TermMethod -> SMTSolver -> Bool -> [Sort] -> FunTypMap -> ES -> IO SomeTermRes
checkTermination NCPO s d bts fTyM hrs = MkSomeTermRes SNCPO <$> NCPO.checkTermination s d bts fTyM hrs
checkTermination StarCPO s d bts fTyM hrs = MkSomeTermRes SStarCPO <$> StarCPO.checkTermination s d bts fTyM hrs
checkTermination Poly s d _ fTyM hrs
  | all secondOrderEq hrs = MkSomeTermRes SPoly <$> Poly.checkTermination s d fTyM hrs
  | otherwise             = pure $ MkSomeTermRes SPoly $ Poly.failRes

terminationResultDoc :: SomeTermRes -> Doc ann
terminationResultDoc (MkSomeTermRes SNCPO res) = NCPO.resultDoc res
terminationResultDoc (MkSomeTermRes SStarCPO res) = StarCPO.resultDoc res
terminationResultDoc (MkSomeTermRes SPoly res) = Poly.resultDoc res

terminationStrategy :: [TermMethod] -> SMTSolver -> Bool -> [Sort] -> FunTypMap -> ES -> IO SomeTermRes
terminationStrategy [] _ _ _ _ _ = pure $ MkSomeTermRes SNCPO $ NCPO.failRes
terminationStrategy (tm:tms) s d bts fTyM hrs = do
  res <- checkTermination tm s d bts fTyM hrs
  if terminationStatus res
    then pure res
    else terminationStrategy tms s d bts fTyM hrs
  
  



