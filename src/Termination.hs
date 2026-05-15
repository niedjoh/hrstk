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
import Typ.Type (Sort)
import qualified Termination.NCPO as NCPO
import qualified Termination.Poly as Poly

$(singletons [d|
  data TermMethod = NCPO | Poly
  |])

instance Show TermMethod where
  show NCPO = "ncpo"
  show Poly = "poly"

type family TermRes (a :: TermMethod) where
  TermRes NCPO = NCPO.NCPORes
  TermRes Poly = Poly.PolyIntRes

data SomeTermRes :: Type where
  MkSomeTermRes :: Sing a -> TermRes a -> SomeTermRes

terminationStatus :: SomeTermRes -> Bool
terminationStatus (MkSomeTermRes SNCPO res) = NCPO.status res
terminationStatus (MkSomeTermRes SPoly res) = Poly.status res

checkTermination :: TermMethod -> SMTSolver -> Bool -> [Sort] -> FunTypMap -> ES -> IO SomeTermRes
checkTermination NCPO s d bts fTyM hrs = MkSomeTermRes SNCPO <$> NCPO.checkTermination s d bts fTyM hrs
checkTermination Poly s d _ fTyM hrs = MkSomeTermRes SPoly <$> Poly.checkTermination s d fTyM hrs

terminationResultDoc :: SomeTermRes -> ES -> Doc ann
terminationResultDoc (MkSomeTermRes SNCPO res) = NCPO.resultDoc res
terminationResultDoc (MkSomeTermRes SPoly res) = Poly.resultDoc res   
    
