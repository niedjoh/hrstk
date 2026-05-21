{-# LANGUAGE OverloadedStrings #-}

module Confluence where

import Prettyprinter (Doc,emptyDoc)

import Utils.SMT (SMTSolver)
import Typ.Type (Sort)
import Term.Type (FunTypMap)
import Equation.Type (CriticalPair,ES)
import Equation.Ops (leftLinear,patternRule)
import qualified Equation.CriticalPairs as CP
import Equation.Rewriting as RW
import Termination (TermMethod(..),terminationStrategy,terminationStatus,terminationResultDoc)

data ConfStatus = CYes | CNo | CMaybe

instance Show ConfStatus where
  show CYes = "YES"
  show CNo = "NO"
  show CMaybe = "MAYBE"

data ConfMethod = OR | DC | LC | KB

instance Show ConfMethod where
  show LC = "local confluence"
  show OR = "orthogonality"
  show DC = "development closedness"
  show KB = "Knuth-Bendix criterion"

data ConfResult ann = ConfResult { status :: ConfStatus, resultDoc :: Doc ann }

maybeRes :: ConfResult ann
maybeRes = ConfResult { status = CMaybe
                      , resultDoc = emptyDoc
                      }

failRes :: ConfResult ann
failRes = ConfResult { status = CNo
                     , resultDoc = emptyDoc
                     }

checkConfluence :: ConfMethod -> SMTSolver -> Bool -> [Sort] -> FunTypMap -> ES -> [CriticalPair] -> IO (ConfResult ann)
checkConfluence OR _ _ _ _ dprs cpairs
  | all leftLinear dprs && null cpairs = pure $ ConfResult { status = CYes, resultDoc = "\n\northogonal" }
  | otherwise = pure maybeRes
checkConfluence DC _ _ _ _ dprs cpairs
  | all (\e -> leftLinear e && patternRule e) dprs =
       pure $ ConfResult { status = if CP.checkMSJoinability dprs cpairs then CYes else CMaybe
                         , resultDoc = CP.resultDocJoinable "development closedness tests:" RW.msJoinabilityDoc dprs cpairs
                         }
  | otherwise = pure maybeRes
checkConfluence LC _ _ _ _ dprs cpairs =
  pure $ ConfResult { status = if CP.checkJoinability dprs cpairs then CYes else CNo
                    , resultDoc = CP.resultDocJoinable "joinability tests:" RW.joinabilityDoc dprs cpairs
                    }
checkConfluence KB s d bts fTyM dprs cpairs = do
  lcRes <- checkConfluence LC s d bts fTyM dprs cpairs
  case confluenceStatus lcRes of
    CYes -> do
      termRes <- terminationStrategy [NCPO,Poly] s d bts fTyM dprs
      if terminationStatus termRes
        then pure $ ConfResult { status = CYes
                               , resultDoc = resultDoc lcRes <> terminationResultDoc termRes
                               }
        else pure $ ConfResult { status = CMaybe
                               , resultDoc = resultDoc lcRes <> "\n\n no termination proof found"
                               }
    _ -> pure lcRes

confluenceStatus :: ConfResult ann -> ConfStatus
confluenceStatus = status

confluenceResultDoc :: ConfResult ann -> Doc ann
confluenceResultDoc = resultDoc

confluenceStrategy :: [ConfMethod] -> SMTSolver -> Bool -> [Sort] -> FunTypMap -> ES -> [CriticalPair] -> IO (ConfResult ann)
confluenceStrategy [] _ _ _ _ _ _ = pure maybeRes
confluenceStrategy (cm:cms) s d bts fTyM dprs cpairs = do
  res <- checkConfluence cm s d bts fTyM dprs cpairs
  case confluenceStatus res of
    CYes -> return res
    CNo -> return res
    CMaybe -> confluenceStrategy cms s d bts fTyM dprs cpairs
      

      
