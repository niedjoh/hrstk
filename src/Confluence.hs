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


data ConfMethod = OR | DC | LC | KB

instance Show ConfMethod where
  show LC = "local confluence"
  show OR = "orthogonality"
  show DC = "development closedness"
  show KB = "Knuth-Bendix criterion"

data ConfResult ann = ConfResult { status :: Bool, resultDoc :: Doc ann }

failRes :: ConfResult ann
failRes = ConfResult { status = False
                     , resultDoc = emptyDoc
                     }

checkConfluence :: ConfMethod -> SMTSolver -> Bool -> [Sort] -> FunTypMap -> ES -> [CriticalPair] -> IO (ConfResult ann)
checkConfluence OR _ _ _ _ dprs cpairs
  | all leftLinear dprs && null cpairs = pure $ ConfResult { status = True, resultDoc = "\n\northogonal" }
  | otherwise = pure failRes
checkConfluence DC _ _ _ _ dprs cpairs
  | all (\e -> leftLinear e && patternRule e) dprs =
       pure $ ConfResult { status = CP.checkMSJoinability dprs cpairs
                         , resultDoc = CP.resultDocJoinable "development closedness tests:" RW.msJoinabilityDoc dprs cpairs
                         }
  | otherwise = pure failRes
checkConfluence LC _ _ _ _ dprs cpairs =
  pure $ ConfResult { status = CP.checkJoinability dprs cpairs
                    , resultDoc = CP.resultDocJoinable "joinability tests:" RW.joinabilityDoc dprs cpairs
                    }
checkConfluence KB s d bts fTyM dprs cpairs = do
  lcRes <- checkConfluence LC s d bts fTyM dprs cpairs
  if confluenceStatus lcRes
    then do
      termRes <- terminationStrategy [NCPO,Poly] s d bts fTyM dprs
      if terminationStatus termRes
        then pure $ ConfResult { status = True
                               , resultDoc = resultDoc lcRes <> terminationResultDoc termRes
                               }
        else pure $ ConfResult { status = False
                               , resultDoc = resultDoc lcRes <> "\n\n no termination proof found"
                               }
    else pure lcRes

confluenceStatus :: ConfResult ann -> Bool
confluenceStatus = status

confluenceResultDoc :: ConfResult ann -> Doc ann
confluenceResultDoc = resultDoc

confluenceStrategy :: [ConfMethod] -> SMTSolver -> Bool -> [Sort] -> FunTypMap -> ES -> [CriticalPair] -> IO (ConfResult ann)
confluenceStrategy [] _ _ _ _ _ _ = pure failRes
confluenceStrategy (cm:cms) s d bts fTyM dprs cpairs = do
  res <- checkConfluence cm s d bts fTyM dprs cpairs
  if confluenceStatus res
    then return res
    else confluenceStrategy cms s d bts fTyM dprs cpairs
