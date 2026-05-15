{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}

-- |solver for NCPO
module Termination.NCPO.Solver where

import Prelude hiding ((&&),(||),and,or,not)

import Control.Monad.Trans.State (evalState)
import Data.Default (def)
import Data.List (groupBy,sortBy,partition)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Language.Hasmtlib as SMT
import Language.Hasmtlib (Orderable(..),Boolean(..),and)
import Prettyprinter (line,vsep,hsep,pretty,(<+>),Doc,line,punctuate,hsep,encloseSep)

import Utils.Type (Id(..),Accessor(..))
import Utils.SMT (SMTSolver(..),Constraint,smtVarMap)
import Typ.Type (Typ(..),Sort)
import Typ.Ops (arity,posOf,posPos)
import Term.Type (FunTypMap)
import Equation.Type (Equation(..),ES)
import Termination.NCPO.Type
import Termination.NCPO.Ordering (ncpoWrapper)

-- |result of termination proof attempt by NCPO
data NCPORes = NCPORes
  { status :: Bool
  , mSol :: Maybe CPOSolution
  }

-- |Converts a sort precedence to an easily printable list representation
-- (a list of lists of equivalent elements in decreasing order)
sPrecToList :: Ord a => SortPrecedence a -> [[Id]]
sPrecToList (Prec m) = map (map fst) $ groupBy (\x y -> snd x == snd y)
  (sortBy (\x y -> compare (snd y) (snd x)) (M.assocs m))

-- |Converts a constant precedence to an easily printable list representation
-- (a list of list of lists of equivalent elements in decreasing order)
-- the outermost list layer is needed such that constants with different stati
-- are not considered to be equivalent in the precedence.
fPrecToLists :: Ord a => Precedence a -> Status ArgOrd -> [[[Id]]]
fPrecToLists (Prec m) (Stat stm) = f iRepr where
  iRepr = map (partition stateIsLex . map fst) $ groupBy (\x y -> snd x == snd y)
    (sortBy (\x y -> compare (snd y) (snd x)) (M.assocs m))
  stateIsLex x = stm M.! x == Lex
  f (([],[]):_) = error "impossible case"
  f ((as,[]):rest) = do
    xss <- f rest
    pure $ as : xss
  f (([],bs):rest) = do
    xss <- f rest
    pure $ bs : xss
  f ((as,bs):rest) = do
    cs <- [as,bs]
    xss <- f rest
    pure $ cs : xss
  f [] = [[]]

-- |Determines whether all base type occuring in a type are
-- less than or equal than a given base type.
sortLeq :: Orderable a => SortPrecedence a -> Id -> Typ -> Constraint
sortLeq sortPrec a (Typ bs b) = sortPrec ! a >=? sortPrec ! b && and (map (sortLeq sortPrec a) bs)

-- |Generates the condition for an argument of a constant is accessible.
accessibleCond :: Orderable a => CPOInfo a b -> Id -> Int -> Typ -> Id -> Constraint
accessibleCond cpoInfo f i a b =
  not (isAccessible cpoInfo ! (f,i)) ||
  (bool (posOf b a `S.isSubsetOf` posPos a) && sortLeq (sPrec cpoInfo) b a)

-- |Generates the condition for a sort to be basic.
basicCond :: Orderable a => CPOInfo a b -> [Id] -> FunTypMap -> Id -> Constraint
basicCond cpoInfo fs fTyps c = not (basic ! c) ||
  (and . map (\b -> not (sortPrec ! b <? sortPrec ! c) || basic ! c) . filter (/= c) $ ss) &&
  (and . map fun $ relevantAccs)
  where
    (ss,sortPrec,basic,acc) = (sorts cpoInfo,sPrec cpoInfo,isBasic cpoInfo,isAccessible cpoInfo)
    fun (f,Typ [] c',i) = not (acc ! (f,i)) || bool (c == c') || basic ! c'
    fun (f,_,i) = not (acc ! (f,i))
    relevantAccs = [(f,a,i) | f <- fs, (Typ as c') <- [fTyps M.! f], c == c', (a,i) <- zip as [0..]]

-- |Check termination of an HRS using NHORPO
checkTermination :: SMTSolver -> Bool -> [Sort] -> FunTypMap -> ES -> IO NCPORes
checkTermination (Solver _ s _) debug ss fTyps hrs = do
  let fs = M.keys fTyps
  (res,msol) <- SMT.solveWith (if debug then SMT.solver (SMT.debugging def s) else SMT.solver s) $ do
    SMT.setLogic "ALL"
    sortPrec <- Prec <$> smtVarMap @SMT.IntSort ss
    basic <- Basic <$> smtVarMap @SMT.BoolSort ss
    st <- Stat <$> smtVarMap @SMT.BoolSort fs
    funPrec <- Prec <$> smtVarMap @SMT.IntSort fs
    accessible <- Acc <$> smtVarMap @SMT.BoolSort [ (f,i)
                                                  | f <- fs, i <- [0..(arity $ fTyps M.! f) - 1]]
    let cpoinfo = CPOInfo { sorts = ss
                          , sPrec = sortPrec
                          , stat = st
                          , fPrec = funPrec
                          , isBasic = basic
                          , isAccessible = accessible
                          }
    mapM_ (SMT.assert . basicCond cpoinfo fs fTyps) ss
    mapM_ SMT.assert [accessibleCond cpoinfo f i a b
                     | f <- fs, Typ as b <- [fTyps M.! f], (a,i) <- zip as [0..]]
    let constraints = evalState (mapM (\e -> ncpoWrapper cpoinfo (lhs e) (rhs e)) hrs) 0
    mapM_ SMT.assert constraints
    return (sortPrec,st,funPrec,basic,accessible)
  let boolRes = case res of
        SMT.Sat -> True
        SMT.Unsat -> False
        SMT.Unknown -> False
  return $ NCPORes { status = boolRes, mSol = msol }

-- |Print the result of a solution attempt to a termination check using NCPO.
resultDoc :: NCPORes -> ES -> Doc ann
resultDoc res hrs = let
    prettySortPrec prec =
      hsep . punctuate " >" $ [ hsep . punctuate " ~" $ [pretty idt | idt <- eqs]
                              | eqs <- sPrecToList prec]
    prettyFunPrec prec st = vsep
      [hsep . punctuate " >" $ [ hsep . punctuate " ~" $ [pretty idt | idt <- eqs]
                               | eqs <- precedence]
      | precedence <- fPrecToLists prec st]
    prettyStatus (Stat m) = vsep $ map (\(idt,s) -> pretty idt <> ":" <+> pretty s) (M.assocs m)
    prettyBasic (Basic m) = hsep . map pretty . M.keys . M.filter id $ m
    prettyAcc (Acc m) =
      vsep [pretty c <> ":" <+> encloseSep "{" "}" "," (map pretty (i:map snd xs))
           | ((c,i):xs) <- groupBy (\x y -> fst x == fst y) . M.keys . M.filter id $ m]
    inputHRS = line <> "input HRS:" <> line <> line <> vsep (map pretty hrs)
  in case mSol res of
    Just (sortPrec,st,funPrec,basic,acc) -> inputHRS <> line <> line <>
      "status:" <> line <> line <>  prettyStatus st <> line <> line <>
      "sort precedence:" <> line <> line <> prettySortPrec sortPrec <> line <> line <>
      "function symbol precedence:" <> line <> line <> prettyFunPrec funPrec st <> line <> line <>
      "basic sorts:" <> line <> line <> prettyBasic basic <> line <> line <>
      "accessible arguments:" <> line <> line <> prettyAcc acc <> line <> line
    Nothing -> inputHRS <> line <> line
