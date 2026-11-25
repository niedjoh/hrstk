{-# LANGUAGE OverloadedStrings #-}

module DuplicateChecker where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Utils.Type (Id(..))
import Typ.Type (Typ(..))
import Term.Type (FunTypMap)

type TypSkeletonFunsMap = Map Typ [Id]

toSkeleton :: Typ -> Typ
toSkeleton (Typ as _) = Typ (map toSkeleton as) (Id "_")

toTypSkeletonFunsMap :: FunTypMap -> TypSkeletonFunsMap
toTypSkeletonFunsMap fTyM = M.fromListWith (++) vks where
  vks = map (\(f,a) -> (toSkeleton a, [f])) . M.toList $ fTyM

