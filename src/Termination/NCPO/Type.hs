{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

-- |types for NCPO
module Termination.NCPO.Type where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import qualified Language.Hasmtlib as SMT
import Prettyprinter (Pretty,pretty)

import Utils.Type (Id(..),Accessor(..))
import Utils.SMT (Constraint)
import Typ.Type (Sort)

-- |type class which can differentiate between lexicographic/multiset status
class IsStatus a where
  isLex :: a -> Constraint
  isMul :: a -> Constraint

-- |Different types of argument orderings (lexicographic and multiset).
data ArgOrd = Lex | Mul deriving Eq

instance SMT.Equatable ArgOrd where
  (===) Lex Lex = SMT.true
  (===) Mul Mul = SMT.true
  (===) _ _ = SMT.false

instance IsStatus ArgOrd where
  isLex x = SMT.bool (x == Lex)
  isMul x = SMT.bool (x == Mul)

instance IsStatus (SMT.Expr SMT.BoolSort) where
  isLex x = x SMT.=== SMT.false
  isMul x = x SMT.=== SMT.true

instance Pretty ArgOrd where
  pretty Lex = "lex"
  pretty Mul = "mul"

-- |the status of a constant implemented as a map
newtype Status a = Stat (Map Id a)

-- |the precedence of a function symbol implemented as a map
newtype Precedence a = Prec (Map Id a) deriving (Foldable,Functor,Traversable)

-- |precedence for sorts
type SortPrecedence a = Precedence a

-- |basic sorts
newtype Basic a = Basic (Map Id a) deriving (Foldable,Functor,Traversable)

-- |accessible arguments
newtype Acc a = Acc (Map (Id,Int) a) deriving (Foldable,Functor,Traversable)

instance Accessor Status where
  type AccessorKey Status = Id
  (Stat m) ! k = m M.! k

instance Accessor Precedence where
  type AccessorKey Precedence = Id
  (Prec m) ! k = m M.! k

instance Accessor Basic where
  type AccessorKey Basic = Id
  (Basic m) ! k = m M.! k

instance Accessor Acc where
  type AccessorKey Acc = (Id,Int)
  (Acc m) ! k = m M.! k

instance SMT.Codec (Status (SMT.Expr SMT.BoolSort)) where
  type Decoded (Status (SMT.Expr SMT.BoolSort)) = Status ArgOrd
  encode (Stat m) = Stat $ fmap f m where
    f Lex = SMT.false
    f Mul = SMT.true
  decode sol (Stat m) = Stat <$> traverse f m where
    f x = do
      i <- SMT.decode sol x
      case i of
        False -> Just Lex
        True -> Just Mul

instance SMT.Codec a => SMT.Codec (Precedence a) where
  encode = fmap SMT.encode
  decode sol = traverse (SMT.decode sol)

instance SMT.Codec a => SMT.Codec (Basic a) where
  encode = fmap SMT.encode
  decode sol = traverse (SMT.decode sol)

instance SMT.Codec a => SMT.Codec (Acc a) where
  encode = fmap SMT.encode
  decode sol = traverse (SMT.decode sol)

-- |type precedence, status of constants, constant precedence , list of sorts, list of constants,
-- map for basic and accessible information bundled into a record data type.
data CPOInfo a b = CPOInfo { sorts :: [Sort]
                           , sPrec :: SortPrecedence a
                           , stat :: Status b
                           , fPrec :: Precedence a
                           , isBasic :: Basic Constraint
                           , isAccessible :: Acc Constraint
                           }

type CPOSolution = ( SortPrecedence Integer
                   , Status ArgOrd
                   , Precedence Integer
                   , Basic Bool
                   , Acc Bool
                   )                   
