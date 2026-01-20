{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}

-- |utility type declarations
module Utils.Type where

import Data.Text (Text)
import Prettyprinter (Pretty,pretty)

-- |newtype wrapper for 'Text'-based identifiers
newtype Id = Id Text deriving (Eq,Ord,Show,Pretty)

-- |Variables are either named or fresh variables which are referenced by a unique integer.
data Var = Named Id | Fresh Int deriving (Eq,Ord,Show)

instance Pretty Var where
  pretty (Named idt) = pretty idt
  pretty (Fresh i) = pretty ("?" :: Text) <> pretty i

-- |type class which lifts the map accessor function accordingly
class Accessor a where
  type AccessorKey a
  (!) :: a b -> AccessorKey a -> b

infixl 9 !
