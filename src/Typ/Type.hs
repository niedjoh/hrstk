{-# LANGUAGE OverloadedStrings #-}

-- |types for module 'Typ'
module Typ.Type where

import Prettyprinter (Pretty,pretty,tupled,(<+>))

import Utils.Type (Id)

-- |Standard representation of simple types with binary arrow constructor.
data Typ = Typ [Typ] Id deriving (Eq,Ord,Show)

-- |Sorts are identifiers.
type Sort = Id

instance Pretty Typ where
  pretty (Typ [] a) = pretty a
  pretty (Typ [Typ [] b] a) = pretty b <+> ">" <+> pretty a
  pretty (Typ as a) = tupled (map pretty as) <+> ">" <+> pretty a
