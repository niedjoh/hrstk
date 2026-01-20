{-# LANGUAGE OverloadedStrings #-}

-- |types for module Subst
module Subst.Type where

import Data.Map.Strict (Map)
import Data.Map.Strict (assocs)
import Prettyprinter (Pretty,pretty,list,(<+>))

import Utils.Type (Var)
import Term.Type (Term)

-- |List of singleton substitutions. Intermediate datatype for matching.
type SubstL = [(Var,Term)]

-- |newtype wrapper for maps from variables to terms
newtype Subst = Subst (Map Var Term) deriving (Eq,Show)

instance Pretty Subst where
  pretty (Subst m) = list . map prettyEntry . assocs $ m where
    prettyEntry (v,t) = pretty v <+> "⟼" <+> pretty t
