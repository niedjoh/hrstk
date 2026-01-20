{-# LANGUAGE OverloadedStrings #-}

-- |types for module Equation
module Equation.Type where

import Term.Type
import Prettyprinter (Pretty,pretty,line,group,nest,(<+>))

-- |An equation is an oriented pair of terms. The flag 'isRule' can be used
-- to distinguish equations from rules of a PRS.
data Equation = Equation {lhs :: Term, rhs :: Term, isRule :: Bool} deriving (Show,Eq)

-- |An equational system (ES) is a collection of equations
type ES = [Equation]

type CriticalPair = (Equation,Pos,Equation,Equation)

instance Pretty Equation where
  pretty e = group $ pretty (lhs e) <+> symb <> nest 2 (line <> pretty (rhs e)) where
    symb = if isRule e then "->" else "="
