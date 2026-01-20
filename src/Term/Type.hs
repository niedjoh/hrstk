{-# LANGUAGE OverloadedStrings #-}

-- |Types for module Term
module Term.Type where

import Data.Map (Map)
import Prettyprinter (Pretty,pretty,tupled,punctuate,comma,hcat,emptyDoc,align)

import Utils.Type (Id,Var)
import Typ.Type (Typ(..))

-- |De Brujin indices in tuple form
type DB = (Int,Typ)

-- |Positions in terms
type Pos = [Int]

-- |Terms are simply-typed lambda terms in lnf with full local type information.
data Term = Term { nlams :: Int, hd :: Head, sp :: [Term], typ :: Typ} deriving (Eq,Ord,Show)
data Head = F Id | FV Var | DB Int deriving (Eq,Ord,Show)

-- |Contexts are implemented as Haskell functions from terms to terms.
type Context = Term -> Term

-- |Subterms consist of a context, a bound variable context, a position and the subterm itself
type Subterm = (Context,[Typ],Pos,Term)

-- |A map from constant identifiers to types
type FunTypMap = Map Id Typ

instance Pretty Term where
  pretty = go [] (0 :: Int) where
    prettyHd (F idt) _ = pretty idt
    prettyHd (FV v) _ = pretty v
    prettyHd (DB i) ctx
      | i < 0          = error "negative DB"
      | i < length ctx = ctx !! i
      | otherwise      = error "dangling DB"
    prettyAbs k vars
      | k > 0     = hcat (punctuate comma vars)  <> "."
      | otherwise = emptyDoc
    go ctx d s = prettyAbs k vars <> prettyHd (hd s) ctx' <>
      if null (sp s) then emptyDoc else (align . tupled $ map (go ctx' d') (sp s)) where
        k = nlams s
        vars = ["x" <> pretty i | i <- [d..d+k-1]]
        ctx' = reverse vars ++ ctx
        d' = d+k
      
