{-# LANGUAGE OverloadedStrings #-}

-- | intermediate representation of terms for parsing
module Utils.ITerm where

import Control.Exception (assert)
import Data.List (stripPrefix)
import Prettyprinter (Pretty,pretty,align,emptyDoc,tupled)

import Utils.Type (Id,Var)
import Typ.Type (Typ(..))
import Typ.Ops (liftTyp)
import Term.Type (Term(..),Head(..))
import Equation.Type (Equation(..))

-- |type synonym to store positions in the input
type Pos = Int

data IHead = IF Id | IFV Var | IDB Id Int deriving (Eq,Ord,Show)

-- |intermediate term representation which stores positions while parsing
data ITerm = IMat Pos IHead (Maybe Typ) [ITerm] | ILam Pos Id Typ ITerm deriving (Eq,Show)

-- |intermediate equation representation which stores positions while parsing
data IEquation = IEquation { ilhs :: ITerm
                           , irhs :: ITerm
                           , iisRule :: Bool
                           , iposl :: Int
                           , iposr :: Int }

-- |ESs of intermediate equations
type IES = [IEquation]

instance Pretty IHead where
  pretty (IF idt) = pretty idt
  pretty (IFV v) = pretty v
  pretty (IDB idt _) = pretty idt

instance Pretty ITerm where
  pretty (IMat _ ih _ ts) = pretty ih <> if null ts
    then emptyDoc
    else align . tupled $ map pretty ts
  pretty (ILam _ idt a s) =
    "λ" <> pretty idt <> ":" <> pretty a <> "." <> pretty s

-- |Extracts the parse position stored in an intermediate term.
ipos :: ITerm -> Pos
ipos (IMat p _ _ _) = p
ipos (ILam p _ _ _) = p

-- | This function tries to compute the type of an intermediate term.
-- It does not check whether terms are correctly applied.
mityp :: ITerm -> Maybe Typ
mityp (IMat _ _ (Just (Typ as a)) ts) = Just $ Typ (drop (length ts) as) a
mityp (IMat _ _ Nothing _) = Nothing
mityp (ILam _ _ a s) = case mityp s of
  Just (Typ bs b) -> Just (Typ (a:bs) b)
  Nothing -> Nothing

-- | This function extracts type information from intermediate terms where
-- all the typing information on heads is available. It also checks whether
-- terms are correctly applied as a sanity check.
ityp :: ITerm -> Typ
ityp (IMat _ _ (Just (Typ as a)) ts) = case stripPrefix (map ityp ts) as of
  Just as' -> Typ as' a
  Nothing -> error "types of application do not match"
ityp (IMat _ _ Nothing _) = error "type inference missing"
ityp (ILam _ _ a s) = Typ (a:as) b where
  Typ as b = ityp s

-- |If the head is a De Bruijn index and greater or equal than
-- i, j is added to it.
shiftHead :: Int -> Int -> IHead -> IHead
shiftHead i j h@(IDB idt k)
    | k < i     = h
    | otherwise = IDB idt (k+j)
shiftHead _ _ h = h

-- |Adds j to all De Bruijn indexes in the term
-- which are greater or equal than i.
shift :: Int -> Int -> ITerm -> ITerm
shift i j (IMat pos ih a ts) = IMat pos (shiftHead i j ih) a $ map (shift i j) ts
shift i j (ILam pos idt a s) = ILam pos idt a $ shift (i+1) j s

-- |Eta-expands an intermediate term
etaExpand :: Typ -> ITerm -> ITerm
etaExpand (Typ (a:as) b) (ILam pos idt c s) =
  assert (a == c) (ILam pos idt c (etaExpand (Typ as b) s))
etaExpand (Typ [] _) (ILam _ _ _ _) = error "impossible case"
etaExpand (Typ as _) (IMat pos ih ma@(Just (Typ bs _)) ts) = foldr (ILam undefined undefined) s' as where
  l = length as
  ih' = shiftHead 0 l ih
  ts' = map (\(t,b) -> etaExpand b $ shift 0 l t) $ zip ts bs
  additionalArgs = [ etaExpand b (IMat undefined (IDB undefined i) (Just b) [])
                   | (b,i) <- zip as [l-1,l-2..]
                   ]
  s' = IMat pos ih' ma (ts' ++ additionalArgs)
etaExpand _ (IMat _ _ Nothing _) = error "type inference missing"

-- |Conversion of the intermediate head representation to the head representation
-- of the Term datatype.
iHeadToHead :: IHead -> Head
iHeadToHead (IF idt) = F idt
iHeadToHead (IFV v) = FV v
iHeadToHead (IDB _ i) = DB i

-- |Conversion from the intermediate representation of terms to terms in lnf.
iTermToTerm :: ITerm -> Term
iTermToTerm it = changeRepr [] . etaExpand (ityp it) $ it where
  changeRepr as s@(IMat _ ih _ ts) = Term { nlams = length as
                                          , hd = iHeadToHead ih
                                          , sp = map (changeRepr []) ts
                                          , typ = liftTyp as (ityp s)
                                          }
  changeRepr as (ILam _ _ a s) = changeRepr (as ++ [a]) s

-- |Conversion from the intermediate representation of equations to equations with terms in lnf.
iEqToEq :: IEquation -> Equation
iEqToEq ie = Equation { lhs = iTermToTerm $ ilhs ie
                      , rhs = iTermToTerm $ irhs ie
                      , isRule = iisRule ie
                      }
