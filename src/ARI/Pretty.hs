{-# LANGUAGE OverloadedStrings #-}
module ARI.Pretty where

import Equation.Type (Equation(..),ES)
import Typ.Type (Typ(..))
import Term.Type (Term(..),Head(..))
import Prettyprinter (Doc,pretty,hsep,vsep,parens,(<+>))
import Typ.Ops (argTyps)

prettyARIsystem :: ES -> Doc ann
prettyARIsystem equations = vsep (map prettyARIeq equations)

prettyARIeq :: Equation -> Doc ann
prettyARIeq e = parens (tag <+> leftSide <+> rightSide) where
   leftSide  = prettyARIterm (lhs e)
   rightSide = prettyARIterm (rhs e)
   tag = if isRule e
     then "rule"
     else "equation"

prettyARIterm :: Term -> Doc ann
prettyARIterm = go [] (0 :: Int) where
  prettyHd (F idt) _ = pretty idt
  prettyHd (FV v) _ = pretty v
  prettyHd (DB i) ctx
    | i < 0          = error "negative DB"
    | i < length ctx = pretty (ctx !! i)
    | otherwise      = error "dangling DB"
  prettyHd (FStar _ _) _ = error "impossible case"
  go ctx d s@(Term {nlams = k})
    | k > 0 = parens ("lambda" <+> parens bindings <+> appDoc)
    | otherwise = appDoc
    where
      appDoc = if null (sp s)
        then prettyHd (hd s) ctx'
        else parens (hsep (prettyHd (hd s) ctx' : map (go ctx' d') (sp s)))
      vars = ["x" ++ show i | i <- [d..d+k-1]]
      ctx' = reverse vars ++ ctx
      d' = d+k
      bindings = hsep [ parens (pretty v <+> prettyARItyp t)
                      | (v, t) <- zip vars (argTyps (typ s)) ]

prettyARItyp :: Typ -> Doc ann
prettyARItyp (Typ [] a) = pretty a
prettyARItyp (Typ bs a) =  parens ("->" <+> hsep (map prettyARItyp bs) <+> pretty a)
