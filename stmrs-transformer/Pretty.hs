{-# LANGUAGE OverloadedStrings #-}
module Pretty where

import Equation.Type
import Typ.Type
import Term.Type
import Utils.Type
import Prettyprinter
import Data.Text.Internal

prettyAriSystem :: ES -> Doc ann
prettyAriSystem equations = vsep (map prettyAriEquation equations)

prettyAriEquation :: Equation -> Doc ann
prettyAriEquation e = 
    let 
        -- Format both sides using your new function!
        leftSide  = prettyAri (lhs e)
        rightSide = prettyAri (rhs e)
    in 
        if isRule e 
        then parens ("rule" <+> leftSide <+> rightSide)
        else parens ("equation" <+> leftSide <+> rightSide)


prettyAri :: Term -> Doc ann
prettyAri = go [] (0 :: Int) where

  -- The Head lookup stays exactly the same!
  prettyHd (F idt) _ = pretty idt
  prettyHd (FV v) _ = pretty v
  prettyHd (DB i) ctx
    | i < 0          = error "negative DB"
    | i < length ctx = pretty (ctx !! i)
    | otherwise      = error "dangling DB"

  -- The recursive worker
  go ctx d s = 
    let k = nlams s
        -- 1. Invent names (x0, x1, etc.)
        vars = ["x" ++ show i | i <- [d..d+k-1]]
        -- 2. Update context
        ctx' = reverse vars ++ ctx
        d' = d+k

        -- 3. FORMATTING THE APPLICATION (Lisp style: "(f a b)")
        appDoc = if null (sp s) 
                 then prettyHd (hd s) ctx' 
                 -- 'hsep' puts spaces between items, 'parens' wraps it in ()
                 else parens (hsep (prettyHd (hd s) ctx' : map (go ctx' d') (sp s)))

    in if k > 0 
       then 
            -- 1. Extract the list of argument types from the lambda node 's'
            let argTyps = getArgTypes (typ s)
            
            -- 2. Zip the invented names (vars) with their corresponding types (argTyps)
                bindings = hsep [ parens (pretty v <+> prettyTyp t) 
                                          | (v, t) <- zip vars argTyps ]
                                
            in parens ("lambda" <+> parens bindings <+> appDoc)
       else 
            appDoc


-- Pulls the list of argument types out of the function's type signature
getArgTypes :: Typ -> [Typ]
getArgTypes (Typ args _returnType) = args

-- Grabs the string name out of a base sort
getSortName :: Typ -> Data.Text.Internal.Text
getSortName (Typ [] (Id name)) = name
getSortName _ = "unknown_sort" -- Fallback just in case

prettyTyp :: Typ -> Doc ann
-- Fall 1: Keine Argumente. Es ist ein Basis-Sort (z.B. N). Drucke einfach die ID.
prettyTyp (Typ [] sortId) = pretty sortId
-- Fall 2: Es gibt Argumente. Es ist eine Funktion. Bilde (-> arg1 arg2 ... ret)
prettyTyp (Typ args retId) = 
    parens ("->" <+> hsep (map prettyTyp args) <+> pretty retId)