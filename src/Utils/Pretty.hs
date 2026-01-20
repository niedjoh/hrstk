{-# LANGUAGE OverloadedStrings #-}

-- |utility functions for prettyprinting
module Utils.Pretty where

import Data.List.NonEmpty (NonEmpty(..))
import Data.Text (Text)
import qualified Data.Text.Lazy as TL
import Prettyprinter ( Doc
                     , Pretty
                     , pretty
                     , parens
                     , vsep
                     , line
                     , (<+>)
                     , indent
                     , align
                     , fill
                     , layoutPretty
                     , defaultLayoutOptions
                     )
import Prettyprinter.Render.Text (renderStrict,renderLazy)
import Prettyprinter.Render.String (renderString)

-- |Prints parents around a document if the given predicate holds.
parensIf :: Bool -> Doc ann -> Doc ann
parensIf p x
  | p         = parens x
  | otherwise = x

-- |Prettyprinting to 'Text'.
prettyText :: Pretty a => a -> Text
prettyText = renderStrict . layoutPretty defaultLayoutOptions . pretty

-- |Prettyprinting to 'Text'.
prettyLazyText :: Pretty a => a -> TL.Text
prettyLazyText = renderLazy . layoutPretty defaultLayoutOptions . pretty

-- |Prettyprinting a rewrite sequence.
prettySequence :: Pretty a => NonEmpty a -> Doc ann
prettySequence (t :| ts)
  | null ts   = line <> line <> indent 3 (pretty t <> line <> "in normal form")
  | otherwise = line <> line <> indent 3 (pretty t) <> line <> vsep (map (\s -> "->" <+> pretty s) ts)

-- |Prettyprinting a numbered list of docs
prettyNList :: [Doc ann] -> Doc ann
prettyNList xs =  vsep $ map (\(x,i) -> "#" <> fill (log10 n + 1) (pretty i) <+> align x <> line) (zip xs [1 :: Int ..]) where
  n = length xs
  log10 = floor . logBase (10.0 :: Float) . fromIntegral

docToString :: Doc ann -> String
docToString = renderString . layoutPretty defaultLayoutOptions
