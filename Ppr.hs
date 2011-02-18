{-# LANGUAGE
      UnicodeSyntax
  #-}
module Ppr where

import Text.PrettyPrint as Ppr

-- | A type class for types that are pretty-printable. Helps to manage
--   precedence levels, and uses the Show trick for lists.
class Ppr a where
  pprPrec    ∷ Int → a → Doc
  pprPrec _  = ppr
  ppr        ∷ a → Doc
  ppr        = pprPrec 0
  pprList    ∷ [a] → Doc
  pprList xs = char '[' <>
                 fsep (punctuate comma (map ppr xs))
               <> char ']'

instance Ppr a ⇒ Ppr [a] where
  ppr = pprList

instance Ppr Char where
  ppr c     = text [c]
  pprList s = text s

parensIf :: Bool → Doc → Doc
parensIf False = id
parensIf True  = parens

