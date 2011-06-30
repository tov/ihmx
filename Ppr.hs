{-# LANGUAGE
      UnicodeSyntax
  #-}
module Ppr where

import Text.PrettyPrint   as Ppr
import qualified Data.Map as Map
import qualified Data.Set as Set

parensIf :: Bool → Doc → Doc
parensIf False = id
parensIf True  = parens

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

instance Ppr Doc where
  ppr = id

instance Ppr Char where
  ppr c     = text [c]
  pprList s = text s

instance Ppr Int where
  ppr       = int

instance Ppr Bool where
  ppr       = text . show

instance Ppr a ⇒ Ppr (Maybe a) where
  pprPrec _ Nothing  = text "Nothing"
  pprPrec p (Just x) = parensIf (p > 10) $
                         text "Just" Ppr.<+> pprPrec 0 x

instance (Ppr a, Ppr b) ⇒ Ppr (a, b) where
  ppr (a,b) = parens (sep (punctuate comma [ppr a, ppr b]))

instance (Ppr a, Ppr b, Ppr c) ⇒ Ppr (a, b, c) where
  ppr (a,b,c) = parens (sep (punctuate comma [ppr a, ppr b, ppr c]))

instance (Ppr a, Ppr b, Ppr c, Ppr d) ⇒ Ppr (a, b, c, d) where
  ppr (a,b,c,d) = parens (sep (punctuate comma [ppr a, ppr b, ppr c, ppr d]))

instance (Ppr k, Ppr v) ⇒ Ppr (Map.Map k v) where
  ppr m = braces . fsep . punctuate comma $
    [ ppr k <> colon <+> ppr v
    | (k, v) ← Map.toList m ]

instance Ppr a ⇒ Ppr (Set.Set a) where
  ppr = braces . fsep . punctuate comma . map ppr . Set.toList

