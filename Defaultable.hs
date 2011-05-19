{-#
  LANGUAGE
    UnicodeSyntax
  #-}
module Defaultable (
  Defaultable(..),
) where

import qualified Data.Map as Map

class Defaultable a where
  getDefault ∷ a

instance (Defaultable a, Defaultable b) ⇒ Defaultable (a, b) where
  getDefault = (getDefault, getDefault)

instance (Defaultable ()) where
  getDefault = ()

instance Defaultable (Map.Map k a) where
  getDefault = Map.empty

