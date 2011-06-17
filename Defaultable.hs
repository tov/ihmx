{-#
  LANGUAGE
    UnicodeSyntax
  #-}
module Defaultable (
  Defaultable(..),
) where

import qualified Data.Map as Map
import qualified Data.Set as Set

class Defaultable a where
  getDefault ∷ a

instance (Defaultable a, Defaultable b) ⇒ Defaultable (a, b) where
  getDefault = (getDefault, getDefault)

instance (Defaultable ()) where
  getDefault = ()

instance Defaultable (Map.Map k a) where
  getDefault = Map.empty

instance Defaultable (Set.Set a) where
  getDefault = Set.empty
