{-# LANGUAGE
      UnicodeSyntax
      #-}
{- Equality type classes for unary and binary type constructors. -}
module Eq1 (
  Eq1(..), EQ1(..),
  Eq2(..), EQ2(..),
) where

import Data.IORef
import Data.STRef
import Control.Concurrent.STM.TVar

-- | Like 'Eq', but for unary type constructors.
class Eq1 t where
  eq1 ∷ t a → t a → Bool
  ne1 ∷ t a → t a → Bool
  x `ne1` y = not (x `eq1` y)

infix 4 `eq1`, `ne1`

instance Eq1 IORef where eq1 = (==)
instance Eq1 (STRef s) where eq1 = (==)
instance Eq1 TVar where eq1 = (==)

-- | Injection for using 'Eq': If @t@ is 'Eq1' then @EQ1 t a@ is 'Eq'
newtype EQ1 t a = EQ1 (t a)
instance Eq1 t ⇒ Eq1 (EQ1 t) where EQ1 x `eq1` EQ1 y = x `eq1` y
instance Eq1 t ⇒ Eq (EQ1 t a) where EQ1 x == EQ1 y = x `eq1` y

-- | Like 'Eq1', but for binary type constructors.
class Eq2 t where
  eq2 ∷ t a b → t a b → Bool
  ne2 ∷ t a b → t a b → Bool
  x `ne2` y = not (x `eq2` y)

infix 4 `eq2`, `ne2`

instance Eq2 STRef where eq2 = (==)

-- | Injection for using 'Eq': If @t@ is 'Eq2' then @EQ2 t a b@ is 'Eq'
newtype EQ2 t a b = EQ2 (t a b)
instance Eq2 t ⇒ Eq2 (EQ2 t) where EQ2 x `eq2` EQ2 y = x `eq2` y
instance Eq2 t ⇒ Eq (EQ2 t a b) where EQ2 x == EQ2 y = x `eq2` y

