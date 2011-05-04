{-#
  LANGUAGE
    DeriveFunctor,
    UnicodeSyntax,
    ViewPatterns
  #-}
module Stream where

import Prelude hiding (head, tail, repeat, foldr, iterate, drop, zipWith)

import Control.Applicative
import Control.Monad
import qualified Data.List as List
import Data.Monoid

data Stream a = a :* Stream a
  deriving (Eq, Ord, Functor, Show)

infixr 5 :*

head ∷ Stream a → a
head (x :* _) = x

tail ∷ Stream a → Stream a
tail (_ :* xs) = xs

foldr ∷ (a → b → b) → Stream a → b
foldr f (x :* xs) = f x (foldr f xs)

unfold ∷ (b → (a, b)) → b → Stream a
unfold f (f → (x, z)) = x :* unfold f z

repeat ∷ a → Stream a
repeat x = x :* repeat x

iterate ∷ (a → a) → a → Stream a
iterate f x = x :* iterate f (f x)

toList   ∷ Stream a → [a]
toList   = foldr (:)

fromList ∷ [a] → Stream a
fromList l0 = loop l0 where
  loop []     = fromList l0
  loop (x:xs) = x :* loop xs

take   ∷ Int → Stream a → [a]
take k = List.take k . toList

drop   ∷ Int → Stream a → Stream a
drop k xs | k <= 0 = xs
drop k (_ :* xs)   = drop (k - 1) xs

zipWith ∷ (a → b → c) → Stream a → Stream b → Stream c
zipWith f (x :* xs) (y :* ys) = f x y :* zipWith f xs ys

instance Monoid a ⇒ Monoid (Stream a) where
  mempty  = repeat mempty
  mappend = liftM2 mappend

instance Monad Stream where
  return        = repeat
  x :* xs >>= k = head (k x) :* (xs >>= (tail . k))

instance Applicative Stream where
  pure  = return
  (<*>) = zipWith ($)

instance Num a ⇒ Num (Stream a) where
  (+)         = zipWith (+)
  (*)         = zipWith (*)
  abs         = fmap abs
  signum      = fmap signum
  fromInteger = repeat . fromInteger

instance Bounded a ⇒ Bounded (Stream a) where
  minBound    = repeat minBound
  maxBound    = repeat maxBound
