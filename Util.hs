{-# LANGUAGE
      BangPatterns,
      UnicodeSyntax
  #-}
module Util (
  module Perhaps,
  module TupleClass,
  module Control.Arrow,
  module Control.Applicative,
  module Control.Monad,
  module Data.Monoid,
  module Data.Maybe,
  findLastIndex, listNth,
  allM, whenM, unlessM, foldr2, ordNub,
  before,
  (<$$>), (<$$$>), (<$$$$>), (<$$$$$>), (<$$$$$$>),
  (<$.>), (<$$.>), (<$$$.>), (<$$$$.>),
) where

import Perhaps
import TupleClass

import Control.Arrow
import Control.Applicative
import Control.Monad
import Data.Monoid
import Data.Maybe

import qualified Data.Set as Set

findLastIndex ∷ (a → Bool) → [a] → Maybe Int
findLastIndex pred = loop 0 Nothing where
  loop _  acc [] = acc
  loop !ix acc (x:xs) = loop (ix + 1) (if pred x then Just ix else acc) xs

listNth ∷ Int → [a] → Maybe a
listNth i = foldr (const . Just) Nothing . drop i

allM ∷ Monad m ⇒ (a → m Bool) → [a] → m Bool
allM pred xs = mapM pred xs >>= return . all id

whenM ∷ Monad m ⇒ m Bool → m () → m ()
whenM test branch = test >>= flip when branch

unlessM ∷ Monad m ⇒ m Bool → m () → m ()
unlessM test branch = test >>= flip unless branch

foldr2 ∷ (a → b → c → c) → c → [a] → [b] → c
foldr2 f z xs ys = foldr (uncurry f) z (zip xs ys)

-- | Like nub, but O(n log n) instead of O(n^2)
ordNub ∷ Ord a ⇒ [a] → [a]
ordNub = loop Set.empty where
  loop seen (x:xs)
    | x `Set.member` seen = loop seen xs
    | otherwise           = x : loop (Set.insert x seen) xs
  loop _    []     = []

before ∷ Monad m ⇒ m a → (a → m b) → m a
before m k = do
  a ← m
  k a
  return a

infixl 8 `before`

(<$$>) ∷ (b → c) → (a1 → a2 → b) →
         a1 → a2 → c
(f <$$> g) x = f <$> g x

(<$$$>) ∷ (b → c) → (a1 → a2 → a3 → b) →
          a1 → a2 → a3 → c
(f <$$$> g) x = f <$$> g x

(<$$$$>) ∷ (b → c) → (a1 → a2 → a3 → a4 → b) →
           a1 → a2 → a3 → a4 → c
(f <$$$$> g) x = f <$$$> g x

(<$$$$$>) ∷ (b → c) → (a1 → a2 → a3 → a4 → a5 → b) →
            a1 → a2 → a3 → a4 → a5 → c
(f <$$$$$> g) x = f <$$$$> g x

(<$$$$$$>) ∷ (b → c) → (a1 → a2 → a3 → a4 → a5 → a6 → b) →
             a1 → a2 → a3 → a4 → a5 → a6 → c
(f <$$$$$$> g) x = f <$$$$$> g x

infixl 4 <$$>, <$$$>, <$$$$>, <$$$$$>, <$$$$$$>

(<$.>) ∷ (b1 → b2 → c) → (a → b2) →
         b1 → a → c
f <$.> g = flip (<$>) g . f

(<$$.>) ∷ (b1 → b2 → b3 → c) → (a → b3) →
          b1 → b2 → a → c
f <$$.> g = flip (<$.>) g . f

(<$$$.>) ∷ (b1 → b2 → b3 → b4 → c) → (a → b4) →
           b1 → b2 → b3 → a → c
f <$$$.> g = flip (<$$.>) g . f

(<$$$$.>) ∷ (b1 → b2 → b3 → b4 → b5 → c) → (a → b5) →
            b1 → b2 → b3 → b4 → a → c
f <$$$$.> g = flip (<$$$.>) g . f

infixl 4 <$.>, <$$.>, <$$$.>, <$$$$.>
