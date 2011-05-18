{-# LANGUAGE
      BangPatterns,
      TypeOperators,
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
  -- module Data.Foldable,
  -- module Data.Traversable,
  findLastIndex, listNth,
  allM, whenM, unlessM, foldr2, ordNub, concatMapM, foldM1,
  before,
  (<$$>), (<$$$>), (<$$$$>), (<$$$$$>), (<$$$$$$>),
  (<$.>), (<$$.>), (<$$$.>), (<$$$$.>),
) where

{-
import Prelude hiding ( (=<<), Functor(..), Maybe(..), Monad(..), all,
                        and, any, concat, concatMap, elem, foldl, foldl1,
                        foldr, foldr1, mapM, mapM_, maximum, maybe,
                        minimum, notElem, or, product, sequence, sequence_,
                        sum )
-}

import Perhaps
import TupleClass

import Control.Arrow
import Control.Applicative
import Control.Monad 
  {- hiding ( forM, forM_, mapM, mapM_, msum,
              sequence, sequence_ ) -}
import Data.Monoid
import Data.Maybe
-- import Data.Foldable
-- import Data.Traversable

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

concatMapM   ∷ Monad m ⇒ (a → m [b]) → [a] → m [b]
concatMapM f = foldr (liftM2 (++) . f) (return [])

foldM1       ∷ Monad m ⇒ (a → a → m a) → [a] → m a
foldM1 _ []     = fail "foldM1: empty"
foldM1 f (x:xs) = foldM f x xs

before ∷ Monad m ⇒ m a → (a → m b) → m a
before m k = do
  a ← m
  k a
  return a

infixl 8 `before`

(<$$>) ∷ (Functor f, Functor g) ⇒ 
         (b → c) → g (f b) → g (f c)
(<$$>) = fmap . fmap

(<$$$>) ∷ (Functor f, Functor g, Functor h) ⇒
          (b → c) → h (g (f b)) →
          h (g (f c))
(<$$$>) = fmap . fmap . fmap

(<$$$$>) ∷ (Functor f, Functor g, Functor h, Functor i) ⇒
           (b → c) → i (h (g (f b))) →
           i (h (g (f c)))
(<$$$$>) = fmap . fmap . fmap . fmap

(<$$$$$>) ∷ (Functor f, Functor g, Functor h, Functor i, Functor j) ⇒
            (b → c) → j (i (h (g (f b)))) →
            j (i (h (g (f c))))
(<$$$$$>) = fmap . fmap . fmap . fmap . fmap

(<$$$$$$>) ∷ (Functor f, Functor g, Functor h,
              Functor i, Functor j, Functor k) ⇒
             (b → c) → k (j (i (h (g (f b))))) →
             k (j (i (h (g (f c)))))
(<$$$$$$>) = fmap . fmap . fmap . fmap . fmap . fmap

infixl 4 <$$>, <$$$>, <$$$$>, <$$$$$>, <$$$$$$>

(<$.>) ∷ (Arrow (⇝), Functor f) ⇒
         f (b ⇝ c) → (a ⇝ b) →
         f (a ⇝ c)
f <$.> g = (g >>>) <$> f

(<$$.>) ∷ (Arrow (⇝), Functor f, Functor g) ⇒
          g (f (b ⇝ c)) → (a ⇝ b) →
          g (f (a ⇝ c))
f <$$.> g = (g >>>) <$$> f

(<$$$.>) ∷ (Arrow (⇝), Functor f, Functor g, Functor h) ⇒
           h (g (f (b ⇝ c))) → (a ⇝ b) →
           h (g (f (a ⇝ c)))
f <$$$.> g = (g >>>) <$$$> f

(<$$$$.>) ∷ (Arrow (⇝), Functor f, Functor g, Functor h, Functor i) ⇒
            i (h (g (f (b ⇝ c)))) → (a ⇝ b) →
            i (h (g (f (a ⇝ c))))
f <$$$$.> g = (g >>>) <$$$$> f

infixl 4 <$.>, <$$.>, <$$$.>, <$$$$.>
