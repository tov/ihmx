{-# LANGUAGE
      BangPatterns,
      TypeOperators,
      UnicodeSyntax
  #-}
module Util (
  module Perhaps,
  module Control.Arrow,
  module Control.Applicative,
  module Control.Monad,
  module Data.List,
  module Data.Monoid,
  module Data.Maybe,
  -- module Data.Foldable,
  -- module Data.Traversable,
  findLastIndex, listNth,
  allM, anyM, whenM, unlessM, foldr2, ordNub, concatMapM, mconcatMapM, foldM1,
  before,
  unEither,
  (<$$>), (<$$$>), (<$$$$>), (<$$$$$>), (<$$$$$$>),
  (<$.>), (<$$.>), (<$$$.>), (<$$$$.>),
  (<->), (<-->), (<--->), (<---->), (<----->),
  mapHead, mapTail, mapInit, mapLast,
) where

{-
import Prelude hiding ( (=<<), Functor(..), Maybe(..), Monad(..), all,
                        and, any, concat, concatMap, elem, foldl, foldl1,
                        foldr, foldr1, mapM, mapM_, maximum, maybe,
                        minimum, notElem, or, product, sequence, sequence_,
                        sum )
-}

import Perhaps

import Control.Arrow
import Control.Applicative
import Control.Monad 
  {- hiding ( forM, forM_, mapM, mapM_, msum,
              sequence, sequence_ ) -}
import Data.List (foldl')
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
allM pred xs = all id `liftM` mapM pred xs

anyM ∷ Monad m ⇒ (a → m Bool) → [a] → m Bool
anyM pred xs = any id `liftM` mapM pred xs

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

mconcatMapM   ∷ (Monad m, Monoid b) ⇒ (a → m b) → [a] → m b
mconcatMapM f = foldr (liftM2 mappend . f) (return mempty)

foldM1       ∷ Monad m ⇒ (a → a → m a) → [a] → m a
foldM1 _ []     = fail "foldM1: empty"
foldM1 f (x:xs) = foldM f x xs

before ∷ Monad m ⇒ m a → (a → m b) → m a
before m k = do
  a ← m
  k a
  return a

infixl 8 `before`

unEither ∷ Either a a → a
unEither = either id id

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

(<->)   ∷ Functor f ⇒ 
          f (a → b) → a → f b
f <-> x = ($ x) <$> f

(<-->)   ∷ (Functor f, Functor g) ⇒
           f (g (a → b)) → a → f (g b)
f <--> x = (<-> x) <$> f

(<--->)   ∷ (Functor f, Functor g, Functor h) ⇒
            f (g (h (a → b))) → a → f (g (h b))
f <---> x = (<--> x) <$> f

(<---->)   ∷ (Functor f, Functor g, Functor h, Functor i) ⇒
             f (g (h (i (a → b)))) → a → f (g (h (i b)))
f <----> x = (<---> x) <$> f

(<----->)   ∷ (Functor f, Functor g, Functor h, Functor i, Functor j) ⇒
              f (g (h (i (j (a → b))))) → a → f (g (h (i (j b))))
f <-----> x = (<----> x) <$> f

infixl 4 <->, <-->, <--->, <---->, <----->

mapHead, mapTail, mapInit, mapLast ∷ (a → a) → [a] → [a]

mapHead _ []     = []
mapHead f (x:xs) = f x : xs

mapTail _ []     = []
mapTail f (x:xs) = x : map f xs

mapInit _ []     = []
mapInit _ [x]    = [x]
mapInit f (x:xs) = f x : mapInit f xs

mapLast _ []     = []
mapLast f [x]    = [f x]
mapLast f (x:xs) = x : mapLast f xs

