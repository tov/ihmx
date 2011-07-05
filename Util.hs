{-# LANGUAGE
      BangPatterns,
      NoImplicitPrelude,
      TypeOperators,
      UnicodeSyntax
  #-}
module Util (
  module Control.Arrow,
  module Control.Applicative,
  module Control.Monad,
  module Control.Monad.Error,
  module Control.Monad.Identity,
  module Control.Monad.List,
  module Control.Monad.RWS.Strict,
  module Control.Monad.Reader,
  module Control.Monad.State.Strict,
  module Control.Monad.Trans,
  module Control.Monad.Writer.Strict,
  module Data.Foldable,
  module Data.Function,
  module Data.Maybe,
  module Data.Monoid,
  module Data.Traversable,
  module Data.Tuple.All,
  module Perhaps,
  module Prelude,
  -- * Extra list operations
  lookupWithIndex, listNth, ordNub, partitionJust,
  -- * Extra 'Traversable' operations
  mapHead, mapTail, mapInit, mapLast, foldr2,
  -- * 'Maybe' and 'Either' operations
  fromMaybeA, unEither,
  -- * Monadic operations
  allA, anyA, whenM, unlessM, concatMapM, foldM1,
  before,
  -- ** Maps for state-like monads
  mapListen2, mapListen3,
  -- * Composition combinators
  (<$$>), (<$$$>), (<$$$$>), (<$$$$$>), (<$$$$$$>),
  (<$.>), (<$$.>), (<$$$.>), (<$$$$.>),
  (<->), (<-->), (<--->), (<---->), (<----->),
) where

import Prelude hiding ( (=<<), Functor(..), Maybe(..), Monad(..), all,
                        and, any, concat, concatMap, elem, foldl, foldl1,
                        foldr, foldr1, mapM, mapM_, maximum, maybe,
                        minimum, notElem, or, product, sequence, sequence_,
                        sum )

import Control.Arrow
import Control.Applicative
import Control.Monad hiding ( forM, forM_, mapM_, mapM, msum,
                              sequence, sequence_ )

import Control.Monad.Error    ( MonadError(..), ErrorT(..), mapErrorT )
import Control.Monad.Identity ( Identity(..) )
import Control.Monad.List     ( ListT(..), mapListT )
import Control.Monad.RWS.Strict ( RWST(..), runRWST, execRWST, evalRWST,
                                  mapRWST )
import Control.Monad.Reader     ( MonadReader(..), ReaderT(..), mapReaderT )
import Control.Monad.State.Strict ( MonadState(..), StateT(..), evalStateT,
                                    evalState, gets, modify, mapStateT )
import Control.Monad.Trans    ( MonadTrans(..), MonadIO(..) )
import Control.Monad.Writer.Strict ( MonadWriter(..), WriterT(..), execWriter,
                                     mapWriterT, censor, listens )

import Data.Maybe
import Data.Monoid
import Data.Foldable
import Data.Function ( on )
import Data.Traversable
import Data.Tuple.All

import Perhaps

import qualified Data.Set as Set

lookupWithIndex ∷ Eq a ⇒ a → [(a, b)] → Maybe (b, Int)
lookupWithIndex k = loop 0 where
  loop _   []   = Nothing
  loop !ix ((k',v):rest)
    | k == k'   = Just (v, ix)
    | otherwise = loop (ix + 1) rest

listNth ∷ Int → [a] → Maybe a
listNth i = foldr (const . Just) Nothing . drop i

mapListen2 ∷ Monad m ⇒ (a → m ((b, s), w)) → a → m ((b, w), s)
mapListen3 ∷ Monad m ⇒ (a → m ((b, s1, s2), w)) → a → m ((b, w), s1, s2)

mapListen2 mapper action = do
  ((b, s), w) ← mapper action
  return ((b, w), s)

mapListen3 mapper action = do
  ((b, s1, s2), w) ← mapper action
  return ((b, w), s1, s2)

allA ∷ (Applicative f, Traversable t) ⇒ (a → f Bool) → t a → f Bool
allA pred xs = and <$> traverse pred xs

anyA ∷ (Applicative f, Traversable t) ⇒ (a → f Bool) → t a → f Bool
anyA pred xs = or <$> traverse pred xs

whenM ∷ Monad m ⇒ m Bool → m () → m ()
whenM test branch = test >>= flip when branch

unlessM ∷ Monad m ⇒ m Bool → m () → m ()
unlessM test branch = test >>= flip unless branch

foldr2 ∷ (Foldable t1, Foldable t2) ⇒
         (a → b → c → c) → c → t1 a → t2 b → c
foldr2 f z xs ys = foldr (uncurry f) z (zip (toList xs) (toList ys))

-- | Like nub, but O(n log n) instead of O(n^2)
ordNub ∷ Ord a ⇒ [a] → [a]
ordNub = loop Set.empty where
  loop seen (x:xs)
    | x `Set.member` seen = loop seen xs
    | otherwise           = x : loop (Set.insert x seen) xs
  loop _    []     = []

partitionJust ∷ (a → Maybe b) → [a] → ([a], [b])
partitionJust f = foldr each ([], []) where
  each x (xs, ys) = case f x of
    Nothing → (x:xs, ys)
    Just y →  (xs, y:ys)

concatMapM   ∷ (Foldable t, Monad m, Monoid b) ⇒ (a → m b) → t a → m b
concatMapM f = foldr (liftM2 mappend . f) (return mempty)

foldM1          ∷ (Foldable t, Monad m) ⇒ (a → a → m a) → t a → m a
foldM1 f xs0    = loop (toList xs0) where
  loop []     = fail "foldM1: empty"
  loop (x:xs) = foldM f x xs

before ∷ Monad m ⇒ m a → (a → m b) → m a
before m k = do
  a ← m
  k a
  return a

infixl 8 `before`

fromMaybeA ∷ Applicative f ⇒ f a → Maybe a → f a
fromMaybeA _ (Just a) = pure a
fromMaybeA f Nothing  = f

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

mapHead, mapTail, mapInit, mapLast ∷ Traversable t ⇒ (a → a) → t a → t a

mapHead f = snd . mapAccumL each True where
  each True x = (False, f x)
  each _    x = (False, x)

mapTail f = snd . mapAccumL each True where
  each True x = (False, x)
  each _    x = (False, f x)

mapInit f = snd . mapAccumR each True where
  each True x = (False, x)
  each _    x = (False, f x)

mapLast f = snd . mapAccumR each True where
  each True x = (False, f x)
  each _    x = (False, x)

