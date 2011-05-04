{-# LANGUAGE
      DeriveFunctor
  #-}
module Perhaps where

import Control.Applicative
import Control.Arrow
import Control.Monad
import Control.Monad.Fix
import Data.Monoid

class Functor f => Optional f where
  foldOptional :: b -> (a -> b) -> f a -> b
  optionalSome :: a -> f a
  optionalNone :: f a

instance Optional Maybe where
  foldOptional = maybe
  optionalSome = Just
  optionalNone = Nothing

instance Optional [] where
  foldOptional z f = foldr (const . f) z
  optionalSome     = return
  optionalNone     = []

coerceOptional :: (Optional f, Optional g) => f a -> g a
coerceOptional  = foldOptional optionalNone optionalSome

catOptional :: Optional f => [f a] -> [a]
catOptional = foldr (foldOptional id (:)) []

fromOptionalSome :: Optional f => f a -> a
fromOptionalSome = foldOptional (error "fromOptionalSome: got optionalNone") id

fromOptional :: Optional f => a -> f a -> a
fromOptional = flip foldOptional id

isOptionalSome, isOptionalNone :: Optional f => f a -> Bool
isOptionalSome = foldOptional False (const True)
isOptionalNone = not . isOptionalSome

mapOptional :: Optional f => (a -> f b) -> [a] -> [b]
mapOptional f = foldr (foldOptional id (:) . f) []

-- | This is like @Maybe@, except all values of the type compare as
--   equal, which is useful for “suggestions” in the syntax that have
--   no semantic significance.
data Perhaps a
  = Nope
  | Here a
  deriving Functor

instance Optional Perhaps where
  foldOptional = perhaps
  optionalSome = Here
  optionalNone = Nope

perhaps :: b -> (a -> b) -> Perhaps a -> b
perhaps nope _    Nope     = nope
perhaps _    here (Here x) = here x

catPerhaps :: [Perhaps a] -> [a]
catPerhaps = foldr (perhaps id (:)) []

fromHere :: Perhaps a -> a
fromHere = perhaps (error "fromHere: got Nope") id

fromPerhaps :: a -> Perhaps a -> a
fromPerhaps = flip perhaps id

isHere, isNope :: Perhaps a -> Bool
isHere = perhaps False (const True)
isNope = not . isHere

listToPerhaps :: [a] -> Perhaps a
listToPerhaps = foldr (const . Here) Nope

mapPerhaps :: (a -> Perhaps b) -> [a] -> [b]
mapPerhaps f = foldr (perhaps id (:) . f) []

perhapsToList :: Perhaps a -> [a]
perhapsToList = perhaps [] (:[])

perhapsToMaybe :: Perhaps a -> Maybe a
perhapsToMaybe = perhaps Nothing Just

maybeToPerhaps :: Maybe a -> Perhaps a
maybeToPerhaps = maybe Nope Here

instance Eq (Perhaps a) where
  _ == _ = True

instance Monad Perhaps where
  return = Here
  (>>=)  = perhaps (const Nope) (flip ($))

instance Ord (Perhaps a) where
  _ `compare` _ = EQ

instance Read a => Read (Perhaps a) where
  readsPrec p s = case readsPrec p s of
    [] -> [ (Nope, s) ]
    xs -> map (first Here) xs

instance Show a => Show (Perhaps a) where
  showsPrec = perhaps id . showsPrec

instance MonadFix Perhaps where
  mfix f = let a = f (unHere a) in a
     where unHere (Here x) = x
           unHere Nope     = error "mfix Perhaps: Nope"

instance MonadPlus Perhaps where
  mzero = Nope
  mplus = perhaps id (const . Here)

instance Applicative Perhaps where
  pure  = return
  (<*>) = ap

instance Monoid a => Monoid (Perhaps a) where
  mempty  = Nope
  Here x1 `mappend` Here x2 = Here (x1 `mappend` x2)
  p1      `mappend` Nope    = p1
  Nope    `mappend` p2      = p2

instance Alternative Perhaps where
  empty  = mzero
  (<|>)  = mplus

