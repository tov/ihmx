{-#
  LANGUAGE
    ExistentialQuantification,
    FunctionalDependencies,
    GeneralizedNewtypeDeriving,
    KindSignatures,
    ImplicitParams,
    MultiParamTypeClasses,
    RankNTypes,
    UnicodeSyntax
  #-}
module MonadU (
  -- * Unification monad
  MonadU(..), deref, derefAll,
  -- * Implementations of 'MonadU'
  -- ** Representation of type variables
  TV,
  -- ** Transformer
  UT, runUT, UIO, UST,
  -- ** Pure
  U, runU,
  -- * Debugging
  trace,
) where

import Control.Applicative
import Control.Monad

import Control.Monad.ST
import Control.Monad.Error  as CME
import Control.Monad.State  as CMS
import Data.STRef
import Data.IORef
import qualified Text.PrettyPrint as Ppr

import Syntax
import Ppr
import MonadRef

---
--- A unification monad
---

class (Functor m, Applicative m, Monad m, Tv tv) ⇒
      MonadU tv m | m → tv where
  writeTV   ∷ tv → Type tv → m ()
  readTV    ∷ tv → m (Maybe (Type tv))
  newTV     ∷ m tv
  newTVTy   ∷ m (Type tv)
  -- | Allows re-writing a type variable, which 'writeTV' doesn't
  updateTV  ∷ tv → Type tv → m ()
  ftv       ∷ Ftv a tv ⇒ a → m [tv]
  -- Unsafe operations:
  unsafePerformU ∷ m a → a
  unsafeIOToU    ∷ IO a → m a
  --
  newTVTy  = liftM fvTy newTV
  ftv      = ftvM where ?deref = readTV
  writeTV tv t = do
    trace ("write", tv, t)
    old ← readTV tv
    case old of
      Just _  → fail "BUG: Attempted to write TV more than once"
      Nothing → updateTV tv t

-- | Fully dereference a sequence of TV indirections, with path
--   compression
deref ∷ MonadU tv m ⇒ Type tv → m (Type tv)
deref = liftM fst . loop where
  loop τ0@(VarTy (FreeVar α)) = do
    mτ ← readTV α
    case mτ of
      Nothing → return (τ0, False)
      Just τ1 → do
        (τ, b) ← loop τ1
        when b (updateTV α τ)
        return (τ, True)
  loop τ0 = return (τ0, False)

-- | Fully dereference a type
derefAll ∷ MonadU tv m ⇒ Type tv → m (Type tv)
derefAll = foldType QuaTy bvTy fvTy ConTy where ?deref = readTV

---
--- Representation of free type variables
---

-- | A free type variable is represented by a unique 'Int' (its
--   identity) and mutable reference of type @r@, which must be
--   an instance of 'UnsafeReadRef' to facilitate debugging.
data TV r
  = UnsafeReadRef r ⇒ TV {
      tvId     ∷ !Int,
      tvRef    ∷ !(r (Maybe (TypeR r)))
    }

-- | For type inference, we use types with free type variables
--   represented by a 'TV', where the parameter gives the represention
--   of the underlying mutable reference type.
type TypeR r = Type (TV r)

instance Eq (TV s) where
  TV { tvId = i1 } == TV { tvId = i2 } = i1 == i2

instance Ord (TV s) where
  TV { tvId = i1 } `compare` TV { tvId = i2 } = i1 `compare` i2

instance Ppr (TV s) where
  ppr = Ppr.text . show

instance Show (TV s) where
  showsPrec _ tv = showChar '#' . shows (tvId tv)
      . if debug -- && tvFlavor tv == Universal
          then case unsafeReadTV tv of
                 Nothing → id
                 Just t  → showChar '[' . shows t . showChar ']'
          else id

instance Ftv (TV s) (TV s) where
  ftvTree = ftvTree . fvTy

---
--- Implementations of MonadU
---

-- | Monad transformer implementing 'MonadU'
newtype UT (s ∷ * → *) m a = UT { unUT ∷ StateT Int m a }
  deriving (Functor, Monad)

-- | 'UT' over 'IO'
type UIO a = UT IORef IO a
-- | 'UT' over 'ST'
type UST s a = UT (STRef s) (ST s) a

instance Monad m ⇒ Applicative (UT s m) where
  pure  = return
  (<*>) = ap

instance MonadTrans (UT s) where
  lift = UT . lift

instance MonadRef s m ⇒ MonadU (TV s) (UT s m) where
  updateTV TV { tvRef = r } t = lift (writeRef r (Just t))
  --
  newTV = do
    i ← UT get
    r ← lift $ newRef Nothing
    trace ("new", i)
    UT $ put (i + 1)
    return (TV i r)
  --
  readTV TV { tvRef = r } = UT (readRef r)
  --
  unsafePerformU = unsafePerformRef . unUT
  unsafeIOToU    = lift . unsafeIOToRef

instance Defaultable Int where getDefault = 0

runUT ∷ Monad m ⇒ UT s m a → m a
runUT m = evalStateT (unUT m) 0

type U a = ∀ s m. MonadRef s m ⇒ UT s m a

runU ∷ U a → Either String a
runU m = runST (runErrorT (runUT m))

---
--- Debugging
---

-- | Super sketchy!
unsafeReadTV ∷ TV s → Maybe (TypeR s)
unsafeReadTV TV { tvRef = r } = unsafeReadRef r

debug ∷ Bool
debug = False

trace ∷ (MonadU r m, Show a) ⇒ a → m ()
trace = if debug
          then unsafeIOToU . print
          else const (return ())
