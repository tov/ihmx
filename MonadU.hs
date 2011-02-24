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
import Util
import MonadRef

---
--- A unification monad
---

-- | A class for type variables and unification.
--   Minimal definition: @newTV@, @writeTV_@, @readTV_@,
--   @unsafePerformU#, and @unsafeIOToU@
class (Functor m, Applicative m, Monad m, Tv tv) ⇒
      MonadU tv m | m → tv where
  -- | Allocate a new, empty type variable
  newTV     ∷ m tv
  -- | Write a type into a type variable. Not meant to be used
  --   directly by client.
  writeTV_  ∷ tv → Type tv → m ()
  -- | Read a type variable. Not meant to be used directly by
  --   clients.
  readTV_   ∷ tv → m (Maybe (Type tv))
  -- | Get the canonical representative (root) of a tree of type
  --   variables, and any non-tv type stored at the root, if it
  --   exists.  Performs path compression.
  rootTV   ∷ tv → m (tv, Maybe (Type tv))
  rootTV α = do
    mτ ← readTV_ α
    case mτ of
      Just (VarTy (FreeVar α')) → do
        (α'', mτ') ← rootTV α'
        when (α'' /= α') $ writeTV_ α (fvTy α'')
        return (α'', mτ')
      Just τ  → return (α, Just τ)
      Nothing → return (α, Nothing)
  -- | Get the canonical representation of a tree of type variables.
  reprTV    ∷ tv → m tv
  reprTV    = liftM fst . rootTV
  -- | Fully dereference a type variable, getting a @Right τ@ if the
  --   chain ends with a non-type variable type @τ@, and @Left α$ if
  --   the type variable is empty, where @α@ is the representative.
  readTV    ∷ tv → m (Either tv (Type tv))
  readTV    = liftM (uncurry (flip maybe Right . Left)) . rootTV
  -- | Follow a type variable to the end of the chain, whatever that is.
  derefTV   ∷ tv → m (Type tv)
  derefTV   = liftM (uncurry (fromMaybe . fvTy)) . rootTV
  -- | Get a type variable pointing to a type. If the type is already
  --   a type variable, then we get the canonical representation.
  tvOf ∷ Type tv → m tv
  tvOf (VarTy (FreeVar α)) = reprTV α
  tvOf τ = do
    α ← newTV
    writeTV_ α τ
    return α
  -- | Combine two type variables to point to the same root.
  --   If both type variables have a type at the root, that's
  --   an error.
  linkTV    ∷ tv → tv → m ()
  linkTV α β = do
    (α', mτα) ← rootTV α
    (β', mτβ) ← rootTV β
    trace ("linkTV", (α', mτα), (β', mτβ))
    case (mτα, mτβ) of
      (Nothing, _) → writeTV_ α' (fvTy β')
      (_, Nothing) → writeTV_ β' (fvTy α')
      _ → fail "BUG! linkTV: Tried to overwrite type variable"
  -- | Write a type into an empty type variable.
  writeTV   ∷ tv → Type tv → m ()
  writeTV α τ = linkTV α =<< tvOf τ
  -- | Allocate a new type variable and wrap it in a type
  newTVTy   ∷ m (Type tv)
  newTVTy   = liftM fvTy newTV
  -- | Compute the free type variables in a type
  ftv       ∷ Ftv a tv ⇒ a → m [tv]
  ftv       = ftvM where ?deref = readTV
  -- Unsafe operations:
  unsafePerformU ∷ m a → a
  unsafeIOToU    ∷ IO a → m a

-- | Fully dereference a sequence of TV indirections, with path
--   compression
deref ∷ MonadU tv m ⇒ Type tv → m (Type tv)
deref (VarTy (FreeVar α)) = derefTV α
deref τ                   = return τ

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
      tvRef    ∷ !(r (Maybe (Type (TV r))))
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
  newTV = do
    i ← UT $ get `before` put . succ
    trace ("new", i)
    r ← lift $ newRef Nothing
    return (TV i r)
  --
  writeTV_ TV { tvRef = r } t = lift (writeRef r (Just t))
  --
  readTV_ TV { tvRef = r } = UT (readRef r)
  --
  unsafePerformU = unsafePerformRef . unUT
  unsafeIOToU    = lift . unsafeIOToRef

instance Defaultable Int where
  getDefault = error "BUG! getDefault[Int]: can't gensym here"

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
