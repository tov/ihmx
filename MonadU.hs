{-#
  LANGUAGE
    ExistentialQuantification,
    FlexibleContexts,
    FlexibleInstances,
    FunctionalDependencies,
    GeneralizedNewtypeDeriving,
    KindSignatures,
    ImplicitParams,
    MultiParamTypeClasses,
    RankNTypes,
    TypeFamilies,
    UndecidableInstances,
    UnicodeSyntax
  #-}
module MonadU (
  -- * Unification monad
  MonadU(..), deref, derefAll, isUnifiableTV,
  -- ** Change monitoriing
  setChanged, withChanged, monitorChange, whileChanging, iterChanging,
  -- * Implementations of 'MonadU'
  -- ** Representation of type variables
  TV, TypeR,
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
import Control.Monad.Writer as CMW
import Control.Monad.Reader as CMR
import Control.Monad.RWS    as RWS
import Data.STRef
import Data.IORef
import qualified Data.Map
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
--   @hasChanged@, @setChanged@, @unsafePerformU#, and @unsafeIOToU@
class (Functor m, Applicative m, Monad m, Tv tv, MonadRef (URef m) m) ⇒
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
    setChanged
    (α', mτα) ← rootTV α
    (β', mτβ) ← rootTV β
    trace ("linkTV", (α', mτα), (β', mτβ))
    case (mτα, mτβ) of
      (Nothing, _) → writeTV_ α' (fvTy β')
      (_, Nothing) → writeTV_ β' (fvTy α')
      _ → fail "BUG! linkTV: Tried to overwrite type variable"
  -- | Write a type into an empty type variable.
  writeTV   ∷ tv → Type tv → m ()
  writeTV α τ = do
    setChanged
    (α', mτα) ← rootTV α
    trace ("writeTV", (α', mτα), τ)
    case mτα of
      Nothing → writeTV_ α' τ
      Just _  → fail "BUG! writeTV: Tried to overwrite type variable"
  -- | Allocate a new type variable and wrap it in a type
  newTVTy   ∷ m (Type tv)
  newTVTy   = liftM fvTy newTV
  -- | Compute the free type variables in a type
  ftv       ∷ Ftv a tv ⇒ a → m [tv]
  ftv       = ftvM where ?deref = readTV
  -- | Has the unification state changed?
  hasChanged ∷ m Bool
  -- | Set whether the unification state has changed
  putChanged ∷ Bool → m ()
  -- | Unsafe operations:
  unsafePerformU ∷ m a → a
  unsafeIOToU    ∷ IO a → m a
  -- | Arbitrary references inside the unification monad
  type URef m ∷ * → *

-- | Fully dereference a sequence of TV indirections, with path
--   compression
deref ∷ MonadU tv m ⇒ Type tv → m (Type tv)
deref (VarTy (FreeVar α)) = derefTV α
deref τ                   = return τ

-- | Fully dereference a type
derefAll ∷ MonadU tv m ⇒ Type tv → m (Type tv)
derefAll = foldType QuaTy (const bvTy) fvTy ConTy where ?deref = readTV

-- | Assert that a type variable is ununified
isUnifiableTV ∷ MonadU tv m ⇒ tv → m Bool
isUnifiableTV α = either (const True) (const False) <$> readTV α

-- | Record that the state has changed
setChanged ∷ MonadU tv m ⇒ m ()
setChanged = putChanged True

-- | Run a computation with a different changed status
withChanged ∷ MonadU tv m ⇒ Bool → m a → m a
withChanged b m = do
  b0 ← hasChanged
  putChanged b
  r  ← m
  putChanged b0
  return r

-- | Run a computation with starting with unchanged
monitorChange ∷ MonadU tv m ⇒ m a → m (a, Bool)
monitorChange m = do
  b0 ← hasChanged
  putChanged False
  r  ← m
  b  ← hasChanged
  putChanged b0
  return (r, b)

-- | Iterate a computation until it stops changing
whileChanging ∷ MonadU tv m ⇒ m a → m a
whileChanging m = do
  (r, b) ← monitorChange m
  if b
    then whileChanging m
    else return r

iterChanging ∷ MonadU tv m ⇒ (a → m a) → a → m a
iterChanging f z = do
  (z', b) ← monitorChange (f z)
  if b
    then iterChanging f z'
    else return z'

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

instance Tv (TV r) where tvUniqueID = tvId

-- | For type inference, we use types with free type variables
--   represented by a 'TV', where the parameter gives the represention
--   of the underlying mutable reference type.
type TypeR r = Type (TV r)

instance Eq (TV s) where
  TV { tvId = i1 } == TV { tvId = i2 } = i1 == i2

instance Ord (TV s) where
  TV { tvId = i1 } `compare` TV { tvId = i2 } = i1 `compare` i2

instance Ppr (TV s) where
  pprPrec p tv = Ppr.text (showsPrec p tv "")

instance Show (TV s) where
  showsPrec p tv = case (debug, unsafeReadTV tv) of
    (True, Just t) → showsPrec p t
                     -- showChar '#' . shows (tvId tv) . showChar '[' .
                     -- shows t . showChar ']'
    _              → showChar '#' . shows (tvId tv)

instance Ftv (TV s) (TV s) where
  ftvTree = ftvTree . fvTy

---
--- Implementations of MonadU
---

data UTState
  = UTState {
      utsGensym  ∷ !Int,
      utsChanged ∷ !Bool
    }

-- | Monad transformer implementing 'MonadU'
newtype UT (s ∷ * → *) m a = UT { unUT ∷ StateT UTState m a }
  deriving (Functor, Monad)

-- | 'UT' over 'IO'
type UIO a = UT IORef IO a
-- | 'UT' over 'ST'
type UST s a = UT (STRef s) (ST s) a

instance (Functor m, Monad m) ⇒ Applicative (UT s m) where
  pure  = return
  (<*>) = ap

instance MonadTrans (UT s) where
  lift = UT . lift

instance MonadRef s m ⇒ MonadRef s (UT s m) where
  newRef        = UT . newRef
  readRef       = UT . readRef
  writeRef      = UT <$$> writeRef
  unsafeIOToRef = UT . unsafeIOToRef

instance (Functor m, MonadRef s m) ⇒ MonadU (TV s) (UT s m) where
  newTV = do
    uts ← UT get
    let i = utsGensym uts
    UT $ put uts { utsGensym = succ i }
    trace ("new", i)
    r ← lift $ newRef Nothing
    return (TV i r)
  --
  writeTV_ TV { tvRef = r } t = lift (writeRef r (Just t))
  readTV_ TV { tvRef = r } = UT (readRef r)
  --
  hasChanged   = UT $ gets utsChanged
  putChanged b = UT $ modify $ \uts → uts { utsChanged = b }
  --
  unsafePerformU = unsafePerformRef . unUT
  unsafeIOToU    = lift . unsafeIOToRef
  --
  type URef (UT s m) = s

instance Defaultable UTState where
  getDefault = error "BUG! getDefault[UTState]: can't gensym here"

runUT ∷ (Functor m, Monad m) ⇒ UT s m a → m a
runUT m = evalStateT (unUT m) (UTState 0 False)

type U a = ∀ s m. (Functor m, MonadRef s m) ⇒ UT s m a

runU ∷ U a → Either String a
runU m = runST (runErrorT (runUT m))

---
--- More instances
---

instance (MonadU tv m, Monoid w) ⇒ MonadU tv (CMW.WriterT w m) where
  newTV    = lift newTV
  writeTV_ = lift <$$> writeTV_
  readTV_  = lift <$> readTV_
  hasChanged = lift hasChanged
  putChanged = lift <$> putChanged
  unsafePerformU = unsafePerformU <$> liftM fst <$> CMW.runWriterT
  unsafeIOToU    = lift <$> unsafeIOToU
  type URef (WriterT w m) = URef m

instance (MonadU tv m, Defaultable s) ⇒ MonadU tv (CMS.StateT s m) where
  newTV    = lift newTV
  writeTV_ = lift <$$> writeTV_
  readTV_  = lift <$> readTV_
  hasChanged = lift hasChanged
  putChanged = lift <$> putChanged
  unsafePerformU = unsafePerformU <$> flip CMS.evalStateT getDefault
  unsafeIOToU    = lift <$> unsafeIOToU
  type URef (CMS.StateT s m) = URef m

instance (MonadU tv m, Defaultable r) ⇒ MonadU tv (CMR.ReaderT r m) where
  newTV    = lift newTV
  writeTV_ = lift <$$> writeTV_
  readTV_  = lift <$> readTV_
  hasChanged = lift hasChanged
  putChanged = lift <$> putChanged
  unsafePerformU = unsafePerformU <$> flip CMR.runReaderT getDefault
  unsafeIOToU    = lift <$> unsafeIOToU
  type URef (CMR.ReaderT r m) = URef m

instance (MonadU tv m, Defaultable r, Monoid w, Defaultable s) ⇒
         MonadU tv (RWS.RWST r w s m) where
  newTV    = lift newTV
  writeTV_ = lift <$$> writeTV_
  readTV_  = lift <$> readTV_
  hasChanged = lift hasChanged
  putChanged = lift <$> putChanged
  unsafePerformU = unsafePerformU <$> liftM fst <$>
                   \m → RWS.evalRWST m getDefault getDefault
  unsafeIOToU    = lift <$> unsafeIOToU
  type URef (RWS.RWST r w s m) = URef m

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
