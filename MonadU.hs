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
  MonadU(..), Derefable(..), isUnifiableTV,
  -- ** Rank management
  lowerRank,
  -- ** Change monitoriing
  setChanged, withChanged, monitorChange, whileChanging, iterChanging,
  (>=>!),
  -- * Implementations of 'MonadU'
  -- ** Representation of type variables
  TV, TypeR,
  -- ** Transformer
  UT, runUT, UIO, UST,
  -- ** Pure
  U, runU,
  -- * Debugging
  warn, trace,
) where

import Control.Applicative
import Control.Monad

import Control.Monad.ST
import Control.Monad.Error  as CME
import Control.Monad.State  as CMS
import Control.Monad.Writer as CMW
import Control.Monad.Reader as CMR
import Control.Monad.RWS    as RWS
import qualified Data.Set   as Set
import Data.STRef
import Data.IORef
import qualified Text.PrettyPrint as Ppr
import System.IO (hPutStrLn, stderr)

import qualified Rank
import Rank (Rank)
import Syntax
import Ppr
import Util
import MonadRef

---
--- A unification monad
---

-- | A class for type variables and unification.
--   Minimal definition: @newTV@, @writeTV_@, @readTV_@, @setTVRank_@,
--   @getTVRank_@,
--   @hasChanged@, @setChanged@, @unsafePerformU#, and @unsafeIOToU@
class (Functor m, Applicative m, Monad m, Tv tv, MonadRef r m) ⇒
      MonadU tv r m | m → tv r where
  -- | Allocate a new, empty type variable with the given kind
  newTVKind ∷ Kind → m tv
  -- | Allocate a new, empty type variable
  newTV     ∷ m tv
  newTV     = newTVKind TypeKd
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
    trace ("tvOf", τ)
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
    when (α' /= β') $ do
      setChanged
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
      Nothing → do
        Just rank ← getTVRank_ α'
        lowerRank rank τ
        writeTV_ α' τ
      Just _  → fail "BUG! writeTV: Tried to overwrite type variable"
  -- | Write a type into a type variable, even if it's not empty.
  rewriteTV   ∷ tv → Type tv → m ()
  rewriteTV α τ = do
    setChanged
    (α', mτα) ← rootTV α
    trace ("rewriteTV", (α', mτα), τ)
    writeTV_ α' τ
  -- | Allocate a new type variable and wrap it in a type
  newTVTy   ∷ m (Type tv)
  newTVTy   = liftM fvTy newTV
  -- | Compute the free type variables in a type
  ftv       ∷ Ftv a tv ⇒ a → m [tv]
  ftv       = ftvM where ?deref = readTV
  -- | Find out the rank of a type variable. Not meant to be used
  --   directly.
  getTVRank_  ∷ tv → m (Maybe Rank)
  -- | Set the rank of a type variable. Not meant to be used
  --   directly.
  setTVRank_  ∷ Rank → tv → m ()
  -- | Find out the rank of a type variable.
  getTVRank   ∷ tv → m Rank
  getTVRank tv =
    getTVRank_ tv >>=
    maybe (fail "BUG! (getTVRank) substituted tyvar has no rank")
          return
  -- | Lower the rank of a type variable
  lowerTVRank ∷ Rank → tv → m ()
  lowerTVRank r tv = do
    r0 ← getTVRank tv
    when (r < r0) (setTVRank_ r tv)
  -- | Has the unification state changed?
  hasChanged ∷ m Bool
  -- | Set whether the unification state has changed
  putChanged ∷ Bool → m ()
  -- | Unsafe operations:
  unsafePerformU ∷ m a → a
  unsafeIOToU    ∷ IO a → m a

class Monad m ⇒ Derefable a m where
  -- | Fully dereference a sequence of TV indirections, with path
  --   compression
  deref    ∷ a → m a
  -- | Fully dereference a thing
  derefAll ∷ a → m a

instance Derefable a m ⇒ Derefable [a] m where
  deref    = mapM deref
  derefAll = mapM derefAll

instance MonadU tv r m ⇒ Derefable (Type tv) m where
  deref (VarTy (FreeVar α)) = derefTV α
  deref τ                   = return τ
  derefAll = foldType (mkQuaF QuaTy)
                      (mkBvF bvTy)
                      fvTy ConTy RowTy
                      (mkRecF RecTy)
    where ?deref = readTV

-- | Lower the rank of all the type variables in a given type
lowerRank ∷ (MonadU tv r m, Ftv a tv) ⇒ Rank → a → m ()
lowerRank rank τ = ftvSet τ >>= mapM_ (lowerTVRank rank) . Set.toList
  where ?deref = readTV

-- | Assert that a type variable is ununified
isUnifiableTV ∷ MonadU tv r m ⇒ tv → m Bool
isUnifiableTV α = either (const True) (const False) <$> readTV α

-- | Record that the state has changed
setChanged ∷ MonadU tv r m ⇒ m ()
setChanged = putChanged True

-- | Run a computation with a different changed status
withChanged ∷ MonadU tv r m ⇒ Bool → m a → m a
withChanged b m = do
  b0 ← hasChanged
  putChanged b
  r  ← m
  putChanged b0
  return r

-- | Run a computation with starting with unchanged
monitorChange ∷ MonadU tv r m ⇒ m a → m (a, Bool)
monitorChange m = do
  b0 ← hasChanged
  putChanged False
  r  ← m
  b  ← hasChanged
  putChanged (b || b0)
  return (r, b)

-- | Iterate a computation until it stops changing
whileChanging ∷ MonadU tv r m ⇒ m a → m a
whileChanging m = do
  (r, b) ← monitorChange m
  if b
    then whileChanging m
    else return r

iterChanging ∷ MonadU tv r m ⇒ (a → m a) → a → m a
iterChanging f z = do
  (z', b) ← monitorChange (f z)
  if b
    then iterChanging f z'
    else return z'

(>=>!) ∷ MonadU tv r m ⇒ (a → m a) → (a → m a) → a → m a
(>=>!) m n z = do
  (z', changed) ← monitorChange (m z)
  if changed
    then return z'
    else n z

infixr 1 >=>!

---
--- Representation of free type variables
---

-- | A free type variable is represented by a unique 'Int' (its
--   identity) and mutable reference of type @r@, which must be
--   an instance of 'UnsafeReadRef' to facilitate debugging.
data TV r
  = UnsafeReadRef r ⇒ TV {
      tvId     ∷ !Int,
      tvRef    ∷ !(r (Either Rank (Type (TV r)))),
      tvKind_  ∷ !Kind
    }

instance Tv (TV r) where
  tvUniqueID = tvId
  tvKind     = tvKind_

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
  showsPrec _p tv = case (debug, unsafeReadTV tv) of
    (True, Just t) → -- showsPrec _p t
                     shows (tvId tv) . showChar '=' .
                     showsPrec 2 t
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

instance (Functor m, MonadRef s m) ⇒ MonadU (TV s) s (UT s m) where
  newTVKind k = do
    uts ← UT get
    let i = utsGensym uts
    UT $ put uts { utsGensym = succ i }
    trace ("new", i)
    ref ← lift $ newRef (Left Rank.infinity)
    return (TV i ref k)
  --
  writeTV_ TV { tvRef = r } t = lift (writeRef r (Right t))
  readTV_ TV { tvRef = r } = (const Nothing ||| Just) <$> UT (readRef r)
  --
  getTVRank_ tv    = (Just ||| const Nothing) <$> UT (readRef (tvRef tv))
  setTVRank_ r tv  = UT (writeRef (tvRef tv) (Left r))
  --
  hasChanged   = UT $ gets utsChanged
  putChanged b = UT $ modify $ \uts → uts { utsChanged = b }
  --
  unsafePerformU = unsafePerformRef . unUT
  unsafeIOToU    = lift . unsafeIOToRef

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

instance (MonadU tv s m, Monoid w) ⇒ MonadU tv s (CMW.WriterT w m) where
  newTVKind = lift <$> newTVKind
  writeTV_ = lift <$$> writeTV_
  readTV_  = lift <$> readTV_
  getTVRank_ = lift <$> getTVRank_
  setTVRank_ = lift <$$> setTVRank_
  hasChanged = lift hasChanged
  putChanged = lift <$> putChanged
  unsafePerformU = unsafePerformU <$> liftM fst <$> CMW.runWriterT
  unsafeIOToU    = lift <$> unsafeIOToU

instance (MonadU tv r m, Defaultable s) ⇒ MonadU tv r (CMS.StateT s m) where
  newTVKind = lift <$> newTVKind
  writeTV_ = lift <$$> writeTV_
  readTV_  = lift <$> readTV_
  getTVRank_ = lift <$> getTVRank_
  setTVRank_ = lift <$$> setTVRank_
  hasChanged = lift hasChanged
  putChanged = lift <$> putChanged
  unsafePerformU = unsafePerformU <$> flip CMS.evalStateT getDefault
  unsafeIOToU    = lift <$> unsafeIOToU

instance (MonadU tv p m, Defaultable r) ⇒ MonadU tv p (CMR.ReaderT r m) where
  newTVKind = lift <$> newTVKind
  writeTV_ = lift <$$> writeTV_
  readTV_  = lift <$> readTV_
  getTVRank_ = lift <$> getTVRank_
  setTVRank_ = lift <$$> setTVRank_
  hasChanged = lift hasChanged
  putChanged = lift <$> putChanged
  unsafePerformU = unsafePerformU <$> flip CMR.runReaderT getDefault
  unsafeIOToU    = lift <$> unsafeIOToU

instance (MonadU tv p m, Defaultable r, Monoid w, Defaultable s) ⇒
         MonadU tv p (RWS.RWST r w s m) where
  newTVKind = lift <$> newTVKind
  writeTV_ = lift <$$> writeTV_
  readTV_  = lift <$> readTV_
  getTVRank_ = lift <$> getTVRank_
  setTVRank_ = lift <$$> setTVRank_
  hasChanged = lift hasChanged
  putChanged = lift <$> putChanged
  unsafePerformU = unsafePerformU <$> liftM fst <$>
                   \m → RWS.evalRWST m getDefault getDefault
  unsafeIOToU    = lift <$> unsafeIOToU

---
--- Debugging
---

-- | Super sketchy!
unsafeReadTV ∷ TV s → Maybe (TypeR s)
unsafeReadTV TV { tvRef = r } = (const Nothing ||| Just) (unsafeReadRef r)

debug ∷ Bool
debug = False

warn ∷ MonadU tv r m ⇒ String → m ()
warn = unsafeIOToU . hPutStrLn stderr

trace ∷ (MonadU tv r m, Show a) ⇒ a → m ()
trace = if debug
          then unsafeIOToU . print
          else const (return ())
