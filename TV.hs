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
    NoImplicitPrelude,
    RankNTypes,
    TypeFamilies,
    UndecidableInstances,
    UnicodeSyntax
  #-}
module TV {-(
  -- * Unification monad
  MonadTV(..), Substitutable(..),
  -- ** Rank management
  lowerRank,
  -- ** Change monitoring
  setChanged, withChanged, monitorChange, whileChanging, iterChanging,
  (>=>!),
  -- * Implementations of 'MonadTV'
  -- ** Representation of type variables
  TV,
  -- ** Transformer
  UT, runUT, UIO, UST,
  -- ** Pure
  U, runU,
  -- * Debugging
  warn, trace, debug,
)-} where

import Control.Monad.ST
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
import qualified NodeMap as NM
import qualified Graph as Gr

---
--- A unification monad
---

-- | A class for type variables and unification.
--   Minimal definition: @newTV@, @writeTV_@, @readTV_@, @setTVRank_@,
--   @getTVRank_@,
--   @hasChanged@, @setChanged@, @unsafePerformTV@, and @unsafeIOToTV@
class (Functor m, Applicative m, Monad m,
       Tv tv, MonadRef r m, MonadReadTV tv m) ⇒
      MonadTV tv r m | m → tv r where
  -- | Allocate a new, empty type variable with the give properties
  newTV_    ∷ Flavor → Kind → m tv
  -- | Allocate a new, empty (unifiable) type variable
  newTV     ∷ m tv
  newTV     = newTV' ()
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
  unsafePerformTV ∷ m a → a
  unsafeIOToTV    ∷ IO a → m a

class    NewTV a              where
  newTV'   ∷ MonadTV tv r m ⇒ a → m tv
  newTVTy' ∷ MonadTV tv r m ⇒ a → m (Type tv)
  newTVTy' = fvTy <$$> newTV'

instance NewTV (Flavor, Kind) where newTV' = uncurry newTV_
instance NewTV (Kind, Flavor) where newTV' = uncurry (flip newTV_)
instance NewTV Kind           where newTV' = newTV_ Universal
instance NewTV Flavor         where newTV' = flip newTV_ TypeKd
instance NewTV ()             where newTV' = \_ → newTV_ Universal TypeKd

class Monad m ⇒ Substitutable a m where
  -- | Fully dereference a sequence of TV indirections, with path
  --   compression, at the root of a type (or each type of a
  --   collection).
  substRoot ∷ a → m a
  -- | Fully dereference all the values, deeply.
  substDeep ∷ a → m a

instance Substitutable a m ⇒ Substitutable [a] m where
  substRoot = mapM substRoot
  substDeep = mapM substDeep

instance MonadTV tv r m ⇒ Substitutable (Type tv) m where
  substRoot (VarTy (FreeVar α)) = derefTV α
  substRoot τ                   = return τ
  substDeep = foldType (mkQuaF QuaTy)
                       (mkBvF bvTy)
                       fvTy ConTy RowTy
                       (mkRecF RecTy)

-- | Lower the rank of all the type variables in a given type
lowerRank ∷ (MonadTV tv r m, Ftv a tv) ⇒ Rank → a → m ()
lowerRank rank τ = ftvList τ >>= mapM_ (lowerTVRank rank)

-- | Record that the state has changed
setChanged ∷ MonadTV tv r m ⇒ m ()
setChanged = putChanged True

-- | Run a computation with a different changed status
withChanged ∷ MonadTV tv r m ⇒ Bool → m a → m a
withChanged b m = do
  b0 ← hasChanged
  putChanged b
  r  ← m
  putChanged b0
  return r

-- | Run a computation with starting with unchanged
monitorChange ∷ MonadTV tv r m ⇒ m a → m (a, Bool)
monitorChange m = do
  b0 ← hasChanged
  putChanged False
  r  ← m
  b  ← hasChanged
  putChanged (b || b0)
  return (r, b)

-- | Iterate a computation until it stops changing
whileChanging ∷ MonadTV tv r m ⇒ m a → m a
whileChanging m = do
  (r, b) ← monitorChange m
  if b
    then whileChanging m
    else return r

-- | Iterate a Kleisli arrow until it stops changing.
iterChanging ∷ MonadTV tv r m ⇒ (a → m a) → a → m a
iterChanging f z = do
  (z', b) ← monitorChange (f z)
  if b
    then iterChanging f z'
    else return z'

-- | Compose two Kleisli arrows, running the second only if the first
--   had no effect.
(>=>!) ∷ MonadTV tv r m ⇒ (a → m a) → (a → m a) → a → m a
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
      tvKind_  ∷ !Kind,
      tvRep    ∷ !(TVRep r)
    }

data TVRep r
  = UniFl !(r (Either Rank (Type (TV r))))
  | SkoFl

instance Tv (TV r) where
  tvUniqueID = tvId
  tvKind     = tvKind_
  tvFlavor TV { tvRep = UniFl _ } = Universal
  tvFlavor TV { tvRep = SkoFl }   = Skolem

instance Eq (TV s) where
  TV { tvId = i1 } == TV { tvId = i2 } = i1 == i2

instance Ord (TV s) where
  TV { tvId = i1 } `compare` TV { tvId = i2 } = i1 `compare` i2

instance Ppr (TV s) where
  pprPrec p tv = Ppr.text (showsPrec p tv "")

instance Show (TV s) where
  showsPrec _p tv = case (debug, unsafeReadTV tv) of
    (True, Just t) → showsPrec _p t
                     -- shows (tvId tv) . showChar '=' .
                     -- showsPrec 2 t
    _              → showChar (flavorSigil (tvFlavor tv)) . shows (tvId tv)

instance Ftv (TV s) (TV s) where
  ftvTree = ftvTree . fvTy

---
--- Implementations of MonadTV
---

-- | Monad transformer implementing 'MonadTV'.  U is for unification.
newtype UT (s ∷ * → *) m a = UT { unUT ∷ StateT UTState m a }
  deriving (Monad, MonadTrans)

-- | The state of the unification monad transformer.
data UTState
  = UTState {
      utsGensym  ∷ !Int,
      utsChanged ∷ !Bool
    }

-- | 'UT' over 'IO'
type UIO a = UT IORef IO a
-- | 'UT' over 'ST'
type UST s a = UT (STRef s) (ST s) a

instance Monad m ⇒ Functor (UT s m) where
  fmap f m = m >>= return . f

instance Monad m ⇒ Applicative (UT s m) where
  pure  = return
  (<*>) = ap

instance MonadRef s m ⇒ MonadRef s (UT s m) where
  newRef        = UT . newRef
  readRef       = UT . readRef
  writeRef      = UT <$$> writeRef
  unsafeIOToRef = UT . unsafeIOToRef

instance MonadTV tv r m ⇒ MonadReadTV tv m where
  readTV = liftM (uncurry (flip maybe Right . Left)) . rootTV

instance (Functor m, MonadRef r m) ⇒ MonadTV (TV r) r (UT r m) where
  newTV_ flavor kind = do
    uts ← UT get
    let i = utsGensym uts
    UT $ put uts { utsGensym = succ i }
    trace ("new", flavor, kind, i)
    TV i kind <$> case flavor of
      Universal → lift $ UniFl <$> newRef (Left Rank.infinity)
      Skolem    → return SkoFl
  --
  writeTV_ TV { tvRep = UniFl r } t = lift (writeRef r (Right t))
  writeTV_ TV { tvRep = SkoFl }   _ = fail "BUG! writeTV_ got skolem"
  readTV_ TV { tvRep = UniFl r } = (const Nothing ||| Just) <$> UT (readRef r)
  readTV_ TV { tvRep = SkoFl }   = return Nothing
  --
  getTVRank_ TV { tvRep = UniFl r }
    = (Just ||| const Nothing ) <$> UT (readRef r)
  getTVRank_ TV { tvRep = SkoFl }
    = return Nothing
  setTVRank_ rank TV { tvRep = UniFl r } = UT (writeRef r (Left rank))
  setTVRank_ _    TV { tvRep = SkoFl }   = fail "BUG! setTVRank_ got skolem"
  --
  hasChanged   = UT $ gets utsChanged
  putChanged b = UT $ modify $ \uts → uts { utsChanged = b }
  --
  unsafePerformTV = unsafePerformRef . unUT
  unsafeIOToTV    = lift . unsafeIOToRef

instance Defaultable UTState where
  getDefault = error "BUG! getDefault[UTState]: can't gensym here"

runUT ∷ (Functor m, Monad m) ⇒ UT s m a → m a
runUT m = evalStateT (unUT m) (UTState 0 False)

type U a = ∀ s m. (Functor m, MonadRef s m) ⇒ UT s m a

runU ∷ U a → Either String a
runU m = runST (runErrorT (runUT m))

---
--- Pass-through instances
---

instance (MonadTV tv r m, Monoid w) ⇒ MonadTV tv r (WriterT w m) where
  newTV_   = lift <$$> newTV_
  writeTV_ = lift <$$> writeTV_
  readTV_  = lift <$> readTV_
  getTVRank_ = lift <$> getTVRank_
  setTVRank_ = lift <$$> setTVRank_
  hasChanged = lift hasChanged
  putChanged = lift <$> putChanged
  unsafePerformTV = unsafePerformTV <$> liftM fst <$> runWriterT
  unsafeIOToTV    = lift <$> unsafeIOToTV

instance (MonadTV tv r m, Defaultable s) ⇒ MonadTV tv r (StateT s m) where
  newTV_   = lift <$$> newTV_
  writeTV_ = lift <$$> writeTV_
  readTV_  = lift <$> readTV_
  getTVRank_ = lift <$> getTVRank_
  setTVRank_ = lift <$$> setTVRank_
  hasChanged = lift hasChanged
  putChanged = lift <$> putChanged
  unsafePerformTV = unsafePerformTV <$> flip evalStateT getDefault
  unsafeIOToTV    = lift <$> unsafeIOToTV

instance (MonadTV tv p m, Defaultable r) ⇒ MonadTV tv p (ReaderT r m) where
  newTV_   = lift <$$> newTV_
  writeTV_ = lift <$$> writeTV_
  readTV_  = lift <$> readTV_
  getTVRank_ = lift <$> getTVRank_
  setTVRank_ = lift <$$> setTVRank_
  hasChanged = lift hasChanged
  putChanged = lift <$> putChanged
  unsafePerformTV = unsafePerformTV <$> flip runReaderT getDefault
  unsafeIOToTV    = lift <$> unsafeIOToTV

instance (MonadTV tv p m, Defaultable r, Monoid w, Defaultable s) ⇒
         MonadTV tv p (RWST r w s m) where
  newTV_   = lift <$$> newTV_
  writeTV_ = lift <$$> writeTV_
  readTV_  = lift <$> readTV_
  getTVRank_ = lift <$> getTVRank_
  setTVRank_ = lift <$$> setTVRank_
  hasChanged = lift hasChanged
  putChanged = lift <$> putChanged
  unsafePerformTV = unsafePerformTV <$> liftM fst <$>
                   \m → evalRWST m getDefault getDefault
  unsafeIOToTV    = lift <$> unsafeIOToTV

instance (MonadTV tv s m, Ord a, Gr.DynGraph g) ⇒
         MonadTV tv s (NM.NodeMapT a b g m) where
  newTV_   = lift <$$> newTV_
  writeTV_ = lift <$$> writeTV_
  readTV_  = lift <$> readTV_
  getTVRank_ = lift <$> getTVRank_
  setTVRank_ = lift <$$> setTVRank_
  hasChanged = lift hasChanged
  putChanged = lift <$> putChanged
  unsafePerformTV =
    unsafePerformTV <$> liftM fst <$> NM.runNodeMapT NM.new Gr.empty
  unsafeIOToTV    = lift <$> unsafeIOToTV

---
--- Debugging
---

-- | Super sketchy!
unsafeReadTV ∷ TV s → Maybe (Type (TV s))
unsafeReadTV TV { tvRep = UniFl r } = (const Nothing ||| Just) (unsafeReadRef r)
unsafeReadTV TV { tvRep = SkoFl }   = error "BUG! unsafeReadTV got skolem"

debug ∷ Bool
debug = False

warn ∷ MonadTV tv r m ⇒ String → m ()
warn = unsafeIOToTV . hPutStrLn stderr

trace ∷ (MonadTV tv r m, Show a) ⇒ a → m ()
trace = if debug
          then unsafeIOToTV . print
          else const (return ())
