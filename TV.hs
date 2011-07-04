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
module TV (
  -- * Type variables
  Tv(..), Flavor(..), tvKindIs, tvFlavorIs,
  -- * Unification monad
  MonadTV(..), MonadReadTV(..), NewTV(..), Substitutable(..),
  -- ** Rank management
  lowerRank,
  -- ** Change monitoring
  whileChanging, iterChanging,
  (>=>!),
  -- * Implementations of 'MonadTV'
  -- ** Representation of type variables
  TV,
  -- ** Transformer
  UT, runUT, UIO, UST,
  -- ** Pure
  U, runU,
  -- * Debugging
  module Trace,
  warn,
) where

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
import Trace

---
--- Abstract type variables
---

-- | A class for type variables (which are free in themselves).
class (Ftv v v, Show v, Ppr v) ⇒ Tv v where
  tvUniqueID ∷ v → Int
  tvKind     ∷ v → Kind
  tvFlavor   ∷ v → Flavor
  tvQual     ∷ v → Maybe QLit

data Flavor
  = Universal
  | Existential
  | Skolem
  deriving (Eq, Ord, Show)

instance Ppr Flavor where
  ppr = Ppr.char . flavorSigil

-- | Shorthand for indicating a flavor
flavorSigil ∷ Flavor → Char
flavorSigil Universal   = '@'
flavorSigil Existential = '#'
flavorSigil Skolem      = '$'

tvFlavorIs ∷ Tv v ⇒ Flavor → v → Bool
tvFlavorIs flavor v = tvFlavor v == flavor

tvKindIs ∷ Tv v ⇒ Kind → v → Bool
tvKindIs kind v = tvKind v == kind

---
--- A unification monad
---

-- | A class for type variables and unification.
--   Minimal definition: @newTV@, @writeTV_@, @readTV_@, @setTVRank_@,
--   @getTVRank_@,
--   @setChanged@, @monitorChange@, @unsafePerformTV@, and @unsafeIOToTV@
class (Functor m, Applicative m, Monad m, MonadTrace m,
       Tv tv, MonadRef r m, MonadReadTV tv m) ⇒
      MonadTV tv r m | m → tv r where
  -- | Allocate a new, empty type variable with the given properties
  newTV_    ∷ (Flavor, Kind, QLit) → m tv
  -- | Allocate a new, empty (unifiable) type variable
  newTV     ∷ m tv
  newTV     = newTV' ()
  -- | Write a type into a type variable. Not meant to be used
  --   directly by client.
  writeTV_  ∷ tv → Type tv → m ()
  -- | Read a type variable. Not meant to be used directly by
  --   clients.
  readTV_   ∷ tv → m (Maybe (Type tv))
  -- | Get all the type variables allocated while running the action
  --   (except for any masked out by a previous action.)
  collectTV ∷ m a → m (a, [tv])
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
    traceN 4 ("tvOf", τ)
    α ← newTV
    writeTV_ α τ
    return α
  -- | Write a type into an empty type variable.
  writeTV   ∷ tv → Type tv → m ()
  writeTV α τ = do
    setChanged
    (α', mτα) ← rootTV α
    traceN 2 ("writeTV", (α', mτα), τ)
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
    traceN 2 ("rewriteTV", (α', mτα), τ)
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
  getTVRank   = fromMaybe Rank.infinity <$$> getTVRank_
  -- | Lower the rank of a type variable
  lowerTVRank ∷ Rank → tv → m ()
  lowerTVRank r tv = do
    r0 ← getTVRank tv
    when (r < r0) (setTVRank_ r tv)
  -- | Monitor an action for changes to variables.
  monitorChange ∷ m a → m (a, Bool)
  -- | Indicate that something has changed.
  setChanged ∷ m ()
  -- | Unsafe operations:
  unsafePerformTV ∷ m a → a
  unsafeIOToTV    ∷ IO a → m a

class NewTV a where
  newTVArg ∷ a → (Flavor, Kind, QLit) → (Flavor, Kind, QLit)
  newTV'   ∷ MonadTV tv r m ⇒ a → m tv
  newTV' a = newTV_ (newTVArg a (Universal, TypeKd, L))
  newTVTy' ∷ MonadTV tv r m ⇒ a → m (Type tv)
  newTVTy' = fvTy <$$> newTV'

instance (NewTV a, NewTV b, NewTV c) ⇒ NewTV (a, b, c) where
  newTVArg (a, b, c) = newTVArg a . newTVArg b . newTVArg c
instance (NewTV a, NewTV b) ⇒ NewTV (a, b) where
  newTVArg (a, b) = newTVArg a . newTVArg b
instance NewTV Flavor         where newTVArg = upd1
instance NewTV Kind           where newTVArg = upd2
instance NewTV QLit           where newTVArg = upd3
instance NewTV ()             where newTVArg = const id

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
  | ExiFl !QLit !(r Rank)
  | SkoFl !QLit

instance Tv (TV r) where
  tvUniqueID = tvId
  tvKind     = tvKind_
  tvFlavor TV { tvRep = UniFl _ }   = Universal
  tvFlavor TV { tvRep = ExiFl _ _ } = Existential
  tvFlavor TV { tvRep = SkoFl _ }   = Skolem
  tvQual   TV { tvRep = SkoFl q }   = Just q
  tvQual   TV { tvRep = ExiFl q _ } = Just q
  tvQual   _                        = Nothing

instance Eq (TV s) where
  TV { tvId = i1 } == TV { tvId = i2 } = i1 == i2

instance Ord (TV s) where
  TV { tvId = i1 } `compare` TV { tvId = i2 } = i1 `compare` i2

instance Ppr (TV s) where
  pprPrec p tv = Ppr.text (showsPrec p tv "")

instance Show (TV s) where
  showsPrec _p tv = case (debug, unsafeReadTV tv) of
    (True, Just t) →
      if debugLevel > 4
        then shows (tvId tv) . showChar '=' .  showsPrec 2 t
        else showsPrec _p t
    _              → (if tvKindIs QualKd tv then showChar '`' else id)
                   . (if tvFlavorIs Universal tv
                        then id
                        else showChar (flavorSigil (tvFlavor tv)))
                   . shows (tvId tv)

instance Ftv (TV s) (TV s) where
  ftvTree = ftvTree . fvTy

---
--- Implementations of MonadTV
---

-- | Monad transformer implementing 'MonadTV'.  U is for unification.
newtype UT (s ∷ * → *) m a
  = UT { unUT ∷ RWST () (UTWriter s) UTState m a }
  deriving (Monad, MonadTrans)

-- | The synthesized state of the unification monad transformer.
type UTWriter s = ([TV s], Any)

-- | The threaded state of the unification monad transformer.
data UTState
  = UTState {
      utsGensym  ∷ !Int,
      utsTrace   ∷ !Int
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
  newRef        = lift . newRef
  readRef       = lift . readRef
  writeRef      = lift <$$> writeRef
  unsafeIOToRef = lift . unsafeIOToRef

instance MonadRef r m ⇒ MonadTrace (UT r m) where
  getTraceIndent   = UT (gets utsTrace)
  putTraceIndent n = UT (modify (\uts → uts { utsTrace = n }))

instance (Functor m, MonadRef r m) ⇒ MonadReadTV (TV r) (UT r m) where
  readTV = liftM (uncurry (flip maybe Right . Left)) . rootTV

instance (Functor m, MonadRef r m) ⇒ MonadTV (TV r) r (UT r m) where
  newTV_ (flavor, kind, bound) = do
    when (flavor == Universal && bound /= L) $
      fail "newTV_ (BUG!): universal tyvars cannot have non-L bound"
    uts ← UT get
    let i = utsGensym uts
    UT $ put uts { utsGensym = succ i }
    traceN 2 ("new", flavor, kind, i)
    α ← TV i kind <$> case flavor of
      Universal   → lift $ UniFl <$> newRef (Left Rank.infinity)
      Existential → lift $ ExiFl bound <$> newRef Rank.infinity
      Skolem      → return $ SkoFl bound
    UT $ tell ([α], mempty)
    return α
  --
  collectTV = UT . censor (upd1 []) . listens sel1 . unUT
  --
  writeTV_ TV { tvRep = UniFl r }   t = lift (writeRef r (Right t))
  writeTV_ TV { tvRep = ExiFl _ _ } _ = fail "BUG! writeTV_ got ex."
  writeTV_ TV { tvRep = SkoFl _ }   _ = fail "BUG! writeTV_ got skolem"
  readTV_ TV { tvRep = UniFl r } = (const Nothing ||| Just) <$> UT (readRef r)
  readTV_ _                      = return Nothing
  --
  getTVRank_ TV { tvRep = UniFl r }
    = (Just ||| const Nothing ) <$> UT (readRef r)
  getTVRank_ TV { tvRep = ExiFl _ r }
    = Just <$> UT (readRef r)
  getTVRank_ TV { tvRep = SkoFl _ }
    = return Nothing
  setTVRank_ rank TV { tvRep = UniFl r }   = UT (writeRef r (Left rank))
  setTVRank_ rank TV { tvRep = ExiFl _ r } = UT (writeRef r rank)
  setTVRank_ _    TV { tvRep = SkoFl _ }   = return ()
  --
  setChanged    = UT $ tell ([], Any True)
  monitorChange = UT . listens (getAny . sel2) . unUT
  --
  unsafePerformTV = unsafePerformRef . unUT
  unsafeIOToTV    = lift . unsafeIOToRef

instance Defaultable UTState where
  getDefault = error "BUG! getDefault[UTState]: can't gensym here"

runUT ∷ (Functor m, Monad m) ⇒ UT s m a → m a
runUT m = fst <$> evalRWST (unUT m) () (UTState 0 0)

type U a = ∀ s m. (Functor m, MonadRef s m) ⇒ UT s m a

runU ∷ U a → Either String a
runU m = runST (runErrorT (runUT m))

---
--- Pass-through instances
---

instance (MonadTV tv r m, Monoid w) ⇒ MonadTV tv r (WriterT w m) where
  newTV_   = lift <$> newTV_
  writeTV_ = lift <$$> writeTV_
  readTV_  = lift <$> readTV_
  collectTV     = mapWriterT (mapListen2 collectTV)
  monitorChange = mapWriterT (mapListen2 monitorChange)
  getTVRank_ = lift <$> getTVRank_
  setTVRank_ = lift <$$> setTVRank_
  setChanged = lift setChanged
  unsafePerformTV = unsafePerformTV <$> extractMsgT' ("unsafePerformTV: "++)
  unsafeIOToTV    = lift <$> unsafeIOToTV

instance (MonadTV tv r m, Monoid w) ⇒ MonadReadTV tv (WriterT w m) where
  readTV = lift . readTV

instance (MonadTV tv r m, Defaultable s) ⇒ MonadTV tv r (StateT s m) where
  newTV_   = lift <$> newTV_
  writeTV_ = lift <$$> writeTV_
  readTV_  = lift <$> readTV_
  collectTV     = mapStateT (mapListen2 collectTV)
  monitorChange = mapStateT (mapListen2 monitorChange)
  getTVRank_ = lift <$> getTVRank_
  setTVRank_ = lift <$$> setTVRank_
  setChanged = lift setChanged
  unsafePerformTV = unsafePerformTV <$> extractMsgT' ("unsafePerformTV: "++)
  unsafeIOToTV    = lift <$> unsafeIOToTV

instance (MonadTV tv r m, Defaultable s) ⇒ MonadReadTV tv (StateT s m) where
  readTV = lift . readTV

instance (MonadTV tv p m, Defaultable r) ⇒ MonadTV tv p (ReaderT r m) where
  newTV_   = lift <$> newTV_
  writeTV_ = lift <$$> writeTV_
  readTV_  = lift <$> readTV_
  collectTV     = mapReaderT collectTV
  monitorChange = mapReaderT monitorChange
  getTVRank_ = lift <$> getTVRank_
  setTVRank_ = lift <$$> setTVRank_
  setChanged = lift setChanged
  unsafePerformTV = unsafePerformTV <$> extractMsgT' ("unsafePerformTV: "++)
  unsafeIOToTV    = lift <$> unsafeIOToTV

instance (MonadTV tv r m, Defaultable s) ⇒ MonadReadTV tv (ReaderT s m) where
  readTV = lift . readTV

instance (MonadTV tv p m, Defaultable r, Monoid w, Defaultable s) ⇒
         MonadTV tv p (RWST r w s m) where
  newTV_   = lift <$> newTV_
  writeTV_ = lift <$$> writeTV_
  readTV_  = lift <$> readTV_
  collectTV     = mapRWST (mapListen3 collectTV)
  monitorChange = mapRWST (mapListen3 monitorChange)
  getTVRank_ = lift <$> getTVRank_
  setTVRank_ = lift <$$> setTVRank_
  setChanged = lift setChanged
  unsafePerformTV = unsafePerformTV <$> extractMsgT' ("unsafePerformTV: "++)
  unsafeIOToTV    = lift <$> unsafeIOToTV

instance (MonadTV tv r' m, Defaultable r, Monoid w, Defaultable s) ⇒
         MonadReadTV tv (RWST r w s m) where
  readTV = lift . readTV

instance (MonadTV tv s m, Ord a, Gr.DynGraph g) ⇒
         MonadTV tv s (NM.NodeMapT a b g m) where
  newTV_   = lift <$> newTV_
  writeTV_ = lift <$$> writeTV_
  readTV_  = lift <$> readTV_
  collectTV     = NM.mapNodeMapT (mapListen2 collectTV)
  monitorChange = NM.mapNodeMapT (mapListen2 monitorChange)
  getTVRank_ = lift <$> getTVRank_
  setTVRank_ = lift <$$> setTVRank_
  setChanged = lift setChanged
  unsafePerformTV = unsafePerformTV <$> extractMsgT' ("unsafePerformTV: "++)
  unsafeIOToTV    = lift <$> unsafeIOToTV

instance (MonadTV tv r m, Ord a, Gr.DynGraph g) ⇒
         MonadReadTV tv (NM.NodeMapT a b g m) where
  readTV = lift . readTV

instance (MonadTrace m, Ord a, Gr.DynGraph g) ⇒
         MonadTrace (NM.NodeMapT a b g m) where
  getTraceIndent = lift getTraceIndent
  putTraceIndent = lift . putTraceIndent

---
--- Debugging
---

-- | Super sketchy!
unsafeReadTV ∷ TV s → Maybe (Type (TV s))
unsafeReadTV TV { tvRep = UniFl r } = (const Nothing ||| Just) (unsafeReadRef r)
unsafeReadTV _                      = Nothing

warn ∷ MonadTV tv r m ⇒ String → m ()
warn = unsafeIOToTV . hPutStrLn stderr
