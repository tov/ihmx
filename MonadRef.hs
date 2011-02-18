{-#
  LANGUAGE
    FlexibleInstances,
    FunctionalDependencies,
    ImpredicativeTypes,
    MultiParamTypeClasses,
    RankNTypes,
    UndecidableInstances,
    UnicodeSyntax
  #-}
module MonadRef (
  MonadRef(..), Defaultable(..),
  RefT, RefRef, runRefT,
  withUnsafePerformRef, withUnsafeRefToIO,
  unsafePerformRef, unsafeRefToIO,
) where

import Control.Applicative

import Control.Monad.ST
import Control.Monad.STM

import Data.IORef
import Data.STRef
import Control.Concurrent.STM.TVar

import Control.Monad.Cont
import Control.Monad.Error
import Control.Monad.List
import Control.Monad.RWS
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

import System.IO.Unsafe
import GHC.Conc (unsafeIOToSTM)

-- | A class for monads with mutable references. Provides generic
--   operations for creating, reading, writing, and modifying
--   references.
class Monad m ⇒ MonadRef p m | m → p where
  newRef    ∷ a → m (p a)
  readRef   ∷ p a → m a
  writeRef  ∷ p a → a → m ()
  modifyRef ∷ (a → a) → p a → m ()
  modifyRef f r = do
    a ← readRef r
    writeRef r (f a)
  -- Unsafe operations.  Minimal definition: unsafeIOToRef, and either
  -- maybeUnsafeRefToIO or maybeUnsafePerformRef
  unsafeIOToRef         ∷ IO a → m a
  maybeUnsafeRefToIO    ∷ Maybe (forall a. m a → IO a)
  maybeUnsafeRefToIO    = withUnsafePerformRef (\it → return . it)
  maybeUnsafePerformRef ∷ Maybe (forall a. m a → a)
  maybeUnsafePerformRef = withUnsafeRefToIO (\it → unsafePerformIO . it)

---
--- Helpers for unsafe operations
---

withUnsafePerformRef ∷ (MonadRef p m, Monad m') ⇒
                       ((forall a. m a → a) → r) → m' r
withUnsafePerformRef kont =
  maybe (fail "withUnsafePerformRef: not found")
        (return . kont) maybeUnsafePerformRef

withUnsafeRefToIO ∷ (MonadRef p m, Monad m') ⇒
                    ((forall a. m a → IO a) → r) → m' r
withUnsafeRefToIO kont =
  maybe (fail "withUnsafeRefToIO: not found") (return . kont) maybeUnsafeRefToIO

unsafeRefToIO ∷ MonadRef p m ⇒ m a → IO a
unsafeRefToIO m = join (withUnsafeRefToIO (\it → it m))

unsafePerformRef ∷ MonadRef p m ⇒ m a → a
unsafePerformRef m = either error id (withUnsafePerformRef (\it → it m))

class Defaultable a where
  getDefault ∷ a

---
--- A transformer version of ST
---

newtype RefT s m a = RefT { unRefT ∷ m a }

runRefT ∷ Monad m ⇒ (forall s. RefT s m a) → m a
runRefT m = unRefT m

instance Monad m ⇒ Functor (RefT s m) where
  fmap  = liftM

instance Monad m ⇒ Applicative (RefT s m) where
  pure  = return
  (<*>) = ap

instance Monad m ⇒ Monad (RefT s m) where
  return  = RefT . return
  m >>= k = RefT (unRefT m >>= unRefT . k)

instance MonadTrans (RefT s) where
  lift = RefT

newtype RefRef s a = RefRef (IORef (Box a))

data Box a = Box { unBox ∷ a }

instance Monad m ⇒ MonadRef (RefRef s) (RefT s m) where
  newRef a = return (RefRef (unsafePerformIO (newIORef (Box a))))
  readRef (RefRef r) =
    let a = unsafePerformIO (readIORef r)
     in a `seq` return (unBox a)
  writeRef (RefRef r) a =
    unsafePerformIO (writeRef r (Box a)) `seq` return ()
  unsafeIOToRef = return . unsafePerformIO
  maybeUnsafeRefToIO = Nothing

instance MonadCont m ⇒ MonadCont (RefT s m) where
  callCC f = RefT (callCC (\k → unRefT (f (RefT . k))))

instance MonadError e m ⇒ MonadError e (RefT s m) where
  throwError = RefT . throwError
  catchError m h = RefT (catchError (unRefT m) (unRefT . h))

instance MonadReader r m ⇒ MonadReader r (RefT s m) where
  ask     = RefT ask
  local f = RefT . local f . unRefT

instance MonadState st m ⇒ MonadState st (RefT s m) where
  get     = RefT get
  put     = RefT . put

instance MonadWriter w m ⇒ MonadWriter w (RefT s m) where
  tell    = RefT . tell
  listen  = RefT . listen . unRefT
  pass    = RefT . pass . unRefT

instance MonadIO m ⇒ MonadIO (RefT s m) where
  liftIO  = RefT . liftIO

---
--- Other MonadRef instances
---

instance MonadRef IORef IO where
  newRef   = newIORef
  readRef  = readIORef
  writeRef = writeIORef
  unsafeIOToRef    = id
  maybeUnsafeRefToIO    = Just id

instance MonadRef (STRef s) (ST s) where
  newRef   = newSTRef
  readRef  = readSTRef
  writeRef = writeSTRef
  unsafeIOToRef    = unsafeIOToST
  maybeUnsafeRefToIO    = Just unsafeSTToIO

instance MonadRef TVar STM where
  newRef   = newTVar
  readRef  = readTVar
  writeRef = writeTVar
  unsafeIOToRef = unsafeIOToSTM
  maybeUnsafeRefToIO = Nothing

instance MonadRef p m ⇒ MonadRef p (ContT r m) where
  newRef a     = lift $ newRef a
  readRef r    = lift $ readRef r
  writeRef r a = lift $ writeRef r a
  unsafeIOToRef    = lift . unsafeIOToRef
  maybeUnsafeRefToIO    = withUnsafeRefToIO (\next m → do
    r ← newIORef Nothing
    next . runContT m $ \a → do
      unsafeIOToRef (writeIORef r (Just a))
      return (error "ContT#maybeUnsafeRefToIO: observed return value")
    ma ← readIORef r
    maybe (fail "ContT#maybeUnsafeRefToIO: empty IORef") return ma)

instance (Show e, Error e, MonadRef p m) ⇒ MonadRef p (ErrorT e m) where
  newRef a     = lift $ newRef a
  readRef r    = lift $ readRef r
  writeRef r a = lift $ writeRef r a
  unsafeIOToRef         = lift . unsafeIOToRef
  maybeUnsafePerformRef = withUnsafePerformRef (\next m → next $ do
    r ← runErrorT m
    case r of
      Left e  → fail (show e)
      Right a → return a)

instance MonadRef p m ⇒ MonadRef p (ListT m) where
  newRef a     = lift $ newRef a
  readRef r    = lift $ readRef r
  writeRef r a = lift $ writeRef r a
  unsafeIOToRef         = lift . unsafeIOToRef
  maybeUnsafePerformRef = withUnsafePerformRef (\next →
    next . (liftM head . runListT))

instance (Defaultable r, Defaultable s, Monoid w, MonadRef p m) ⇒
         MonadRef p (RWST r w s m) where
  newRef a     = lift $ newRef a
  readRef r    = lift $ readRef r
  writeRef r a = lift $ writeRef r a
  unsafeIOToRef         = lift . unsafeIOToRef
  maybeUnsafePerformRef = withUnsafePerformRef (\next m →
    next . liftM fst $ evalRWST m getDefault getDefault)

instance (Defaultable r, MonadRef p m) ⇒ MonadRef p (ReaderT r m) where
  newRef a     = lift $ newRef a
  readRef r    = lift $ readRef r
  writeRef r a = lift $ writeRef r a
  unsafeIOToRef    = lift . unsafeIOToRef
  maybeUnsafePerformRef = withUnsafePerformRef (\next →
    next . flip runReaderT getDefault)

instance (Defaultable s, MonadRef p m) ⇒ MonadRef p (StateT s m) where
  newRef a     = lift $ newRef a
  readRef r    = lift $ readRef r
  writeRef r a = lift $ writeRef r a
  unsafeIOToRef    = lift . unsafeIOToRef
  maybeUnsafePerformRef = withUnsafePerformRef (\next →
    next . flip evalStateT getDefault)

instance (Monoid w, MonadRef p m) ⇒ MonadRef p (WriterT w m) where
  newRef a     = lift $ newRef a
  readRef r    = lift $ readRef r
  writeRef r a = lift $ writeRef r a
  unsafeIOToRef    = lift . unsafeIOToRef
  maybeUnsafePerformRef = withUnsafePerformRef (\next →
    next . liftM fst . runWriterT)
