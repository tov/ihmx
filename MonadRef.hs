{-#
  LANGUAGE
    FlexibleInstances,
    FunctionalDependencies,
    GeneralizedNewtypeDeriving,
    MultiParamTypeClasses,
    RankNTypes,
    TypeFamilies,
    UndecidableInstances,
    UnicodeSyntax
  #-}
module MonadRef (
  MonadRef(..),
  RefT, RefRef, runRefT, mapRefT,
  UnsafeReadRef(..),
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
import Control.Monad.RWS.Strict    as Strict
import Control.Monad.RWS.Lazy      as Lazy
import Control.Monad.Reader
import Control.Monad.State.Strict  as Strict
import Control.Monad.State.Lazy    as Lazy
import Control.Monad.Writer.Strict as Strict
import Control.Monad.Writer.Lazy   as Lazy

import System.IO.Unsafe

import Eq1

-- | A class for monads with mutable references. Provides generic
--   operations for creating, reading, writing, and modifying
--   references.
class (UnsafeReadRef p, Monad m, Eq1 p) ⇒ MonadRef p m | m → p where
  newRef    ∷ a → m (p a)
  readRef   ∷ p a → m a
  writeRef  ∷ p a → a → m ()
  modifyRef ∷ (a → a) → p a → m ()
  modifyRef f r = do
    a ← readRef r
    writeRef r (f a)

class UnsafeReadRef p where
  unsafeReadRef ∷ p a → a

---
--- A transformer version of ST
---

newtype RefT s m a = RefT { unRefT ∷ m a }
  deriving Monad

runRefT ∷ Monad m ⇒ (forall s. RefT s m a) → m a
runRefT m = unRefT m

mapRefT   ∷ (m a → m b) → RefT s m a → RefT s m b
mapRefT f = RefT . f . unRefT

liftCallCC :: (((a → m b) → m a) → m a) →
              ((a → RefT s m b) → RefT s m a) → RefT s m a
liftCallCC callCC f =
  RefT $ callCC $ \ c -> unRefT (f (RefT . c))

liftCatch ∷ (m a → (e → m a) → m a) →
            RefT s m a → (e → RefT s m a) → RefT s m a
liftCatch f m h = RefT $ f (unRefT m) (unRefT . h)

instance Monad m ⇒ Functor (RefT s m) where
  fmap  = liftM

instance Monad m ⇒ Applicative (RefT s m) where
  pure  = return
  (<*>) = ap

instance MonadTrans (RefT s) where
  lift = RefT

newtype RefRef s a = RefRef { unRefRef ∷ IORef (Box a) }
  deriving Eq

instance Eq1 (RefRef s) where eq1 = (==)
instance Eq2 RefRef where eq2 = (==)

data Box a = Box { unBox ∷ a }

instance Monad m ⇒ MonadRef (RefRef s) (RefT s m) where
  newRef a = return (RefRef (unsafePerformIO (newIORef (Box a))))
  readRef (RefRef r) =
    let a = unsafePerformIO (readIORef r)
     in a `seq` return (unBox a)
  writeRef (RefRef r) a =
    unsafePerformIO (writeRef r (Box a)) `seq` return ()

instance UnsafeReadRef (RefRef s) where
  unsafeReadRef = unBox . unsafePerformIO . readIORef . unRefRef

instance MonadCont m ⇒ MonadCont (RefT s m) where
  callCC = liftCallCC callCC

instance MonadError e m ⇒ MonadError e (RefT s m) where
  throwError = lift . throwError
  catchError = liftCatch catchError

instance MonadReader r m ⇒ MonadReader r (RefT s m) where
  ask     = lift ask
  local   = mapRefT . local

instance MonadState st m ⇒ MonadState st (RefT s m) where
  get     = lift get
  put     = lift . put

instance MonadWriter w m ⇒ MonadWriter w (RefT s m) where
  tell    = lift . tell
  listen  = mapRefT listen
  pass    = mapRefT pass

instance MonadIO m ⇒ MonadIO (RefT s m) where
  liftIO  = lift . liftIO

---
--- Other MonadRef instances
---

instance MonadRef IORef IO where
  newRef   = newIORef
  readRef  = readIORef
  writeRef = writeIORef

instance UnsafeReadRef IORef where
  unsafeReadRef = unsafePerformIO . readRef

instance MonadRef (STRef s) (ST s) where
  newRef   = newSTRef
  readRef  = readSTRef
  writeRef = writeSTRef

instance UnsafeReadRef (STRef s) where
  unsafeReadRef = unsafePerformIO . unsafeSTToIO . readRef

instance MonadRef TVar STM where
  newRef   = newTVar
  readRef  = readTVar
  writeRef = writeTVar

instance UnsafeReadRef TVar where
  unsafeReadRef = unsafePerformIO . atomically . readRef

instance MonadRef p m ⇒ MonadRef p (ContT r m) where
  newRef a     = lift $ newRef a
  readRef r    = lift $ readRef r
  writeRef r a = lift $ writeRef r a

instance (Show e, Error e, MonadRef p m) ⇒ MonadRef p (ErrorT e m) where
  newRef a     = lift $ newRef a
  readRef r    = lift $ readRef r
  writeRef r a = lift $ writeRef r a

instance MonadRef p m ⇒ MonadRef p (ListT m) where
  newRef a     = lift $ newRef a
  readRef r    = lift $ readRef r
  writeRef r a = lift $ writeRef r a

instance (Monoid w, MonadRef p m) ⇒
         MonadRef p (Strict.RWST r w s m) where
  newRef a     = lift $ newRef a
  readRef r    = lift $ readRef r
  writeRef r a = lift $ writeRef r a

instance (Monoid w, MonadRef p m) ⇒
         MonadRef p (Lazy.RWST r w s m) where
  newRef a     = lift $ newRef a
  readRef r    = lift $ readRef r
  writeRef r a = lift $ writeRef r a

instance (MonadRef p m) ⇒ MonadRef p (ReaderT r m) where
  newRef a     = lift $ newRef a
  readRef r    = lift $ readRef r
  writeRef r a = lift $ writeRef r a

instance (MonadRef p m) ⇒ MonadRef p (Strict.StateT s m) where
  newRef a     = lift $ newRef a
  readRef r    = lift $ readRef r
  writeRef r a = lift $ writeRef r a

instance (MonadRef p m) ⇒ MonadRef p (Lazy.StateT s m) where
  newRef a     = lift $ newRef a
  readRef r    = lift $ readRef r
  writeRef r a = lift $ writeRef r a

instance (Monoid w, MonadRef p m) ⇒ MonadRef p (Strict.WriterT w m) where
  newRef a     = lift $ newRef a
  readRef r    = lift $ readRef r
  writeRef r a = lift $ writeRef r a

instance (Monoid w, MonadRef p m) ⇒ MonadRef p (Lazy.WriterT w m) where
  newRef a     = lift $ newRef a
  readRef r    = lift $ readRef r
  writeRef r a = lift $ writeRef r a

