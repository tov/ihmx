{-#
  LANGUAGE
    DeriveFunctor,
    FlexibleInstances,
    GeneralizedNewtypeDeriving,
    RankNTypes,
    TypeSynonymInstances,
    UnicodeSyntax
  #-}
module Defaultable (
  Defaultable(..),
  DefaultMin(..), DefaultMax(..), DefaultMempty(..), DefaultEmpty(..),
  Extractable(..), ExtractableT(..),
) where

import Control.Applicative

import Control.Monad.Identity
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

{-
import Control.Monad.ST
import Control.Monad.STM
import Unsafe.Coerce
-}

import System.IO.Unsafe
import Data.IORef

import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

import qualified Data.Graph.Inductive.Graph    as Gr
import qualified Data.Graph.Inductive.PatriciaTree as Gr
import qualified Data.Graph.Inductive.NodeMap  as Gr

class Defaultable a where
  getDefault ∷ a

class Extractable f where
  extract     ∷ f a → a
  extract     = extractMsg' id
  extractMsg  ∷ String → f a → a
  extractMsg  = extractMsg' . const
  extractMsg' ∷ (String → String) → f a → a
  extractMsg' = const extract

class ExtractableT t where
  extractT     ∷ Monad m ⇒ t m a → m a
  extractT     = extractMsgT' id
  extractMsgT  ∷ Monad m ⇒ String → t m a → m a
  extractMsgT  = extractMsgT' . const
  extractMsgT' ∷ Monad m ⇒ (String → String) → t m a → m a
  extractMsgT' = const extractT

---
--- Defaultable instances
---

instance (Defaultable a, Defaultable b) ⇒ Defaultable (a, b) where
  getDefault = (getDefault, getDefault)

instance (Defaultable a, Defaultable b, Defaultable c) ⇒
         Defaultable (a, b, c) where
  getDefault = (getDefault, getDefault, getDefault)

instance (Defaultable a, Defaultable b, Defaultable c, Defaultable d) ⇒
         Defaultable (a, b, c, d) where
  getDefault = (getDefault, getDefault, getDefault, getDefault)

instance (Defaultable a, Defaultable b, Defaultable c,
          Defaultable d, Defaultable e) ⇒
         Defaultable (a, b, c, d, e) where
  getDefault = (getDefault, getDefault, getDefault,
                getDefault, getDefault)

instance (Defaultable a, Defaultable b, Defaultable c,
          Defaultable d, Defaultable e, Defaultable f) ⇒
         Defaultable (a, b, c, d, e, f) where
  getDefault = (getDefault, getDefault, getDefault,
                getDefault, getDefault, getDefault)

instance (Defaultable ()) where
  getDefault = ()

instance Defaultable (Map.Map k a) where
  getDefault = Map.empty

instance Defaultable (Set.Set a) where
  getDefault = Set.empty

instance Ord a ⇒ Defaultable (Gr.NodeMap a) where
  getDefault = Gr.new

instance Defaultable (Gr.Gr a b) where
  getDefault = Gr.empty

newtype DefaultMin a    = DefaultMin { defaultMin ∷ a }
newtype DefaultMax a    = DefaultMax { defaultMax ∷ a }
newtype DefaultMempty a = DefaultMempty { defaultMempty ∷ a }
newtype DefaultEmpty f  = DefaultEmpty { defaultEmpty ∷ ∀ a. f a }

instance Bounded a ⇒ Defaultable (DefaultMin a) where
  getDefault = DefaultMin minBound

instance Bounded a ⇒ Defaultable (DefaultMax a) where
  getDefault = DefaultMax maxBound

instance Monoid a ⇒ Defaultable (DefaultMempty a) where
  getDefault = DefaultMempty mempty

instance Alternative f ⇒ Defaultable (DefaultEmpty f) where
  getDefault = DefaultEmpty empty

---
--- Extractable instances
---

{-
instance Extractable IO where
  extract = unsafePerformIO

instance Extractable STM where
  extract = extract . atomically

instance Extractable (ST s) where
  extract = runST . unsafeCoerce
-}

instance Extractable Identity where
  extract = runIdentity

instance Extractable (Cont r) where
  extractMsg' s = runIdentity . extractMsgT' s

instance Show e ⇒ Extractable (ErrorT e Identity) where
  extractMsg' s = runIdentity . extractMsgT' s

instance Extractable Maybe where
  extractMsg' = fromMaybe . error . ($ "extract (Maybe): got Nothing")

instance Show a ⇒ Extractable (Either a) where
  extractMsg' s = extractMsg' s . ErrorT . Identity

instance Extractable [] where
  extractMsg' s = extractMsg' s . ListT . Identity

instance Extractable (ListT Identity) where
  extractMsg' s = runIdentity . extractMsgT' s

instance (Defaultable r, Monoid w, Defaultable s) ⇒
         Extractable (Strict.RWS r w s) where
  extractMsg' s = runIdentity . extractMsgT' s

instance (Defaultable r, Monoid w, Defaultable s) ⇒
         Extractable (Lazy.RWS r w s) where
  extractMsg' s = runIdentity . extractMsgT' s

instance Defaultable r ⇒ Extractable (Reader r) where
  extractMsg' s = runIdentity . extractMsgT' s

instance Defaultable s ⇒ Extractable (Strict.State s) where
  extractMsg' s = runIdentity . extractMsgT' s

instance Defaultable s ⇒ Extractable (Lazy.State s) where
  extractMsg' s = runIdentity . extractMsgT' s

instance Monoid w ⇒ Extractable (Strict.Writer w) where
  extractMsg' s = runIdentity . extractMsgT' s

instance Monoid w ⇒ Extractable (Lazy.Writer w) where
  extractMsg' s = runIdentity . extractMsgT' s

---
--- ExtractableT instances
---

instance ExtractableT (ContT r) where
  extractMsgT' s m  = do
    let r = unsafePerformIO (newIORef Nothing)
    runContT m $ \a → do
      unsafePerformIO (writeIORef r (Just a)) `seq`
        return (error (s "extractT (ContT): observed return"))
    maybe (fail (s "maybeObserveT (ContT): empty IORef"))
          return
          (unsafePerformIO (readIORef r))

instance Show e ⇒ ExtractableT (ErrorT e) where
  extractT m = runErrorT m >>= either (fail . show) return

instance ExtractableT ListT where
  extractMsgT' s m =
    runListT m >>=
      foldr (const . return)
            (fail (s "extractT (ListT): empty list"))

instance (Defaultable r, Monoid w, Defaultable s) ⇒
         ExtractableT (Strict.RWST r w s) where
  extractT m = fst `liftM` Strict.evalRWST m getDefault getDefault

instance (Defaultable r, Monoid w, Defaultable s) ⇒
         ExtractableT (Lazy.RWST r w s) where
  extractT m = fst `liftM` Lazy.evalRWST m getDefault getDefault

instance Defaultable r ⇒ ExtractableT (ReaderT r) where
  extractT m = runReaderT m getDefault

instance Defaultable s ⇒ ExtractableT (Strict.StateT s) where
  extractT m = Strict.evalStateT m getDefault

instance Defaultable s ⇒ ExtractableT (Lazy.StateT s) where
  extractT m = Lazy.evalStateT m getDefault

instance Monoid w ⇒ ExtractableT (Strict.WriterT w) where
  extractT m = fst `liftM` Strict.runWriterT m

instance Monoid w ⇒ ExtractableT (Lazy.WriterT w) where
  extractT m = fst `liftM` Lazy.runWriterT m

