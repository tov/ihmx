{-# LANGUAGE
      FlexibleContexts,
      FlexibleInstances,
      FunctionalDependencies,
      MultiParamTypeClasses,
      UnicodeSyntax
    #-}
{- | From Simonet's Dalton constraint solver -}
module UnionFind (
  -- * Generic Union-Find
  UnionFind(..),
  -- * An implementation on top of 'MonadRef'
  Proxy,
) where

import MonadRef
import Util
import Eq1

-- | A class for implementing union-find. Minimal definition:
--   @create@, @follow@, and @replace@.  Given those, the default
--   implementations of the other methods perform path compression.
class (Monad m, Eq1 p) ⇒ UnionFind p m where
  -- | To create a new set with the given representative
  create  ∷ a → m (p a)
  -- | To follow a link, either to the end or to another link
  follow  ∷ p a → m (Either a (p a))
  -- | To replace the contents of a link with a representative
  --   or another link
  replace ∷ p a → Either a (p a) → m ()

  -- | Find the representative of a set
  repr    ∷ p a → m (p a)
  repr    = liftM fst . loop where
    loop proxy = do
      link ← follow proxy
      case link of
        Left _       → return (proxy, False)
        Right proxy' → do
          (proxy'', changed) ← loop proxy'
          when changed $ replace proxy (Right proxy'')
          return (proxy'', True)

  -- | Find the descriptor of a set
  desc     ∷ p a → m a
  desc proxy = do
    link ← follow proxy
    case link of
      Left a       → return a
      Right proxy' → desc =<< repr proxy'

  -- | Change the descriptor of a set
  setDesc ∷ p a → a → m ()
  setDesc proxy a = flip replace (Left a) =<< repr proxy

  -- | Join two proxies, using the given function to combine their
  --   descriptors.
  coalesce ∷ (a → a → m a) → p a → p a → m ()
  coalesce combine proxy1 proxy2 = unless (proxy1 `eq1` proxy2) $ do
    proxy1' ← repr proxy1
    proxy2' ← repr proxy2
    a1 ← desc proxy1'
    a2 ← desc proxy2'
    a' ← combine a1 a2
    replace proxy1' (Right proxy2')
    replace proxy2' (Left a')

  -- | Make the first proxy point to the second, keeping the second
  --   proxy's descriptor
  linkto ∷ p a → p a → m ()
  linkto = coalesce (const return)

  -- | Is the given proxy object the representative of its set?
  isRepr ∷ p a → m Bool
  isRepr = liftM (either (const True) (const False)) . follow

  -- | Are two proxy objects from the same set?
  sameRepr ∷ p a → p a → m Bool
  sameRepr proxy1 proxy2 = liftM2 eq1 (repr proxy1) (repr proxy2)

---
--- An implementation
---

newtype Proxy p a = Proxy { unProxy ∷ p (Either a (Proxy p a)) }

instance Eq1 p ⇒ Eq1 (Proxy p) where
  Proxy p1 `eq1` Proxy p2 = p1 `eq1` p2

instance MonadRef r m ⇒ UnionFind (Proxy r) m where
  create   = liftM Proxy . newRef . Left
  follow   = readRef . unProxy
  replace  = writeRef . unProxy

