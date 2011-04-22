{-#
  LANGUAGE
    FlexibleContexts,
    FlexibleInstances,
    MultiParamTypeClasses,
    FunctionalDependencies,
    TypeSynonymInstances,
    UnicodeSyntax
  #-}
module NodeMap (
  MonadNM(..),
  module Data.Graph.Inductive.NodeMap,
  NodeMapT, runNodeMapT, runNodeMapT_,
) where

import Data.Graph.Inductive (DynGraph, LNode, LEdge)
import Data.Graph.Inductive.NodeMap
  hiding (mkNodeM, mkNodesM, mkEdgeM, mkEdgesM,
          insMapNodeM, insMapEdgeM, delMapNodeM, delMapEdgeM,
          insMapNodesM, insMapEdgesM, delMapNodesM, delMapEdgesM)
import Control.Monad.State

class (Ord a, DynGraph g, MonadState (NodeMap a, g a b) m) ⇒
      MonadNM a b g m | m → a b g where
  mkNodeM       ∷ a → m (LNode a)
  mkNodesM      ∷ [a] → m [LNode a]
  mkEdgeM       ∷ (a, a, b) → m (Maybe (LEdge b))
  mkEdgesM      ∷ [(a, a, b)] → m (Maybe [LEdge b])
  insMapNodeM   ∷ a → m (LNode a)
  insMapEdgeM   ∷ (a, a, b) → m ()
  delMapNodeM   ∷ a → m ()
  delMapEdgeM   ∷ (a, a) → m ()
  insMapNodesM  ∷ [a] → m [LNode a]
  insMapEdgesM  ∷ [(a, a, b)] → m ()
  delMapNodesM  ∷ [a] → m ()
  delMapEdgesM  ∷ [(a, a)] → m ()
  mkNodeM       = modifyNM . flip mkNode
  mkNodesM      = modifyNM . flip mkNodes
  mkEdgeM e     = gets (flip mkEdge e . fst)
  mkEdgesM es   = gets (flip mkEdges es . fst)
  insMapNodeM   = modifyNMG . flip insMapNode
  insMapEdgeM   = modifyG . flip insMapEdge
  delMapNodeM   = modifyG . flip delMapNode
  delMapEdgeM   = modifyG . flip delMapEdge
  insMapNodesM  = modifyNMG . flip insMapNodes
  insMapEdgesM  = modifyG . flip insMapEdges
  delMapNodesM  = modifyG . flip delMapNodes
  delMapEdgesM  = modifyG . flip delMapEdges

modifyNMG   ∷ MonadNM a b g m ⇒
              (NodeMap a → g a b → (g a b, NodeMap a, r)) → m r
modifyNMG f = do
  (nm, g) ← get
  let (g', nm', r) = f nm g
  put (nm', g')
  return r

modifyG     ∷ MonadNM a b g m ⇒ (NodeMap a → g a b → g a b) → m ()
modifyG f   = do
  (nm, g) ← get
  put (nm, f nm g)

modifyNM    ∷ MonadNM a b g m ⇒ (NodeMap a → (r, NodeMap a)) → m r
modifyNM f  = do
  (nm, g) ← get
  let (r, nm') = f nm
  put (nm', g)
  return r

type NodeMapT a b g m r = StateT (NodeMap a, g a b) m r

instance (Ord a, DynGraph g, Monad m) ⇒
         MonadNM a b g (StateT (NodeMap a, g a b) m)

runNodeMapT  ∷ (DynGraph g, Ord a, Monad m) ⇒
               NodeMap a → g a b → NodeMapT a b g m r →
               m (r, (NodeMap a, g a b))
runNodeMapT nm g m = runStateT m (nm, g)

runNodeMapT_ ∷ (DynGraph g, Ord a, Monad m) ⇒
               g a b → NodeMapT a b g m r →
               m (g a b)
runNodeMapT_ g m = (snd . snd) `liftM` runNodeMapT (fromGraph g) g m

