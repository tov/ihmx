{-#
  LANGUAGE
    UnicodeSyntax
  #-}
module Graph (
  ShowGraph(..),
  trcnr, untransitive, transitiveReduce, nmLab, labelNode, labScc,
  labComponents, labNodeEdges,
  module Data.Graph.Inductive.Basic,
  module Data.Graph.Inductive.Graph,
  module Data.Graph.Inductive.Query.DFS,
  module Data.Graph.Inductive.Query.TransClos,
) where

import qualified Data.List as List
import qualified Data.Tree as Tree

-- From fgs:
import Data.Graph.Inductive.PatriciaTree (Gr)
import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Query.DFS
import Data.Graph.Inductive.Query.TransClos

-- Mine:
import qualified NodeMap as NM
import Util hiding (empty)
import Defaultable

-- | Transitive, non-reflexive closure
trcnr ∷ DynGraph gr ⇒ gr a b → gr a ()
trcnr g = insEdges newEdges (insNodes lns empty) where
  lns      = labNodes g
  newEdges = [ (n, n', ())
             | (n, _) ← lns
             , n'     ← reachable n g
             , n /= n' ]

-- | Compute the transitive reduction of a transitive graph.
untransitive ∷ DynGraph gr ⇒ gr a b → gr a b
untransitive g =
  let redundant = [ (n1, n2)
                  | (n1, n2) ← edges g
                  , n'       ← suc g n1
                  , n' /= n2
                  , n' /= n1
                  , n2 `elem` suc g n' ]
   in delEdges redundant g

-- | Compute the transitive reduction of a graph.
transitiveReduce ∷ DynGraph gr ⇒ gr a b → gr a b
transitiveReduce g =
  let gPlus     = trc g
      redundant = [ (n1, n2)
                  | (n1, n2) ← edges g
                  , n'       ← suc g n1
                  , n' /= n2
                  , n2 `elem` suc gPlus n' ]
   in delEdges redundant g

-- | Look up the node index of a node label
nmLab ∷ Ord a ⇒ NM.NodeMap a → a → Node
nmLab = fst <$$> NM.mkNode_

labelNode ∷ Graph gr ⇒ gr a b → Node → LNode a
labelNode g n = case lab g n of
  Just ln → (n, ln)
  Nothing → error "labelNode: node not found"

labScc ∷ Graph gr ⇒ gr a b → [[LNode a]]
labScc g = map preorder (rdffWith labNode' (topsort g) g)
  where
  rdffWith :: Graph gr ⇒ CFun a b c → [Node] → gr a b → [Tree.Tree c]
  rdffWith = xdffWith pre'

-- | Partition a graph into components of /labeled/ nodes
labComponents ∷ Graph gr ⇒ gr a b → [[LNode a]]
labComponents = componentsWith labNode'
  where
  udffWith ∷ Graph gr ⇒ CFun a b c → [Node] → gr a b → [Tree.Tree c]
  udffWith = xdffWith neighbors'
  --
  udffWith' ∷ Graph gr ⇒ CFun a b c → gr a b → [Tree.Tree c]
  udffWith' f g = udffWith f (nodes g) g
  --
  componentsWith ∷ Graph gr ⇒ CFun a b c → gr a b → [[c]]
  componentsWith = preorder <$$$> udffWith'

-- | Get the edges of a graph as pairs of node labels
labNodeEdges ∷ Graph gr ⇒ gr n e → [(n, n)]
labNodeEdges g =
  [ (α, β)
  | (n1, n2) ← edges g
  , let Just α = lab g n1
  , let Just β = lab g n2
  ]

-- | For showing graphs
newtype ShowGraph gr v = ShowGraph { unShowGraph ∷ gr v () }

instance (Graph gr, Show v) ⇒ Show (ShowGraph gr v) where
  showsPrec _ (ShowGraph gr) =
    showChar '{' .
    foldr (.) id
      (List.intersperse (showString " ⋀ ")
         [ shows n1 . showChar '≤' . shows n2
         | (n1, n2) ← labNodeEdges gr ])
    . showChar '}'

instance Ord a ⇒ Defaultable (NM.NodeMap a) where
  getDefault = NM.new

instance Defaultable (Gr a b) where
  getDefault = empty

