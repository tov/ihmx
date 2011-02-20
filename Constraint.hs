{-#
  LANGUAGE
    FlexibleInstances,
    FunctionalDependencies,
    ImplicitParams,
    MultiParamTypeClasses,
    TupleSections,
    UnicodeSyntax
  #-}
module Constraint (
  -- * Generic constraints
  Constraint(..), (~≤~),
  -- * An implementation
  SubtypeConstraint
) where

import qualified Data.List  as List
import qualified Data.Map   as Map
import qualified Data.Set   as Set
import qualified Data.Tree  as Tree

-- From fgs:
import Data.Graph.Inductive.PatriciaTree (Gr)
import Data.Graph.Inductive.Basic        (preorder)
import qualified Data.Graph.Inductive.Graph     as Gr
import qualified Data.Graph.Inductive.NodeMap   as NM
import qualified Data.Graph.Inductive.Query.DFS as DFS

import Syntax
import MonadU
import Util

---
--- Abstract constraints
---

class (Ftv c r, Monoid c) ⇒ Constraint c r | c → r where
  -- | The trivial constraint
  (⊤)        ∷ c
  (⊤)        = mempty
  -- | A conjunction of constraints
  (⋀)        ∷ c → c → c
  (⋀)        = mappend
  -- | A subtype constraint
  (≤)        ∷ Type r → Type r → c
  -- | A subtype constraint in the given variance
  relate     ∷ Variance → Type r → Type r → c
  relate v τ τ' = case v of
    Covariant     → τ ≤ τ'
    Contravariant → τ' ≤ τ
    Invariant     → τ ≤ τ' ⋀ τ' ≤ τ
    Omnivariant   → (⊤)
  --
  -- | Generalize a type under a constraint and environment,
  --   given whether the the value restriction is satisfied or not
  gen        ∷ (MonadU r m, Ftv γ r) ⇒
               Bool → c → γ → Type r → m (Type r, c)

infixr 4 ⋀
infix  5 ≤

-- | Generate the constraints to subtype-unify two types.  If both
--   types are type variables, return them as a pair (Right); otherwise
--   return the new constraint to solve and a list of affect
--   (substituted) type variables.
(~≤~) ∷ (Constraint c r, MonadU r m) ⇒
        Type r → Type r → m (Either (c, [r]) (r, r))
τ0 ~≤~ τ0' = do
  τ1  ← deref τ0
  τ1' ← deref τ0'
  case (τ1, τ1') of
    (VarTy (FreeVar α), VarTy (FreeVar β))
      | α == β
      → return (Left ((⊤), []))
      | otherwise
      → return (Right (α, β))
    (ConTy c τs,        ConTy c' τs')
      | c == c'
      → let cs = zipWith3 relate (getVariances c (length τs)) τs τs'
         in return (Left (mconcat cs, []))
      | otherwise
      → fail $ "Could not unify type constructors: " ++ c ++ " and " ++ c'
    (VarTy (FreeVar α), ConTy c' τs')
      → expandVar (≤) α c' τs'
    (ConTy c τs,        VarTy (FreeVar β))
      → expandVar (flip (≤)) β c τs
    (_,                 _)
      → do
        τ2  ← derefAll τ1
        τ2' ← derefAll τ1'
        fail $ "Could not unify: " ++ show τ2 ++ " ≤ " ++ show τ2'
  where
    expandVar (≤≥) α c τs = do
      βs ← ftv τs
      when (α `elem` βs) $ fail "Occurs check failed"
      αs ← replicateM (length τs) newTVTy
      let τ = ConTy c αs
      writeTV α τ
      return (Left (τ ≤≥ ConTy c τs, [α]))

---
--- An implementation of constraints
---

-- | Simple subtype constraints
newtype SubtypeConstraint r
  = SC {
      unSC ∷ [(Type r, Type r)]
    }
  deriving (Show)

instance Monoid (SubtypeConstraint r) where
  mempty      = SC []
  mconcat     = SC . concat . map unSC
  mappend c d = mconcat [c, d]

instance Ord r ⇒ Ftv (SubtypeConstraint r) r where
  ftvTree = ftvTree . unSC

instance Tv r ⇒ Constraint (SubtypeConstraint r) r where
  τ ≤ τ' = SC [(τ, τ')]
  --
  -- Generalization proceeds in several steps:
  --
  --  1. atomize: subtype-unify all subtype constraints until we have
  --     constraints only on type variables, which we consider as a
  --     directed graph.
  --
  --  3. existentials: any type variables that appear in the constraint
  --     but not the type nor context can be existentially quantified in
  --     the constraint; we eliminate each of them by connecting all its
  --     predecessors to all its successors.
  --
  --  4. scc: each strongly-connected component is coalesced into one
  --     type variable.
  --
  --  5. untransitive: (NOT IMPLEMENTED) remove redundant edges that
  --     are implied by transitivity.
  --
  --  6. singles:
  --      - type variables that appear in the type exactly once in
  --        positive position, if they have no lower bound (no in-edges)
  --        in the constraint, are made unconstrained.
  --      - dually, for once-appearing negative sinks
  --      - once-appearing, positive type variables with exactly one
  --        lower bound (in degree 1) are unified with their lower bound
  --      - dually, for once-appearing negative of out degree 1
  --
  --  7. components: coalesce and remove any components that consist only
  --     of generalization candidates:
  --      - if we're dealing with a value, ftv τ \ ftv γ
  --      - otherwise, limit the above those that appear only positively
  --        or only negatively in τ
  --
  --  8. reconstruct: turn the graph back into a constraint
  --
  --  9. generalize: candidates that are not free in the constraint
  gen value (SC c0) γ τ = do
    trace ("gen (begin)", c0, τ)
    let ?deref = readTV
    c1           ← atomize c0 []
    γftv         ← ftvSet γ
    τftv         ← ftvVs τ
    trace ("gen (atomize)", c1, γftv, τftv, τ)
    let (nm, g) = buildGraph c1
    g            ← eliminateExistentials nm (g, γftv, τftv)
    trace ("gen (existentials)", reconstruct g, γftv, τftv, τ)
    (g, γftv, τftv)
                 ← coalesceSCCs (g, γftv, τftv)
    trace ("gen (scc)", reconstruct g, γftv, τftv, τ)
    (g, γftv, τftv)
                 ← removeSingles nm (g, γftv, τftv)
    trace ("gen (singles)", reconstruct g, γftv, τftv, τ)
    (g, γftv, τftv)
                 ← coalesceComponents value (g, γftv, τftv)
    trace ("gen (components)", reconstruct g, γftv, τftv, τ)
    let c        = reconstruct g
    σ            ← generalizeNow value c γftv τftv τ
    trace ("gen (generalize)", σ)
    return (σ, c)
    where
      -- atomize takes a list of subtype constraint pairs and a list
      -- of type variables, and returns when all the constraint is
      -- reduced to pairs of type variables.
      atomize []           done = return done
      atomize ((τ, τ'):c') done = do
        ec ← τ ~≤~ τ'
        case ec of
          Left (SC c'', αs) →
            let hasChanged (β,β') = β `elem` αs || β' `elem` αs
                (changed, done')  = List.partition hasChanged done
                liftTy            = map (first fvTy . second fvTy)
             in atomize (c'' ++ liftTy changed ++ c') done'
          Right (α, β)      → atomize c' ((α, β):done)
      --
      -- Given a list of pairs, build the graph
      buildGraph pairs =
        snd . NM.run (Gr.empty ∷ Gr r ()) $ do
          NM.insMapNodesM (map fst pairs)
          NM.insMapNodesM (map snd pairs)
          NM.insMapEdgesM [ (α, α', ()) | (α, α') ← pairs ]
          return ()
      --
      -- Eliminate existentially-quantified type variables from the
      -- constraint
      eliminateExistentials nm (g, γftv, τftv) = do
        cftv ← ftvSet (map snd (Gr.labNodes g))
        let extvs = cftv Set.\\ (γftv `Set.union` Map.keysSet τftv)
        return (Set.fold (eliminateNode nm) g extvs)
        where
      -- Given a node label and a graph, remove the node, connecting
      -- all its predecessors to all its successors.
      eliminateNode nm α g =
        Gr.insEdges [ (n1, n2, ())
                    | n1 ← Gr.pre g node, n1 /= node
                    , n2 ← Gr.suc g node, n2 /= node ]
                    (Gr.delNode node g)
        where node = nmLab nm α
      --
      -- Remove once-appearing type variables if covariant-source or
      -- contravariant-sink.  We may have to iterate several times,
      -- since removing a variable may cause another to need to be
      -- removed
      removeSingles nm state0 = iter state0
        where
          iter state = do
            (changed, state') ←
              foldM tryRemove (False, state) (findSingles (prj3 state))
            if changed
              then iter state'
              else return state'
          tryRemove (changed, state@(g, γftv, τftv)) (node, variance) = do
            case (Gr.lab g node, variance, Gr.pre g node, Gr.suc g node) of
              (Nothing, _, _, _) →
                  return (changed, state)
              (_, Covariant, [], _) →
                  return (True, (Gr.delNode node g, γftv, τftv))
              (_, Contravariant, _, []) →
                  return (True, (Gr.delNode node g, γftv, τftv))
              (_, Covariant, [pred], _) →
                  (True,) <$> coalesce node pred state
              (_, Contravariant, _, [succ]) →
                  (True,) <$> coalesce node succ state
              _   → return (changed, state)
          findSingles = Map.foldWithKey keep []
          keep α [1]  = ((nmLab nm α, Covariant):)
          keep α [-1] = ((nmLab nm α, Contravariant):)
          keep _ _    = id
      --
      -- Coalesce the strongly-connected components to single type
      -- variables
      coalesceSCCs state = foldM coalesceList state (DFS.scc (prj1 state))
      -- Given a list of type variables, coalesce them to one type
      -- variable (by assigning the first of the list to all the rest)
      coalesceList acc []     = return acc
      coalesceList acc (n:ns) = foldM (\acc n' -> coalesce n' n acc) acc ns
      -- Assign n2 to n1, updating the graph, type variables, and ftvs
      coalesce n1 n2 (g, γftv, τftv) = do
        let Just α1 = Gr.lab g n1
            Just α2 = Gr.lab g n2
        (γftv', τftv') ← assignTV α1 α2 (γftv, τftv)
        return (assignNode n1 n2 g, γftv', τftv')
      -- Update the graph to remove node n1, assigning all of its
      -- neighbors to n2
      assignNode n1 n2 g =
        Gr.insEdges [ (n', n2, ())
                    | n' ← Gr.pre g n1, n' /= n1, n' /= n2 ] $
        Gr.insEdges [ (n2, n', ())
                    | n' ← Gr.suc g n1, n' /= n1, n' /= n2 ] $
        Gr.delNode n1 g
      -- Update the type variables to assign α2 to α1, updating the
      -- ftvs appropriately
      assignTV α1 α2 (γftv, τftv) = do
        writeTV α1 (fvTy α2)
        return (assignFtvSet α1 α2 γftv, assignFtvMap α1 α2 τftv)
      -- Given two type variables, where α1 ← α2, update a set of free
      -- type variables accordingly
      assignFtvSet α1 α2 set =
        if Set.member α1 set
          then Set.insert α2 (Set.delete α1 set)
          else set
      -- Given two type variables, where α1 ← α2, update a map of free
      -- type variables to variance lists accordingly
      assignFtvMap α1 α2 vmap =
        case Map.lookup α1 vmap of
          Just vs → Map.insertWith (++) α2 vs (Map.delete α1 vmap)
          Nothing → vmap
      -- Coalesce and remove fully-generalizable components
      coalesceComponents value (g, γftv, τftv) =
        let candidates = genCandidates value τftv γftv
            each state component@((node,_):_)
              | all (`Set.member` candidates) (map snd component)
              = do
                (g', γftv', τftv') ← coalesceList state (map fst component)
                return (Gr.delNode node g', γftv', τftv')
            each state _
              = return state
         in foldM each (g, γftv, τftv) (labComponents g)
      -- Find the generalization candidates, which are free in τ but
      -- not in γ (restricted further if not a value)
      genCandidates value τftv γftv =
        Map.keysSet (restrict τftv) Set.\\ γftv
          where
          restrict = if value
                       then id
                       else Map.filter ((`elem` [-1, 1]) . sum)
      -- Reconstruct a constraint from the remaining graph
      reconstruct g = SC $ do
        (n1, n2) ← Gr.edges g
        let Just α1 = Gr.lab g n1
            Just α2 = Gr.lab g n2
        return (fvTy α1, fvTy α2)
      -- Generalize the type, leaving out any type variables remaining
      -- in the constraint
      generalizeNow value c γftv τftv τ = do
        cftv     ← ftvSet c
        let αs   = genCandidates value τftv (γftv `Set.union` cftv)
        closeWith AllQu (Set.toList αs) <$> derefAll τ

-- | Look up the node index of a node label
nmLab ∷ Ord a ⇒ NM.NodeMap a → a → Gr.Node
nmLab = fst <$$> NM.mkNode_

-- | Partition a graph into components of /labeled/ nodes
labComponents ∷ Gr.Graph gr ⇒ gr a b → [[Gr.LNode a]]
labComponents = componentsWith Gr.labNode'
  where
  udffWith ∷ Gr.Graph gr ⇒ DFS.CFun a b c → [Gr.Node] → gr a b → [Tree.Tree c]
  udffWith = DFS.xdffWith Gr.neighbors'
  --
  udffWith' ∷ Gr.Graph gr ⇒ DFS.CFun a b c → gr a b → [Tree.Tree c]
  udffWith' f g = udffWith f (Gr.nodes g) g
  --
  componentsWith ∷ Gr.Graph gr ⇒ DFS.CFun a b c → gr a b → [[c]]
  componentsWith = map preorder <$$> udffWith'
