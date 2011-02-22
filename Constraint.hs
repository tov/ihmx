{-#
  LANGUAGE
    FlexibleInstances,
    FunctionalDependencies,
    ImplicitParams,
    MultiParamTypeClasses,
    ScopedTypeVariables,
    TupleSections,
    UnicodeSyntax
  #-}
module Constraint {-(
  -- * Generic constraints
  Constraint(..), (~≤~),
  -- * An implementation
  SubtypeConstraint,
) -}where

import qualified Data.List  as List
import qualified Data.Map   as Map
import qualified Data.Set   as Set
import qualified Data.Tree  as Tree

-- From fgs:
import Data.Graph.Inductive.PatriciaTree (Gr)
import Data.Graph.Inductive.Basic        (preorder)
import qualified Data.Graph.Inductive.Graph             as Gr
import qualified Data.Graph.Inductive.NodeMap           as NM
import qualified Data.Graph.Inductive.Query.DFS         as DFS
import qualified Data.Graph.Inductive.Query.TransClos   as TransClos

import Syntax
import MonadU
import Util
import Ppr

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

-- | We reduce constraints to inequalities on atoms, which are either
--   type variables or nullary type constructors.
data Atom tv = VarAt tv
             | ConAt Name
  deriving (Eq, Ord, Show)

instance Ppr tv ⇒ Ppr (Atom tv) where
  pprPrec p = pprPrec p . atomTy

instance Tv tv ⇒ Ftv (Atom tv) tv where
  ftvTree = ftvTree . atomTy

-- | To inject an atom into a type
atomTy ∷ Atom tv → Type tv
atomTy (VarAt α) = fvTy α
atomTy (ConAt n) = ConTy n []

---
--- The subtype order
---

-- | To compare two nullary type constructors
tyConNode  ∷ String → Gr.Node
tyConOrder ∷ Gr String ()
(tyConNode, tyConOrder) = (nmLab nm, TransClos.trc g)
  where
    (_, (nm, g)) = NM.run Gr.empty $ do
      NM.insMapNodesM [ "U", "R", "A", "L" ]
      NM.insMapEdgesM [ ("U","R",()), ("U","A",()), ("R","L",()), ("A","L",()) ]
      return ()

-- | Is one type constructor less than or equal to another?
tyConLe ∷ Name → Name → Bool
tyConLe c1 c2 = Gr.gelem n1 tyConOrder && n2 `elem` Gr.suc tyConOrder n1
  where
    n1 = tyConNode c1
    n2 = tyConNode c2

infix 4 `tyConLe`

-- | Are there any type constuctors greater or lesser than
--   this one?
tyConHasSuccs, tyConHasPreds ∷ Name → Bool
tyConHasSuccs c = Gr.gelem n tyConOrder && Gr.outdeg tyConOrder n > 1
  where n = tyConNode c
tyConHasPreds c = Gr.gelem n tyConOrder && Gr.indeg tyConOrder n > 1
  where n = tyConNode c

-- | Generate the constraints to subtype-unify two types.  If both
--   types are atoms, return them as a pair (Right); otherwise
--   return the new constraint to solve and a list of affect
--   (substituted) type variables.
(~≤~) ∷ (Constraint c tv, MonadU tv m) ⇒
        Type tv → Type tv → m (Either (c, [tv]) (Atom tv, Atom tv))
τ0 ~≤~ τ0' = do
  τ1  ← deref τ0
  τ1' ← deref τ0'
  case (τ1, τ1') of
    (VarTy (FreeVar α), VarTy (FreeVar β))
      | α == β
      → return (Left ((⊤), []))
      | otherwise
      → return (Right (VarAt α, VarAt β))
    (ConTy c [],        ConTy c' [])
      | c `tyConLe` c'
      → return (Left ((⊤), []))
    (VarTy (FreeVar α), ConTy c' [])
      | tyConHasPreds c'
      → return (Right (VarAt α, ConAt c'))
    (ConTy c [], VarTy (FreeVar β))
      | tyConHasSuccs c
      → return (Right (ConAt c, VarAt β))
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

{-
type CState r = (Gr (Atom r) (), Set.Set r, Map.Map r [Variance])
type LN r = Gr.LNode (Atom r)
-}

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
  --  5. untransitive: compute the transitive reduction of the graph,
  --     to remove redundant edges that are implied by transitivity.
  --
  --  6. singles:
  --      - type variables that appear in the type exactly once in
  --        positive position, if they have no lower bound (no in-edges)
  --        in the constraint, are made unconstrained
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
    checkSatisfiable g -- add to list
    g            ← eliminateExistentials nm (g, γftv, τftv)
    trace ("gen (existentials)", reconstruct g, γftv, τftv, τ)
    (g, γftv, τftv)
                 ← coalesceSCCs (g, γftv, τftv)
    trace ("gen (scc)", reconstruct g, γftv, τftv, τ)
    g            ← return (untransitive g)
    trace ("gen (untrans)", reconstruct g, γftv, τftv, τ)
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
      -- of type variables, and returns when all of the constraint is
      -- reduced to pairs of atoms.
      atomize []           done = return done
      atomize ((τ, τ'):c') done = do
        ec ← τ ~≤~ τ'
        case ec of
          Left (SC c'', αs) →
            let hasChanged (VarAt β, _) | β `elem` αs = True
                hasChanged (_, VarAt β) | β `elem` αs = True
                hasChanged _                          = False
                (changed, done')  = List.partition hasChanged done
                liftTy            = map (first atomTy . second atomTy)
             in atomize (c'' ++ liftTy changed ++ c') done'
          Right (α, β)      → atomize c' ((α, β):done)
      --
      -- Given a list of pairs, build the graph
      buildGraph pairs =
        snd . NM.run (Gr.empty ∷ Gr (Atom r) ()) $ do
          NM.insMapNodesM (map fst pairs)
          NM.insMapNodesM (map snd pairs)
          NM.insMapEdgesM [ (α, α', ()) | (α, α') ← pairs, α /= α' ]
          return ()
      --
      -- Make sure the graph is satisfiable
      checkSatisfiable g =
        sequence_
          [ fail $ "Unification error: " ++ c1 ++ " /≤ " ++ c2
          | (n1, n2) ← Gr.edges (TransClos.trc g)
          , Just (ConAt c1) ← return (Gr.lab g n1)
          , Just (ConAt c2) ← return (Gr.lab g n2)
          , not (c1 `tyConLe` c2) ]
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
                    , n2 ← Gr.suc g node, n2 /= node, n2 /= n1 ]
                    (Gr.delNode node g)
        where node = nmLab nm (VarAt α)
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
          tryRemove (changed, state@(g,γftv,τftv)) (lnode@(n,_), var) =
            case (Gr.gelem n g, var, Gr.pre g n, Gr.suc g n) of
              (True, Covariant, [], _) →
                  return (True, (Gr.delNode n g, γftv, τftv))
              (True, Contravariant, _, []) →
                  return (True, (Gr.delNode n g, γftv, τftv))
              (True, Covariant, [pred], _) → do
                  (_, state') ← coalesce lnode (labelNode g pred) state
                  return (True, state')
              (True, Contravariant, _, [succ]) → do
                  (_, state') ← coalesce lnode (labelNode g succ) state
                  return (True, state')
              _ → return (changed, state)
          findSingles = Map.foldWithKey keep []
          keep α [1]  = ((NM.mkNode_ nm (VarAt α), Covariant):)
          keep α [-1] = ((NM.mkNode_ nm (VarAt α), Contravariant):)
          keep _ _    = id
      --
      -- Coalesce the strongly-connected components to single atoms
      coalesceSCCs state =
        foldM (liftM snd <$$> coalesceList) state (labScc (prj1 state))
      -- Given a list of atoms, coalesce them to one atom
      coalesceList state0 (ln:lns) =
        foldM (\(ln1, state) ln2 → coalesce ln1 ln2 state) (ln, state0) lns
      coalesceList _      [] = fail "BUG! coalesceList got []"
      -- Assign n2 to n1, updating the graph, type variables, and ftvs,
      -- and return whichever node survives
      coalesce (n1, lab1) (n2, lab2) (g, γftv, τftv) = do
        case (lab1, lab2) of
          (VarAt α, _)       → (n1, α) `gets` (n2, lab2)
          (_      , VarAt α) → (n2, α) `gets` (n1, lab1)
          _ → return ((n2, lab2), (assignNode n1 n2 g, γftv, τftv))
        where
          (n1', α) `gets` (n2', lab') = do
            (γftv', τftv') ← assignTV α lab' (γftv, τftv)
            return ((n2', lab'), (assignNode n1' n2' g, γftv', τftv'))
      -- Update the graph to remove node n1, assigning all of its
      -- neighbors to n2
      assignNode n1 n2 g =
        Gr.insEdges [ (n', n2, ())
                    | n' ← Gr.pre g n1, n' /= n1, n' /= n2 ] $
        Gr.insEdges [ (n2, n', ())
                    | n' ← Gr.suc g n1, n' /= n1, n' /= n2 ] $
        Gr.delNode n1 g
      -- Update the type variables to assign atom2 to α1, updating the
      -- ftvs appropriately
      assignTV α atom (γftv, τftv) = do
        writeTV α (atomTy atom)
        return (assignFtvSet α atom γftv, assignFtvMap α atom τftv)
      -- Given two type variables, where α ← atom, update a set of free
      -- type variables accordingly
      assignFtvSet α atom set =
        if Set.member α set
          then case atom of
            VarAt β → Set.insert β (Set.delete α set)
            ConAt _ → Set.delete α set
          else set
      -- Given two type variables, where α ← atom, update a map of free
      -- type variables to variance lists accordingly
      assignFtvMap α atom vmap =
        case Map.lookup α vmap of
          Just vs → case atom of
            VarAt β → Map.insertWith (++) β vs (Map.delete α vmap)
            ConAt _ → Map.delete α vmap
          Nothing → vmap
      -- Coalesce and remove fully-generalizable components
      coalesceComponents value (g, γftv, τftv) =
        let candidates = Set.mapMonotonic VarAt (genCandidates value τftv γftv)
            each state component@(_:_)
              | all (`Set.member` candidates) (map snd component)
              = do
                  ((node, _), (g', γftv', τftv'))
                    ← coalesceList state component
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
        return (atomTy α1, atomTy α2)
      -- Generalize the type, leaving out any type variables remaining
      -- in the constraint
      generalizeNow value c γftv τftv τ = do
        cftv     ← ftvSet c
        let αs   = genCandidates value τftv (γftv `Set.union` cftv)
        closeWith AllQu (Set.toList αs) <$> derefAll τ

{-
g ∷ Gr Int ()
g = Gr.insEdges [ (n,n+1,()) | n ← [1..9] ] $
    Gr.insNodes [ (n,n) | n ← [1..10] ] $
    Gr.empty
-}

-- | Compute the transitive reduction of a graph.
untransitive ∷ Gr.DynGraph gr ⇒ gr a b → gr a b
untransitive g =
  let gPlus     = TransClos.trc g
      redundant = [ (n1, n2)
                  | (n1, n2) ← Gr.edges g
                  , n'       ← Gr.suc g n1
                  , n' /= n2
                  , n2 `elem` Gr.suc gPlus n' ]
   in Gr.delEdges redundant g

-- | Look up the node index of a node label
nmLab ∷ Ord a ⇒ NM.NodeMap a → a → Gr.Node
nmLab = fst <$$> NM.mkNode_

labelNode ∷ Gr.Graph gr ⇒ gr a b → Gr.Node → Gr.LNode a
labelNode g n = case Gr.lab g n of
  Just ln → (n, ln)
  Nothing → error "labelNode: node not found"

labScc ∷ Gr.Graph gr ⇒ gr a b → [[Gr.LNode a]]
labScc g = map preorder (rdffWith Gr.labNode' (DFS.topsort g) g)
  where
  rdffWith :: Gr.Graph gr ⇒ DFS.CFun a b c → [Gr.Node] → gr a b → [Tree.Tree c]
  rdffWith = DFS.xdffWith Gr.pre'

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

{-
check "let rec f = \\(C x).f (C (f x)) in f"

diverges like this:

[(1,C 2),(0,2 → 3),(0,C 3 → 4),(1 → 4,0),(0,1 → 4)],0)
[(C 5,C 2),(0,2 → 3),(0,C 3 → 4),(C 5 → 4,0),(0,C 5 → 4)],0)
[(5,2),(0,2 → 3),(0,C 3 → 4),(C 5 → 4,0),(0,C 5 → 4)],0)
[(5,2),(6 → 7,2 → 3),(6 → 7,C 3 → 4),(C 5 → 4,6 → 7),(6 → 7,C 5 → 4)],6 → 7)
[(5,2),(2,6),(7,3),(6 → 7,C 3 → 4),(C 5 → 4,6 → 7),(6 → 7,C 5 → 4)],6 → 7)
[(5,2),(2,6),(7,3),(C 3,6),(7,4),(C 5 → 4,6 → 7),(6 → 7,C 5 → 4)],6 → 7)
[(5,2),(2,C 8),(7,3),(C 3,C 8),(7,4),(C 5 → 4,C 8 → 7),(C 8 → 7,C 5 → 4)],C 8 → 7)
[(5,2),(2,C 8),(7,3),(3,8),(7,4),(C 8,C 5),(4,7),(C 8 → 7,C 5 → 4)],C 8 → 7)
[(5,C 9),(C 9,C 8),(7,3),(3,8),(7,4),(8,5),(4,7),(C 8 → 7,C 5 → 4)],C 8 → 7)
[(5,C 9),(9,8),(7,3),(3,8),(7,4),(8,5),(4,7),(C 8 → 7,C 5 → 4)],C 8 → 7)
[(5,C 9),(9,8),(7,3),(3,8),(7,4),(8,5),(4,7),(C5,C 8),(7,4)],C 8 → 7)
[(5,C 9),(9,8),(7,3),(3,8),(7,4),(8,5),(4,7),(5,8),(7,4)],C 8 → 7)

NEED BETTER OCCURS CHECK


[(1, C 2), (C 1, 2)]
[(C 3, C 2), (C C 3, 2)]
[(3, 2), (C C 3, 2)]
[(3, C 4), (C C 3, C 4)]
[(3, C 4), (C 3, 4)]

[(1, C 2), (2, C 1)]
[(C 3, C 2), (2, C C 3)]
[(3, 2), (2, C C 3)]
[(3, C 4), (C 4, C C 3)]
[(3, C 4), (4, C 3)]


α = C × α
α = C × (C × (C × ...))

α ≤ C × α
α = C × (C × (C × ...))
α = C × (B × (B × ...))
α = C × (B × (A × ...))
α = τ₁ × (τ₂ × (τ₃ × ... (τᵢ × ...) ...))
    where i ≥ j ⇒ τⱼ ≤ τⱼ

OPTIMIZATIONS FROM SIMONET 2003

6.1 Collapsing Cycles

  This is the SCC phase

6.2 Polarities (NOT IMPLEMENTED)

  Upper bounds on positive variables and lower bounds on negative
  variables are irrelevant, e.g.:

    f : ∀ α ≤ A. 1 → α × α
    f : ∀ α. 1 → α × α

  Or:

    let rec f = λx. f (f x) in f
    f : α → β [β ≤ α]
    f : ∀α. ∀β ≤ α. α → β
    f : ∀α. ∀β. α → β

6.3 Reducing Chains

  A positive variable with a single predecessor can be fused with the
  predecessor; dually, a negative variable can be fused with a single
  successor.

    ∀ α ≤ A. α → 1
    A → 1

    ∀ α ≤ A. α × α → 1
    A × A → 1

  Currently this is implemented only for variables that occur only once.
  Why?

6.4 Polarized Garbage Collection

  ?

6.5 Minimization

  If two positive variables have all the same predecessors, the can be
  coalesced. Dually for negative variables with the same successors.

  ∀ α ≤ C. ∀ β ≤ C. α × β → 1
    A × B → 1

  ∀ α ≤ C. α × α → 1
    C × C → 1
    A × B → 1
-}
