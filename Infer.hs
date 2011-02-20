{-#
  LANGUAGE
    EmptyDataDecls,
    ExistentialQuantification,
    FlexibleContexts,
    FlexibleInstances,
    FunctionalDependencies,
    GeneralizedNewtypeDeriving,
    ImplicitParams,
    KindSignatures,
    MultiParamTypeClasses,
    ParallelListComp,
    RankNTypes,
    ScopedTypeVariables,
    TupleSections,
    UnicodeSyntax
  #-}
{- |
  This is based on Daan Leijen's HMF prototypes, and includes the
  following of his features:

   - Full HMF (n-ary applications)

   - Type annotations are treated as rigid

   - Type propagation:

      - Annotations are propagated from outside lambdas onto the
        argument and result.

      - In an application, the types of the formal parameters of the
        operator are propagated to the actual parameters.

  It's been changed/extended in the following ways:

   - The value restriction: applications are not generalized

   - Free type variables in annotations are considered to be bound
     by the "some" quantifier

   - Scoped type variables: some-bound type variables from a lambda
     or annotation are in scope in the body.  (This means that
     (e : σ) is different from (\x:σ.x) e, because scoped type variables
     bound by σ are in scope for e in the former but not the latter.)
     Note that because there is no explicit quantifier for scoped type
     variables, they do not allow shadowing.

   - Binder patterns with type annotations for λ and let

   - Annotation propagation for let patterns:

        let x : π = e1 in e2
          ⇒
        let x : π = (e1 : π) in e2

   - Let rec.

   - Existentials with automatic unpack/pack.

   -- Turned off:
   - Deep subsumption (instantiates under type constructors using the
     correct variance).  This uses Cardelli's "greedy type inference"
     for subtyping, whereby solving the subsumption α <: σ or σ <: α
     sets α = τ.
-}
module Infer (
  TV, TypeR,
  MonadU(..),
  -- Constraint(..),
  -- infer0, infer,

  -- * Debugging
  unsafeReadTV, trace,
) where

import Control.Applicative
import Control.Arrow
import Control.Monad
import Control.Monad.ST
import Control.Monad.Error  as CME
import Control.Monad.State  as CMS
import Control.Monad.Writer as CMW
-- import Control.Monad.RWS    as RWS
import qualified Data.List  as List
import qualified Data.Map   as Map
import qualified Data.Set   as Set
import qualified Data.Tree  as Tree
import Data.STRef
import Data.IORef
import qualified Text.PrettyPrint as Ppr
-- import qualified Test.HUnit as T

-- From fgs:
import Data.Graph.Inductive.PatriciaTree (Gr)
import Data.Graph.Inductive.Basic        (preorder)
import qualified Data.Graph.Inductive.Graph     as Gr
import qualified Data.Graph.Inductive.NodeMap   as NM
import qualified Data.Graph.Inductive.Query.DFS as DFS

import MonadRef
import Ppr
import Syntax hiding (tests)
import Util

---
--- Representation of free type variables
---

-- | A free type variable is represented by a unique 'Int' (its
--   identity) and mutable reference of type @r@, which must be
--   an instance of 'UnsafeReadRef' to facilitate debugging.
data TV r
  = UnsafeReadRef r ⇒ TV {
      tvId     ∷ !Int,
      tvRef    ∷ !(r (Maybe (TypeR r)))
    }

-- | For type inference, we use types with free type variables
--   represented by a 'TV', where the parameter gives the represention
--   of the underlying mutable reference type.
type TypeR r = Type (TV r)

instance Eq (TV s) where
  TV { tvId = i1 } == TV { tvId = i2 } = i1 == i2

instance Ord (TV s) where
  TV { tvId = i1 } `compare` TV { tvId = i2 } = i1 `compare` i2

instance Ppr (TV s) where
  ppr = Ppr.text . show

instance Show (TV s) where
  showsPrec _ tv = showChar '#' . shows (tvId tv)
      . if debug -- && tvFlavor tv == Universal
          then case unsafeReadTV tv of
                 Nothing → id
                 Just t  → showChar '[' . shows t . showChar ']'
          else id

instance Ftv (TV s) (TV s) where
  ftvTree = ftvTree . fvTy

---
--- A unification monad
---

{-
class (Functor m, Applicative m, Monad m, Ord (TV s), Ppr (TV s)) ⇒
      MonadU s m | m → s where
  writeTV  ∷ TV s → Type (TV s) → m ()
  readTV   ∷ TV s → m (Maybe (Type (TV s)))
  newTV    ∷ m (TV s)
  newTVTy  ∷ m (Type (TV s))
  ftv      ∷ Ftv a (TV s) ⇒ a → m [TV s]
  -- Unsafe operations:
  unsafePerformU ∷ m a → a
  unsafeIOToU    ∷ IO a → m a
  --
  newTVTy  = liftM fvTy newTV
  ftv      = ftvM where ?deref = readTV
  -}

class (Functor m, Applicative m, Monad m, Ord tv, Ppr tv) ⇒
      MonadU tv m | m → tv where
  writeTV  ∷ tv → Type tv → m ()
  readTV   ∷ tv → m (Maybe (Type tv))
  newTV    ∷ m tv
  newTVTy  ∷ m (Type tv)
  ftv      ∷ Ftv a tv ⇒ a → m [tv]
  -- Unsafe operations:
  unsafePerformU ∷ m a → a
  unsafeIOToU    ∷ IO a → m a
  --
  newTVTy  = liftM fvTy newTV
  ftv      = ftvM where ?deref = readTV

-- | Fully dereference a sequence of TV indirections
deref ∷ MonadU r m ⇒ Type r → m (Type r)
deref t0@(VarTy (FreeVar tv)) = do
  mt ← readTV tv
  case mt of
    Nothing → return t0
    Just t1 → deref t1
deref t0 = return t0

-- | Fully dereference a type
derefAll ∷ MonadU r m ⇒ Type r → m (Type r)
derefAll = foldType QuaTy bvTy fvTy ConTy where ?deref = readTV

{-
---
--- Implementations of MonadU
---

newtype UT (s ∷ * → *) m a = UT { unUT ∷ StateT Int m a }
  deriving (Functor, Monad)

type UIO a = UT IORef IO a
type UST s a = UT (STRef s) (ST s) a

instance Monad m ⇒ Applicative (UT s m) where
  pure  = return
  (<*>) = ap

instance MonadTrans (UT s) where
  lift = UT . lift

instance MonadRef s m ⇒ MonadU s (UT s m) where
  writeTV TV { tvId = i, tvRef = r } t = do
    old ← lift (readRef r)
    trace ("write", i, t)
    case old of
      Just _  → fail "BUG: Attempted to write TV more than once"
      Nothing → lift (writeRef r (Just t))
  --
  newTV = do
    i ← UT get
    r ← lift $ newRef Nothing
    trace ("new", i)
    UT $ put (i + 1)
    return (TV i r)
  --
  readTV TV { tvRef = r } = UT (readRef r)
  --
  unsafePerformU = unsafePerformRef . unUT
  unsafeIOToU    = lift . unsafeIOToRef

instance Defaultable Int where getDefault = 0

runUT ∷ Monad m ⇒ UT s m a → m a
runUT m = evalStateT (unUT m) 0

type U a = ∀ s m. MonadRef s m ⇒ UT s m a

runU ∷ U a → Either String a
runU m = runST (runErrorT (runUT m))
-}

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
--   types are type variables.  If unification happens, return the
--   generated constraint and a list of affected (substituted) type
--   variables.  Otherwise, if given a comparison on two different
--   type variables, we return them as a pair.
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
--- Abstract inference
---

type Γ r = [[Type r]]
type Δ r = Map.Map Name (Type r)

{-
check ∷ String → IO (Type String)
check = showInfer . read

showInfer ∷ Term Empty → IO (Type String)
showInfer e = runUT $ do
  τ ← infer0 [map (fmap elimEmpty) γ0] e
  stringifyType τ

stringifyType ∷ MonadU s m ⇒ TypeR s → m (Type String)
stringifyType = typeMapM each where
  each r = do
    mt ← readTV r
    case mt of
      Nothing → return (fvTy (show r))
      Just t  → stringifyType t

r t = fmap elimEmpty (read t :: Type Empty)

infer0 ∷ forall m r. (MonadU r m) ⇒
         Γ r → Term Empty → m (TypeR r)
infer0 γ e = do
  (τ, c)  ← infer mempty γ e
  (τ', _) ← gen (syntacticValue e) (c ∷ SubtypeConstraint r) γ τ
  return τ'
  -}

-- | To infer a type and constraint for a term
infer ∷ (MonadU r m, Constraint c r) ⇒
        Δ r → Γ r → Term Empty → m (Type r, c)
infer δ γ e0 = case e0 of
  VarTm (FreeVar ff)            → elimEmpty ff
  VarTm (BoundVar i j _)        → do
    τ ← inst (γ !! i !! j)
    return (τ, (⊤))
  AbsTm (VarPa _) e             → do
    α      ← newTVTy
    (τ, c) ← infer δ ([α]:γ) e
    return (α ↦ τ, c)
  AppTm e1 e2                   → do
    (τ1, c1) ← infer δ γ e1
    (τ2, c2) ← infer δ γ e2
    α        ← newTVTy
    return (α, c1 ⋀ c2 ⋀ τ1 ≤ τ2 ↦ α)
  LetTm False (VarPa _) e1 e2   → do
    (τ1, c1) ← infer δ γ e1
    (σ, c1') ← gen (syntacticValue e1) c1 γ τ1
    (τ2, c2) ← infer δ ([σ]:γ) e2
    return (τ2, c1' ⋀ c2)
  _ → fail $ "Not handled: " ++ show e0

-- | Instantiate a prenex quantifier
inst ∷ MonadU r m ⇒ Type r → m (Type r)
inst σ0 = do
  σ ← deref σ0
  case σ of
    QuaTy AllQu ns τ → do
      αs ← replicateM (length ns) newTVTy
      return (openTy 0 αs τ)
    τ → return τ

---
--- An implementation of constraints
---

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

instance (Show r, Tv r) ⇒ Constraint (SubtypeConstraint r) r where
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

nmLab ∷ Ord a ⇒ NM.NodeMap a → a → Gr.Node
nmLab = fst <$$> NM.mkNode_

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
---
--- Implementation of simple generalization
---

{-

-- | Given a type, strip off the outermost quantifier and make the bound
--   tyvars (un-)unifiable.  Assumes that the given type is already
--   deferenced
openQua ∷ MonadU s m ⇒ Bool → Bool → TypeR s → m (TypeR s, [TV s])
openQua upos epos t = do
  (t', tvs) ← openAll upos t
  t''       ← openEx epos t'
  return (t'', tvs)

openAll ∷ MonadU s m ⇒ Bool → TypeR s → m (TypeR s, [TV s])
openAll pos (QuaTy AllQu n t) = do
  trace ("openAll", pos, n, t)
  tvs ← replicateM n (newTV (determineFlavor Universal pos))
  return (openTy 0 (map fvTy tvs) t, if pos then [] else tvs)
openAll _ t = return (t, [])

openEx ∷ MonadU s m ⇒ Bool → TypeR s → m (TypeR s)
openEx pos (QuaTy ExQu n t) = do
  trace ("openEx", pos, n, t)
  tvs ← replicateM n (newTV (determineFlavor Existential pos))
  return (openTy 0 (map fvTy tvs) t)
openEx _ t = return t

instantiate    ∷ MonadU s m ⇒ TypeR s → m (TypeR s)
instantiate    = deref >=> openQua True True >=> return . fst

instantiateNeg ∷ MonadU s m ⇒ TypeR s → m (TypeR s, [TV s])
instantiateNeg = deref >=> openQua False False

-- | Instantiate only the universal quantifiers up front
instantiateUni ∷ MonadU s m ⇒ TypeR s → m (TypeR s)
instantiateUni σ0 = do
  σ ← deref σ0
  case σ of
    QuaTy AllQu n ρ → do
      tvs ← replicateM n (newTV Universal)
      return (openTy 0 (map fvTy tvs) ρ)
    _ → return σ

---
--- Unification
---

-- | Assumption: tv1 is unifiable and empty
unifyVar ∷ MonadU s m ⇒ TV s → TypeR s → m ()
unifyVar tv1 t2 = do
  trace ("unifyVar", tv1, t2)
  when (not (lcTy t2)) $
    fail "Could not unify: not locally closed (BUG?)"
  tvs ← ftvFlavor Universal t2
  when (tv1 `elem` tvs) $
    fail "Could not unify: occurs check failed"
  writeTV tv1 t2

(=:) ∷ MonadU s m ⇒ TypeR s → TypeR s → m ()
(=:) = unify

unify ∷ MonadU s m ⇒ TypeR s → TypeR s → m ()
unify t10 t20 = do
  trace ("unify {", t10, t20)
  t1 ← deref t10
  t2 ← deref t20
  case (t1, t2) of
    (VarTy v1, VarTy v2)
      | v1 == v2 → return ()
    (ConTy c1 ts1, ConTy c2 ts2)
      | c1 == c2 → zipWithM_ unify ts1 ts2
    (QuaTy q1 n1 t1, QuaTy q2 n2 t2)
      | q1 == q2 && n1 == n2 → do
      tvs ← replicateM n1 (newTV Skolem)
      let open = openTy 0 (map fvTy tvs)
      unify (open t1) (open t2)
      ftvs1 ← ftvFlavor Skolem t1
      ftvs2 ← ftvFlavor Skolem t2
      when (any (`elem` tvs) (ftvs1 ++ ftvs2)) $
        fail "Could not unify: insufficiently polymorphic"
    (VarTy (FreeVar tv1@TV { tvFlavor = Universal }), _)
      → unifyVar tv1 t2
    (_, VarTy (FreeVar tv2@TV { tvFlavor = Universal }))
      → unifyVar tv2 t1
    (_, _)
      → fail $ "Could not unify ‘" ++ show t1 ++ "’ with ‘" ++ show t2 ++ "’"
  trace ("} yfinu", t10, t20)

{-
  ∀α. α → α    ⊔    Int → Int      =       Int → Int
  ∀α. α → Int  ⊔    Int → Int      =       Int → Int
  ∀α. α → α    ⊔    ∀α. Int → α    =       Int → Int
  ∀α. α → Int  ⊔    ∀α. Int → α    =       Int → Int
  ∀α. α → Int  ⊔    ∀α. Bool → α   =       Bool → Int
  ∀αβ. α → β   ⊔    ∀α. α → α      =       ∀α. α → α
  ∀α. α → Int  ⊔    Int → Bool     =       Int → ⊤
  ∀α. Int → α  ⊔    Bool → Int     =       ⊥ → Int

  (∀α. α → α) → 1    ⊔  (Int → Int) → 1     = (∀α. α → α) → 1
* (∀α. α → α) → 1    ⊔  (∀α. α → Int) → 1   = (∀αβ. α → β) → 1
  (∀α. α → Int) → 1  ⊔  (Int → Int) → 1     = (∀α. α → Int) → 1

  ∀α. α → α → 1      ⊔  Int → Bool → 1      = Int → ⊥    → 1
                                            = ⊥   → Bool → 1
                                            = ⊥   → ⊥    → 1

  ∀α. α → α → 1      ⊔  Int → ∀β. β → 1     = Int → Int → 1

  only instantiate up front?

-}

{-
unifyDir ∷ Variance → TypeR s → TypeR s → U s (TypeR s)
unifyDir Invariant σ1 σ2   = σ1 <$ unify σ1 σ2
unifyDir Omnivariant σ1 σ2 = return σ1 -- XXX arbitrary?
unifyDir dir σ10 σ20 = do
  trace ("unifyDir {", dir, σ10, σ20)
  σ1 ← deref σ10
  σ2 ← deref σ20
  σ ← case (σ1, σ2) of
    (VarTy v1, VarTy v2)
      | v1 == v2 → return σ1
    (ConTy c1 σs1, ConTy c2 σs2)
      | c1 == c2 && length σs1 == length σs2 →
      ConTy c1 <$>
        sequence [ unifyDir (dir * dir') σ1 σ2
                 | dir' ← getVariances c1 (length σs1)
                 | σ1   ← σs1
                 | σ2   ← σs2 ]
                 {-
    (VarTy (FreeVar tv@TV { tvFlavor = Universal }), _) → do
    -}
  trace ("} riDyfinu", dir, σ10, σ20)
  return σ
-}

(<:) ∷ MonadU s m ⇒ TypeR s → TypeR s → m ()
σ1 <: σ2 = subsume σ2 σ1

-- | Is t1 subsumed by t2?
subsume ∷ MonadU s m ⇒ TypeR s → TypeR s → m ()
subsume σ1 σ2 = do
  trace ("subsume {", σ1, σ2)
  σ1' ← deref σ1
  case σ1' of
    VarTy (FreeVar tv@TV { tvFlavor = Universal }) → do
      σ2' ← instantiateUni σ2
      unifyVar tv σ2'
    _ → do
      (ρ1, tvs1) ← instantiateNeg σ1'
      ρ2 ← instantiate σ2
      unify ρ1 ρ2
      ftvs1 ← ftvFlavor Skolem σ1
      ftvs2 ← ftvFlavor Skolem σ2
      when (any (`elem` tvs1) (ftvs1 ++ ftvs2)) $ do
        trace (tvs1, ftvs1, ftvs2)
        fail "Could not subsume: insufficiently polymorphic"
  trace ("} emusbus", σ1, σ2)

{-
deepSubsume ∷ TypeR s → TypeR s → U s ()
deepSubsume σ10 σ20 = do
  trace ("subsume {", σ10, σ20)
  σ1 ← deref σ10
  σ2 ← deref σ20
  case (σ1, σ2) of
    (VarTy v1, VarTy v2)
      | v1 == v2 → return ()
    (ConTy c1 σs1, ConTy c2 σs2)
      | c1 == c2 && length σs1 == length σs2 →
      sequence_ [ σ1 `rel` σ2
                | rel ← getRels c1 (length σs1)
                | σ1  ← σs1
                | σ2  ← σs2 ]
    (VarTy (FreeVar tv1@TV {tvFlavor = Universal}), _) →
      unifyVar tv1 σ2
    (_, VarTy (FreeVar tv2@TV {tvFlavor = Universal})) →
      unifyVar tv2 σ1
    (QuaTy _ _ _, _) → do
      (ρ1, tvs1) ← instantiateNeg σ1
      deepSubsume ρ1 σ2
      ftvs1 ← ftvS σ1
      ftvs2 ← ftvS σ2
      when (any (`elem` tvs1) (ftvs1 ++ ftvs2)) $ do
        trace (tvs1, ftvs1, ftvs2)
        fail "Could not subsume: insufficiently polymorphic"
    (_, QuaTy _ _ _) → do
      ρ2 ← instantiate σ2
      deepSubsume σ1 ρ2
    (_, _)
      → fail $ "Could not subsume: ‘" ++
          show σ1 ++ "’ ≥ ‘" ++ show σ2 ++ "’"
  trace ("} emusbus", σ1, σ2)

getRels ∷ Name → Int → [TypeR s → TypeR s → U s ()]
getRels c i = map toRel (getVariances c i) where
  toRel Omnivariant   = \_ _ -> return ()
  toRel Covariant     = deepSubsume
  toRel Contravariant = flip deepSubsume
  toRel Invariant     = unify
-}

-- | Given a list of type/U-action pairs, run all the U actions, but
--   in an order that does all U-actions not assocated with tyvars
--   before those associated with tyvars. Checks dynamically after each
--   action, since an action can turn a tyvar into a non-tyvar.
subsumeN ∷ MonadU s m ⇒ [(TypeR s, m ())] → m ()
subsumeN [] = return ()
subsumeN σs = subsumeOneOf σs >>= subsumeN
  where
    subsumeOneOf []             = return []
    subsumeOneOf [(_, u1)]      = [] <$ u1
    subsumeOneOf ((σ1, u1):σs)  = do
      σ ← deref σ1
      case σ of
        VarTy (FreeVar TV { tvFlavor = Universal })
          → ((σ, u1):) <$> subsumeOneOf σs
        _ → σs <$ u1

-- | Given a function arity and a type, extracts a list of argument
--   types and a result type of at most the given arity.
funmatchN ∷ MonadU s m ⇒ Int → TypeR s → m ([TypeR s], TypeR s)
funmatchN n0 σ0 = do
  σ0' ← deref σ0
  case σ0' of
    ConTy "->" [_, _] → unroll n0 σ0'
    VarTy (FreeVar α@TV {tvFlavor = Universal}) → do
      β1 ← newTVTy Universal
      β2 ← newTVTy Universal
      writeTV α (β1 ↦ β2)
      return ([β1], β2)
    _ → fail ("Expected function type, but got ‘" ++ show σ0' ++ "’")
  where
    unroll (n + 1) (ConTy "->" [σ1, σ']) = do
      (σ2m, σ) ← unroll n =<< deref σ'
      return (σ1:σ2m, σ)
    unroll _ σ                           = return ([], σ)

type Γ s = [[TypeR s]]
type Δ s = Map.Map Name (TypeR s)

infer ∷ MonadU s m ⇒ Δ s → Γ s → Term Empty → Maybe (TypeR s) → m (TypeR s)
infer δ γ e0 mσ = do
  trace ("infer {", δ, init γ, e0, mσ)
  σ ← case e0 of
    VarTm (FreeVar e) → elimEmpty e
    VarTm (BoundVar i j _) → return (γ !! i !! j)
    LetTm False π e1 e2 → do
      let e1' = maybe e1 (AnnTm e1) (extractPattAnnot π)
      σ1 ← infer δ γ e1' Nothing
      (δ', _, σs, _) ← instPatt δ π (Just σ1)
      infer δ' (σs:γ) e2 mσ
    LetTm True π e1 e2 → do
      unless (syntacticValue e1) $
        fail "bound expr in let rec not a syntactic value"
      (δ', σ0, σs, _) ← instPatt δ π Nothing
      σ   ← infer δ' (σs:γ) e1 (Just σ0)
      σ <: σ0
      σs' ← mapM (generalize γ [Universal]) σs -- XXX Existential too?
      infer δ' (σs':γ) e2 mσ
    AbsTm π e → do
      [mσ1, mσ2]      ← splitCon mσ "->" 2
      (δ', σ, σs, αs) ← instPatt δ π mσ1
      σ'              ← inferInst δ' (σs:γ) e mσ2
      unlessM (allM isTauU αs) $
        fail "used some unannotated parameter polymorphically"
      generalize γ [Universal, Existential] (σ ↦ σ')
    ConTm name es → do
      mσs ← splitCon mσ name (length es)
      ρs  ← zipWithM (inferInst δ γ) es mσs
      let ρ    = ConTy name ρs
          gens = if syntacticValue e0
                   then [Universal, Existential]
                   else [Existential]
      generalize γ gens ρ
    AppTm _ _ → do
      let (e, es) = unfoldApp e0
      σ1 ← infer δ γ e Nothing
      σ  ← inferApp δ γ σ1 es
      generalize γ [Existential] σ
    AnnTm e annot → do
      (δ', σ, _) ← instAnnot δ annot
      σ'         ← infer δ' γ e (Just σ)
      σ' <: σ
      return σ
  trace ("} refni", δ, init γ, e0, σ)
  return σ

-- | Given (maybe) a type, a type constructor name, and its arity,
--   return a list of (maybe) parameter types.
{-
Instantiates both ∀ and ∃ to univars:
  (λx.x) : A → A          ⇒       (λ(x:A). (x:A)) : A → A
  (λx.x) : ∀α. α → α      ⇒       (λ(x:β). (x:β)) : ∀α. α → α
  (λx.x) : ∀α. C α → C α  ⇒       (λ(x:C β). (x:C β)) : ∀α. C α → C α
  (λx.x) : ∃α. α → α      ⇒       (λ(x:β). (x:β)) : ∃α. α → α
  (λx.x) : ∃α. C α → C α  ⇒       (λ(x:C β). (x:C β)) : ∃α. C α → C α
-}
splitCon ∷ MonadU s m ⇒ Maybe (TypeR s) → Name → Int → m [Maybe (TypeR s)]
splitCon Nothing  _ arity = return (replicate arity Nothing)
splitCon (Just σ) c arity = do
  trace ("splitCon", σ, c, arity)
  (ρ, _) ← openQua True False σ
  return $ case ρ of
    ConTy c' σs | c == c' && length σs == arity
      → map Just σs
    _ → replicate arity Nothing

-- infer; instantiate if not rigid
inferInst ∷ MonadU s m ⇒
            Δ s → Γ s → Term Empty → Maybe (TypeR s) → m (TypeR s)
inferInst δ γ e mσ = do
  σ ← infer δ γ e mσ
  keepPoly ← maybe (return False) isSigmaU mσ
  if isAnnotated e || keepPoly
    then return σ
    else instantiate σ >>= generalize γ [Existential]

inferApp ∷ MonadU s m ⇒ Δ s → Γ s → TypeR s → [Term Empty] → m (TypeR s)
inferApp δ γ σ0 e1n = do
  ρ        ← instantiate σ0
  (σ1m, σ) ← funmatchN (length e1n) ρ
  σ1m'     ← sequence
                [ do
                    -- last arg to infer (Just σi) is for
                    -- formal-to-actual propagation
                    σi' ← infer δ γ ei (Just σi)
                    return (σi, if isAnnotated ei
                                  then σi' =: σi
                                  else σi' <: σi)
                | σi ← σ1m
                | ei ← e1n ]
  subsumeN σ1m'
  if length σ1m < length e1n
    then inferApp δ γ σ (drop (length σ1m) e1n)
    else return σ

-- | Given a type variable environment, a pattern, and maybe a
--   type annotation, compute an updated type variable environment,
--   a type for the whole pattern, a type for each variable bound by
--   the pattern, and a list of type variables that should stay as
--   monotypes.
--
-- Postcondition:
--   If
--     (δ', σ, σs, αs) ← instPatt δ π (Just σ0)
--   then
--     σ0 <: σ
instPatt ∷ MonadU s m ⇒
           Δ s → Patt Empty → Maybe (TypeR s) ->
           m (Δ s, TypeR s, [TypeR s], [TypeR s])
instPatt δ0 π0 mσ0 = do
  trace ("instPatt {", δ0, π0, mσ0)
  ((σ, σs), δ, αs) ← runRWST (loop π0 mσ0) () δ0
  αs' ← filterM isTauU αs
  trace ("} ttaPtsni", δ, σ, σs, αs')
  return (δ, σ, σs, αs')
  where
  loop π mσ = case π of
    VarPa          → do
      σ ← instM mσ
      return (σ, [σ])
    WldPa          → do
      σ ← instM mσ
      return (σ, [])
    ConPa c πs     → do
      σ ← instM mσ
      αs ← lift $ replicateM (length πs) (newTVTy Universal)
      tell αs
      lift $ σ <: ConTy c αs
      (_, σss) ← unzip <$> zipWithM loop πs (Just <$> αs)
      return (σ, concat σss)
    AnnPa π' annot → do
      σi ← instA annot
      σo ← case mσ of
        Nothing → return σi
        Just σo → do lift (σo <: σi); return σo
      (_, σs) ← loop π' (Just σi)
      return (σo, σs)
  -- make a new univar if given nothing
  instM (Just σ) = return σ
  instM Nothing  = do
    α ← lift (newTVTy Universal)
    tell [α]
    return α
  -- instantiate an annotation:
  instA annot = do
    δ ← get
    (δ', σ, αs) ← lift (instAnnot δ annot)
    put δ'
    tell αs
    return σ

-- | Is the pattern annotated everywhere?
fullyAnnotatedPatt ∷ Patt Empty → Bool
fullyAnnotatedPatt VarPa        = False
fullyAnnotatedPatt WldPa        = False
fullyAnnotatedPatt (ConPa _ πs) = all fullyAnnotatedPatt πs
fullyAnnotatedPatt (AnnPa _ _)  = True

-- | If the pattern is fully annotated, extract the annotation.
extractPattAnnot ∷ Monad m ⇒ Patt Empty → m Annot
extractPattAnnot π0 = do
  (σ, ns) ← runStateT (loop π0) []
  return (Annot ns σ)
  where
  loop VarPa                  = fail "Unannotated variable pattern"
  loop WldPa                  = fail "Unannotated wildcard pattern"
  loop (ConPa c πs)           = ConTy c <$> mapM loop πs
  loop (AnnPa _ (Annot ns σ)) = do
    modify (`List.union` ns)
    return σ

-- | Given a tyvar environment (mapping some-bound names to tyvars) and
--   an annotation, create new universal type variables for any new
--   some-bound names in the annotation and update the environment
--   accordingly. Return the annotation instantiated to a type and the
--   list of new universal tyvars.
instAnnot ∷ MonadU s m ⇒
            Δ s → Annot →
            m (Δ s, TypeR s, [TypeR s])
instAnnot δ (Annot names σ0) = do
  αs ← mapM eachName names
  let δ' = foldr2 insert δ names αs
      σ  = totalSubst names αs =<< σ0
  trace ("instAnnot", δ, δ', σ, αs)
  return (δ', σ, αs)
  where
    insert ('_':_) = const id
    insert k       = Map.insert k
    eachName name  = maybe (newTVTy Universal) return (Map.lookup name δ)

-- | Generalize type variables not found in the context. Generalize
--   universal tyvars into universal quantifiers and existential tyvars
--   into existential quantifiers.
generalize ∷ MonadU s m ⇒ Γ s → [Flavor] → TypeR s → m (TypeR s)
generalize γ flavors σ = do
  σ' ← derefAll σ
  let fftv flav | flav `elem` flavors = ftvFlavor flav σ'
                | otherwise           = return []
  uftv ← fftv Universal
  eftv ← fftv Existential
  ftvγ ← ftv γ
  let uαs = filter (`notElem` ftvγ) uftv
      eαs = filter (`notElem` ftvγ) eftv
  return (closeWith AllQu uαs (closeWith ExQu eαs σ'))

-- | Is the given type quantified? (A σ type?)
isSigmaU ∷ MonadU s m ⇒ TypeR s → m Bool
isSigmaU σ0 = do
  σ ← deref σ0
  return $ case σ of
    QuaTy _ _ _ → True
    _           → False

-- | Is the type quantifier-free? (A τ type?)
isTauU ∷ MonadU s m ⇒ TypeR s → m Bool
isTauU = foldType readTV (\_ _ _→ False) (\_ _ _→ True) (\_→ True) (\_→ and)

---
--- Testing and interactive
---

relAnnot ∷ MonadU s m ⇒
           (TypeR s → TypeR s → m a) →
           Annot → Annot → m (TypeR s, TypeR s)
relAnnot rel (Annot ns1 σ1) (Annot ns2 σ2) = do
    αs1 ← replicateM (length ns1) (newTVTy Universal)
    αs2 ← replicateM (length ns2) (newTVTy Universal)
    let σ1'     = totalSubst ns1 αs1 =<< σ1
        σ2'     = totalSubst ns2 αs2 =<< σ2
    rel σ1' σ2'
    return (σ1', σ2')

unifyAnnot ∷ MonadU s m ⇒ Annot → Annot → m (TypeR s, TypeR s)
unifyAnnot = relAnnot unify

showUnifyAnnot ∷ Annot → Annot → Either String String
showUnifyAnnot t1 t2 = runU $ do
  (t1', t2') ← unifyAnnot t1 t2
  t1'' ← derefAll t1'
  t2'' ← derefAll t2'
  return (show t1'' ++ " / " ++ show t2'')

subsumeAnnot ∷ MonadU s m ⇒ Annot → Annot → m (TypeR s, TypeR s)
subsumeAnnot = relAnnot subsume

showSubsumeAnnot ∷ Annot → Annot → Either String String
showSubsumeAnnot t1 t2 = runU $ do
  (t1', t2') ← subsumeAnnot t1 t2
  t1'' ← derefAll t1'
  t2'' ← derefAll t2'
  return (show t1'' ++ " ≥ " ++ show t2'')

showInfer ∷ Term Empty → Either String (Type String)
showInfer e = runU $ do
  τ ← infer Map.empty [map (fmap elimEmpty) γ0] e Nothing
  stringifyType τ

stringifyType ∷ MonadU s m ⇒ TypeR s → m (Type String)
stringifyType = typeMapM each where
  each r = do
    mt ← readTV r
    case mt of
      Nothing → return (fvTy (show r))
      Just t  → stringifyType t

u ∷ String → String → IO ()
u a b = do
  either putStrLn putStrLn $
    showUnifyAnnot (normalizeAnnot (read a)) (normalizeAnnot (read b))

s ∷ String → String → IO ()
s a b = do
  either putStrLn putStrLn $
    showSubsumeAnnot (normalizeAnnot (read a)) (normalizeAnnot (read b))

i ∷ String → IO ()
i a = do
  either putStrLn print $
    showInfer (read a)

tests, inferTests ∷ IO ()

inferTests = tests
tests      = do
  syntaxTests
  T.runTestTT unifyAnnotTests
  T.runTestTT subsumeAnnotTests
  T.runTestTT inferFnTests
  return ()

unifyAnnotTests ∷ T.Test
unifyAnnotTests = T.test
  [ "α"                 <=> "β"
  , "α"                 <=> "C"
  , "α"                 <=> "C → C"
  , "α → α"             <=> "C → C"
  , "α → β"             <=> "C → D"
  , "α → α"             <=> "β → β"
  , "α → α → β"         <=> "α → β → β"
  , "∀ α. α → α"        <=> "∀ α. α → α"
  , "∃ α. α → α"        <=> "∃ α. α → α"
  , "∀ α. α → β"        <=> "∀ α β γ. β → δ"
  , "∃ α. α → β"        <=> "∃ α β γ. β → δ"
  , "C"                 <!> "D"
  , "α → α"             <!> "C → D"
  , "A β γ β γ"         <!> "A B C α α"
  -- insuffiently polymorphic:
  , "∀ α. α → β"        <!> "∀ α. α → α"
  , "∃ α. α → β"        <!> "∃ α. α → α"
  -- doesn't match:
  , "∀ α. α → α"        <!> "∃ α. α → α"
  -- occurs check:
  , "α → A → α"         <!> "β → β"
  ]
  where
  a <=> b = T.assertBool (a ++ " <=> " ++ b)
              (either f t (showUnifyAnnot (nr a) (nr b)))
  a <!> b = T.assertBool (a ++ " <!> " ++ b)
              (either t f (showUnifyAnnot (nr a) (nr b)))
  nr = normalizeAnnot . read
  f = const False
  t = const True

subsumeAnnotTests ∷ T.Test
subsumeAnnotTests = T.test
  [ "α" ≥ "β"
  , "α" ≥ "C"
  , "C" ≥ "α"
  , "C → C" ≥ "∀ α. α → α"
  , "C → C" ≥ "∀ α β. α → β"
  , "C → D" /≥ "∀ α. α → α"
  , "C → D" ≥ "∀ α β. α → β"
  , "∀ α. α → α" ≥ "∀ α. α → α"
  , "∀ α. α → α" ≥ "∀ α β. α → β"
  , "∀ α. α → C" ≥ "∀ α β. α → β"
  , "∀ α. C → α" ≥ "∀ α β. α → β"
  , "∀ α. α → α" /≥ "α → α"
  , "β → γ" ≥ "∀ α. α → α"
  , "(∀ α. C α) → (∀ α. C α)" ≥ "∀ α. α → α"
  , "∀ β. (∀ α. C α β) → (∀ α. C α β)" ≥ "∀ α. α → α"
  , "∀ β γ. (∀ α. C α β) → (∀ α. C α γ)" /≥ "∀ α. α → α"
  , "(∀ α. C α β) → (∀ α. C α γ)" ≥ "∀ α. α → α"
  , "(∀ α. C α β β D) → (∀ α. C α γ D γ)" ≥ "∀ α. α → α"
  , "(∀ α. C α β β D) → (∀ α. C α γ E γ)" /≥ "∀ α. α → α"
  , "∀ β. β" ≤ "∀ α. α → Int"
  , "∀ β. β" /≥ "∀ α. α → Int"
  -- existentials:
  , "C → C" ≤ "∃ α. α → α"
  , "C → C" ≤ "∃ α β. α → β"
  , "C → D" /≤ "∃ α. α → α"
  , "C → D" ≤ "∃ α β. α → β"
  , "∃ α. α → α" ≤ "∃ α. α → α"
  , "∃ α. α → α" ≤ "∃ α β. α → β"
  , "∃ α. α → C" ≤ "∃ α β. α → β"
  , "∃ α. C → α" ≤ "∃ α β. α → β"
  , "∃ α. α → α" ≤ "α → α" -- weird?
  , "∃ α. α → α" /≤ "A → A"
  , "β → γ" ≤ "∃ α. α → α"
  , "(∀ α. C α) → (∀ α. C α)" ≤ "∃ α. α → α"
  , "∃ β. (∀ α. C α β) → (∀ α. C α β)" ≤ "∃ α. α → α"
  , "∃ β γ. (∀ α. C α β) → (∀ α. C α γ)" /≤ "∃ α. α → α"
  , "(∀ α. C α β) → (∀ α. C α γ)" ≤ "∃ α. α → α"
  , "(∀ α. C α β β D) → (∀ α. C α γ D γ)" ≤ "∃ α. α → α"
  , "(∀ α. C α β β D) → (∀ α. C α γ E γ)" /≤ "∃ α. α → α"
  -- universal/existential interaction
  , "∀ α. C α" ≤  "∃ α. C α"
  , "∀ α. C α" /≥ "∃ α. C α"
  , "∀α. ∃β. C α β" ≤ "∃β. C α β"
  -- quantifiers don't commute
  , "∀α. ∃β. C α β" /≤ "∃β. ∀α. C α β"
  , "∃β. ∀α. C α β" /≤ "∀α. ∃β. C α β"
  -- deep subsumption
  {-
  , "A → (∀α. L α)"   ≤ "A → L B"
  , "L B → A"         ≤ "(∀α. L α) → A"
  , "A → (∀α. L α)"  /≥ "A → L B"
  , "L B → A"        /≥ "(∀α. L α) → A"
  , "Maybe (∀α. L α)" ≤ "Maybe (L B)"
  , "Ref (∀α. L α)"  /≤ "Ref (L B)"
  , "Ref (∀α. L α)"  /≥ "Ref (L B)"
  , "A → (∃α. L α)"   ≥ "A → L B"
  , "L B → A"         ≥ "(∃α. L α) → A"
  , "A → (∃α. L α)"  /≤ "A → L B"
  , "L B → A"        /≤ "(∃α. L α) → A"
  , "Maybe (∃α. L α)" ≥ "Maybe (L B)"
  , "Ref (∃α. L α)"  /≥ "Ref (L B)"
  , "Ref (∃α. L α)"  /≤ "Ref (L B)"
  , "((∀α. A α) → ∃β. B β) → ∀γ. C γ"
                      ≤ "(A X → B Y) → C Z"
  -}
  -- don't allow existential hoisting
  , "∀α. α → (∃β. List β)" /≤ "∀α ∃β. α → List β"
  , "∀α. α → (∃β. β)"       ≤ "∀α ∃γ. α → γ" -- not actually hoisting
  ]
  where
  a ≥ b  = T.assertBool (a ++ " ≥ " ++ b)
              (either f t (showSubsumeAnnot (nr a) (nr b)))
  a /≥ b = T.assertBool (a ++ " /≥ " ++ b)
              (either t f (showSubsumeAnnot (nr a) (nr b)))
  a ≤ b  = b ≥ a
  a /≤ b = b /≥ a
  nr = normalizeAnnot . read
  f = const False
  t = const True

inferFnTests ∷ T.Test
inferFnTests = T.test
  [ "A"         -: "A"
  , "A B C"     -: "A B C"
  , "λx.x"     -: "∀ α. α → α"
  -- predicative vs. impredicative
  , "λα.id id" -: "∀ α β. α → β → β"
  , "id (id : ∀ α. α → α)"
                -: "∀ α. α → α"
  , "(id : (∀ α. α → α) → β) id"
                -: "∀ α. α → α"
  , "(id : β → (∀ α. α → α)) id"
                -: "∀ α. α → α"
  , "(id : (∀ α. α → α) → ∀ α. α → α) id"
                -: "∀ α. α → α"
  , "auto id"   -: "∀ α. α → α"
  , "apply auto id" -: "∀ α. α → α"
  , "λx.choose id"
                -: "∀ β α. β → (α → α) → α → α"
  , "λx.(choose : (∀ α. α → α) → β → β) id"
                -: "∀ β. β → (∀ α. α → α) → (∀ α. α → α)"
  , "λx.choose (id : ∀ α. α → α)"
                -: "∀ β. β → (∀ α. α → α) → (∀ α. α → α)"
  , "λx.choose id auto"
                -: "∀ α. α → (∀ α. α → α) → (∀ α. α → α)"
  , "λx.choose auto id"
                -: "∀ α. α → (∀ α. α → α) → (∀ α. α → α)"
  , "λx.choose xauto xauto"
                -: "∀ α β. α → (∀ γ. γ → γ) → β → β"
  , "λx. choose nil ids"
                -: "∀ β. β → List (∀ α. α → α)"
  , "λx. choose ids nil"
                -: "∀ β. β → List (∀ α. α → α)"
  , "poly id"   -: "Pair Int Bool"
  , "apply poly id"     -: "Pair Int Bool"
  , "revapp id poly"    -: "Pair Int Bool"
  , "head ids A"        -: "A"
  , "λ(f : ∀ α. α → α). P (f A) (f B)"
                -: "(∀ α. α → α) → P A B"
  , te "λf. P (f A) (f B)"
  , "λx. single id" -: "∀ α β. α → List (β → β)"
  , "(single : (∀ α. α → α) → List (∀ α. α → α)) id"
                -: "List (∀ α. α → α)"
  , "(single : (∀ α. α → α) → β) id"
                -: "List (∀ α. α → α)"
  , "(single : β → List (∀ α. α → α)) id"
                -: "List (∀ α. α → α)"
  , "single (id : ∀ α. α → α)"
                -: "List (∀ α. α → α)"
  , te "single id : List (∀ α. α → α)"
  , te "λf. f f"
  , te "λx. poly x"
  , te "poly (id id)"
  , "poly ((id : (∀ α. α → α) → β) id)"
                -: "Pair Int Bool"
  , "poly (id (id : ∀ α. α → α))"
                -: "Pair Int Bool"
  , "single (single (id : ∀ α. α → α))"
                -: "List (List (∀ α. α → α))"
  -- ST Monad
  , "runST (λt. bindST (newSTRef A) readSTRef)"
                -: "A"
  , "apply runST (λt. bindST (newSTRef A) readSTRef)"
                -: "A"
  , "revapp (λt. bindST (newSTRef A) readSTRef) runST"
                -: "A"
  , "runST (λt. bindST (newSTRef A) (λr. returnST A))"
                -: "A"
  , te "runST (λt. bindST (newSTRef A) (λr. returnST r))"
  -- Value restriction
  , "let r = ref nil in writeRef r (cons A nil)"
                -: "T"
  , "let r = ref nil in let t = writeRef r (cons A nil) in r"
                -: "Ref (List A)"
  , "let r = ref nil in let t = writeRef r (cons A (readRef r)) in r"
                -: "Ref (List A)"
  , "let r = ref nil in \
   \ let t = writeRef r (cons A nil) in \
   \ let t = writeRef r (cons A nil) in r"
                -: "Ref (List A)"
  , te "let r = ref nil in \
      \ let t = writeRef r (cons A nil) in \
      \ let t = writeRef r (cons B nil) in r"
  , "let r = ref nil in \
   \ let t = writeRef r (cons A (readRef r)) in \
   \ let t = writeRef r (cons A (readRef r)) in r"
                -: "Ref (List A)"
  , te "let r = ref nil in \
      \ let t = writeRef r (cons A (readRef r)) in \
      \ let t = writeRef r (cons B (readRef r)) in r"
  -- Scoped type variables
  , "λ (x : α) (y : β). pair x y"
                -: "∀ α β. α → β → Pair α β"
  , "λ (x : α) (y : α). pair x y"
                -: "∀ α. α → α → Pair α α"
  , "λ (x : α) (y : β). pair x (y : α)"
                -: "∀ α. α → α → Pair α α"
  , "λ (x : α) (y : β). pair x y : Pair β α"
                -: "∀ α. α → α → Pair α α"
  , "λ (x : α) (y : β). pair x y : Pair β γ"
                -: "∀ α. α → α → Pair α α"
  , "λ (x : α) (y : β). pair x y : Pair γ α"
                -: "∀ α. α → α → Pair α α"
  -- Type annotations
  , "(λx.x) : ∀ α. α → α"
                -: "∀α. α → α"
  , "(λx.x) : Z → Z"
                -: "Z → Z"
  , te "(λx.x) : Y → Z"
  , "λZ.(λx.x) : α"
                -: "∀α. Z → α → α"
  , "((λx.x) : ∀ α. α → α) : Z → Z"
                -: "Z → Z"
  , te "((λx.x) : Z → Z) : ∀α. α → α"
  , te "(λ(x : Z).x) : ∀α. α → α"
  -- Type annotation propagation
  , te "λ f . P (f A) (f B)"
  , "λ(f : ∀ α. α → α). P (f A) (f B)"
                -: "(∀ α. α → α) → P A B"
  , "(λf. P (f A) (f B)) : (∀ α. α → α) → P A B"
                -: "(∀ α. α → α) → P A B"
  , "(λf. P (f A) (f B)) : (∀ α. α → α) → β"
                -: "(∀ α. α → α) → P A B"
  , te "(λf. P (f A) (f B)) : ∀ β. (∀ α. α → α) → β"
  , "List (λx.x)"
                -: "∀ α. List (α → α)"
  , "List ((λx. x) : ∀ α. α → α)"
                -: "List (∀ α. α → α)"
  , "List (λx. x) : ∀ α. List (α → α)"
                -: "∀ α. List (α → α)"
  , "List (λx. x) : List (∀ α. α → α)"
                -: "List (∀ α. α → α)"
  , "λx. (List (λx.x) : List α)"
                -: "∀ α β. α → List (β → β)"
  , "List (λ(x: ∀ α. α → α). x)"
                -: "∀ α. List ((∀ α. α → α) → α → α)"
  , "List (λ(x: ∀ α. α → α). (x : ∀ α. α → α))"
                -: "List ((∀ α. α → α) → ∀ α. α → α)"
  , te "List (λx. (x : ∀ α. α → α))"
  , "List ((λx.x) : (∀ α. α → α) → (∀ α. α → α))"
                -: "List ((∀ α. α → α) → ∀ α. α → α)"
  , "List ((λx.x) : (∀ α. α → α) → β)"
                -: "∀ α. List ((∀ α. α → α) → α → α)"
  , "List (λx.x) : List ((∀ α. α → α) → ∀ α. α → α)"
                -: "List ((∀ α. α → α) → ∀ α. α → α)"
  , "List (λx.x) : ∀ β. List ((∀ α. α → α) → β → β)"
                -: "∀ β. List ((∀ α. α → α) → β → β)"
  , "List (λx.x) : ∀ β. List ((∀ α. α → β) → (∀ α. α → β))"
                -: "∀ β. List ((∀ α. α → β) → (∀ α. α → β))"
  , "List (λx.x) : List (∀ β. (∀ α. α → β) → (∀ α. α → β))"
                -: "List (∀ β. (∀ α. α → β) → (∀ α. α → β))"
  -- Type propagation from formal to actual arguments
  , "λ(poly : (∀ α. α → α) → Z). poly (λx.x)"
                -: "((∀ α. α → α) → Z) → Z"
  , "(λ(poly : (∀ α. α → α) → Z). poly (λx.x)) (λf. f Z)"
                -: "Z"
  , "(λ(poly : (∀ α. α → α) → β). poly (λx.x)) (λf. f Z)"
                -: "Z"
  , "((λpoly. poly (λx.x)) : ((∀ α. α → α) → Z) → Z) (λf. f Z)"
                -: "Z"
  , "((λpoly. poly (λx.x)) : ((∀ α. α → α) → β) → β) (λf. f Z)"
                -: "Z"
  -- Patterns
  , "λA. B"     -: "A → B"
  , "λ(A x). x"
                -: "∀ α. A α → α"
  , "λ(A x) (B y z). x y z"
                -: "∀ α β γ. A (α → β → γ) → B α β → γ"
  , pe "λ(A x x). B"
  , "λ(A α (B β γ) (C δ (D e f g))). E"
                -: "∀ α β γ δ e f g. A α (B β γ) (C δ (D e f g)) → E"
  , "λ(A α (B β γ) (C δ (D e f g))). (E α g : E m m)"
                -: "∀ α β γ δ e f. A α (B β γ) (C δ (D e f α)) → E α α"
  , "λ(A α (B β γ)). (C α (B β γ) : C m m)"
                -: "∀ α β. A (B α β) (B α β) → C (B α β) (B α β)"
  , "λ(A α (B β γ)). (C α (B (β:α) γ) : C α bc)"
                -: "∀ α β. A α (B α β) → C α (B α β)"
  , te "λ(A α (B β γ)). C α (B (β:α) γ : α)"
  -- Patterns with type annotations
  , "λ(x:A). x"
                -: "A → A"
  , "λ(x: A α). x"
                -: "∀ α. A α → A α"
  , "λ(x: A (∀ α. α → α)). (λ(A f). f) x B"
                -: "A (∀ α. α → α) → B"
  , "λ(A x: α). x"
                -: "∀ α. A α → α"
  , "λ(A x: α) (A y: α). x"
                -: "∀ α. A α → A α → α"
  , "λ(A x: α) (y: α). x"
                -: "∀ α. A α → A α → α"
  , "λ(A x: A α) (y: α). x"
                -: "∀ α. A α → α → α"
  , "λ(A (x: α)) (y: α). x"
                -: "∀ α. A α → α → α"
  , te "λ(A x: α) (B y: α). x"
  , te "λ(f: (∀ α. α) → A) (K k). k f"
  , "λ(f: (∀ α. α) → A) (K (k : ((∀ α. α) → A) → Z)). k f"
                -: "((∀ α. α) → A) → (K (((∀ α. α) → A) → Z)) → Z"
  , "λ(f: (∀ α. α) → A) (K k : K (((∀ α. α) → A) → Z)). k f"
                -: "((∀ α. α) → A) → (K (((∀ α. α) → A) → Z)) → Z"
  , "λ(x : α) (y : β) ((z : β) : α). U"
                -: "∀ α. α → α → α → U"
  , "λ(x : α) (y : β) (z : β). (z : α)"
                -: "∀ α. α → α → α → α"
  , "λ(x : A (∀ α. α → α)). x"
                -: "A (∀ α. α → α) → A (∀ α. α → α)"
  , "λ(A x : A (∀ α. α → α)). P (x A) (x B)"
                -: "A (∀ α. α → α) → P A B"
  , "(λ(A x). P (x A) (x B)) : A (∀ α. α → α) → P A B"
                -: "A (∀ α. α → α) → P A B"
  , "(λ(A x). P (x A) (x B)) : A (∀ α. α → α) → β"
                -: "A (∀ α. α → α) → P A B"
  , te "(λ(A x). P (x A) (x B))"
  , "λ(A x : ∀ α. A (α → α)). x"
                -: "∀ α. (∀ β. A (β → β)) → α → α"
  , "λZ.(λ(A x). x) : (∀ β. A (β → β)) → z"
                -: "∀ α. Z → (∀ β. A (β → β)) → α → α"
  , "λ((A x y : A β C) : A B γ). D"
                -: "A B C → D"
  , "(λ(A x y : A β C). D) : A B γ → δ"
                -: "A B C → D"
  -- Let pattern annotations
  , "let f : (∀α. α → α) → Z → Z = λx.x in f"
                -: "(∀α. α → α) → Z → Z"
  , "λZ. let P f g = P (λx.x) (λx.x) in P f g"
                -: "∀α β. Z → P (α → α) (β → β)"
  , "λZ. let P f g : P α α = P (λx.x) (λx.x) in P f g"
                -: "∀α. Z → P (α → α) (α → α)"
  , "λZ. let P (f:α) (g:β) = P (λx.x) (λx.x) in P f g"
                -: "∀α β. Z → P (α → α) (β → β)"
  , "λZ. let P (f:α) (g:α) = P (λx.x) (λx.x) in P f g"
                -: "∀α. Z → P (α → α) (α → α)"
  , "let P (f: ∀α. α → α) (g: ∀α. α → α) = P (λx.x) (λx.x) in \
    \ Q (f A) (g A) (f B) (g B)"
                -: "Q A A B B"
  , "let P (f: ∀α. α → α) (g: ∀α. α → α) = P (λx.x) (λx.x) in \
    \ P (f A) (f B)"
                -: "P A B"
  , te "let P (f: ∀α. α → α) g = P (λx.x) (λx.x) in \
       \ P (f A) (f B)"
  , te "let P (f: ∀α. α → α) g = P (λx.x) ((λx.x) : ∀a. a → a) in \
       \ P (f A) (f B)"
  , "let P (f: ∀α. α → α) g = P ((λx.x) : ∀a. a → a) \
    \                           ((λx.x) : ∀a. a → a) in \
    \ P (f A) (f B)"
                -: "P A B"
  , "let P f g = P ((λx.x) : ∀a. a → a) ((λx.x) : ∀a. a → a) in \
    \ P (f A) (f B)"
                -: "P A B"
  -- Let rec
  , "let rec f = λx y z. f x z y in f"
                -: "∀α β γ. α → β → β → γ"
  , "let rec f = λx. app x (f x) in f"
                -: "∀α. List α → List α"
  , "let rec f = λx. app x (f x) in P (f (List A)) (f (List B))"
                -: "P (List A) (List B)"
  , "let rec f : ∀α. List α → List α = λx. app x (f x) in f"
                -: "∀α. List α → List α"
  , "let rec f : ∀α. List α → List α = λx. app x (f x) \
    \ in P (f (List A)) (f (List B))"
                -: "P (List A) (List B)"
  , te "let rec f = (λx.x) (λx. app x (f x)) in f"
  , "let rec P f g = P (λx. app x (g x)) (λy. app (f y) y) \
    \ in P f g"
                -: "∀α β. P (List α → List α) (List β → List β)"
  , "let rec P f g = P (λx. app x (g x)) (λy. app (f y) y) \
    \ in P (f: ∀α. List α → List α) (g: ∀α. List α → List α)"
                -: "P (∀α. List α → List α) (∀β. List β → List β)"
  , "let rec y = λf. f (y f) in y"
                -: "∀α. (α → α) → α"
  , "let rec y = λf x. f (y f) x in y"
                -: "∀α β. ((α → β) → α → β) → α → β"
  , "let rec C f = C (λx. f (f x)) in f"
                -: "∀α. α → α"
  -- (Let rec polymorphic recursion:)
  , te "let rec f = λx. choose (single x) (head (f (single x))) in f"
  , "let rec f : ∀α. α → List α = \
    \       λx. choose (single x) (head (f (single x))) in f"
                -: "∀α. α → List α"
  ----
  ---- Existential quantification
  ----
  -- Construction
  , "Z : ∃α. α"
                -: "∃α. α"
  , "P Y Z : ∃α. α"
                -: "∃α. α"
  , "P Y Z : ∃α. P Y α"
                -: "∃α. P Y α"
  , te "P Y Z : ∃α. P α α"
  , "P Y Z : ∃α. P ε α"
                -: "∃α. P Y α"
  , "P Z Z : ∃α. P α α"
                -: "∃α. P α α"
  , "P Z Z : ∃α. P Z α"
                -: "∃α. P Z α"
  , "P Z Z : ∃α. P ε α"
                -: "∃α. P Z α"
  -- Impredicative instantiation to ∃
  , "(λx.x) (Z : ∃α. α)"
                -: "∃α. α"
  , "let z : ∃α. α = Z in (λx.x) z"
                -: "∃α. α"
  , "let z : ∃α. α = Z in (λx.Y) z"
                -: "Y"
  , "let z : ∃α. α = Z in (λ(x:∃α.α).Y) z"
                -: "Y"
  , "let f : ∀ α. A α → Z = λ_. Z in \
    \let x : ∃ α. A α = A B in \
    \  f x"
                -: "Z"
  , "let x : ∃α. B α = B A in (λ(B _). Z) x"
                -: "Z"
  -- Constructing data with ∃
  , "let x : ∃α. B α = B A in C x"
                -: "C (∃α. B α)"
  , "let x : ∃α. B α = B A in single x"
                -: "List (∃α. B α)"
  -- Existential unpacking and repacking
  , "let f = λ(B x). B x in     \
    \let x : ∃α. B α = B A in   \
    \  f x"
                -: "∃α. B α"
  , "λ(x: ∃α. List α). x"
                -: "(∃α. List α) → ∃α. List α"
  , "λ(x: ∃α. List α). x : List β"
                -: "∃α. (∃α. List α) → List α"
  , "λ(f : ∀α. α → D α) (e : ∃α. C α). f e"
                -: "(∀α. α → D α) → (∃α. C α) → D (∃α. C α)"
  , "λ(f : ∀α. C α → D α) (e : ∃α. C α). f e"
                -: "(∀α. C α → D α) → (∃α. C α) → ∃α. D α"
  , "λ(f : ∀α. C α → D α α) (e : ∃α. C α). f e"
                -: "(∀α. C α → D α α) → (∃α. C α) → ∃α. D α α"
  , "λ(f : ∀α β. C α → C β → D α β) (e : ∃α. C α). f e e"
                -: "(∀α β. C α → C β → D α β) → (∃α. C α) → ∃α β. D α β"
  , "λ(f : ∀α. α → D α) (C e : ∃α. C α). f e"
                -: "(∀α. α → D α) → ∃α. (∃α. C α) → D α"
  , "λ(f : ∀α. α → D α) (C e : ∃α. C α). (f e : ∃α. D α)"
                -: "(∀α. α → D α) → (∃β. C β) → ∃α. D α"
  -- with propagation
  , "(λf e. f e) : (∀α. α → D α) → (∃α. C α) → D (∃α. C α)"
                -: "(∀α. α → D α) → (∃α. C α) → D (∃α. C α)"
  , "(λf e. f e) : (∀α. C α → D α) → (∃α. C α) → ∃α. D α"
                -: "(∀α. C α → D α) → (∃α. C α) → ∃α. D α"
  , "(λf e. f e) : (∀α. C α → D α α) → (∃α. C α) → ∃α. D α α"
                -: "(∀α. C α → D α α) → (∃α. C α) → ∃α. D α α"
  , "(λf e. f e e) : (∀α β. C α → C β → D α β) → (∃α. C α) → ∃α β. D α β"
                -: "(∀α β. C α → C β → D α β) → (∃α. C α) → ∃α β. D α β"
                {-
  , "(λf e. f e) : (∀α. α → D α) → ∃α. (∃α. C α) → D α"
                -: "(∀α. α → D α) → ∃α. (∃α. C α) → D α"
  , "(λf e. f e) : (∀α. α → D α) → (∃β. C β) → ∃α. D α"
                -: "(∀α. α → D α) → (∃β. C β) → ∃α. D α"
                -}
  -- Destruction by pattern matching
  , "λ(e : ∃α. C (D α) (D α)).          \
    \let C x y = e in           \
    \  choose x y"
                -: "(∃α. C (D α) (D α)) → ∃α. D α"
  , "λ(e : ∃α. C (D α) (D α)).          \
    \let C x y = e in           \
    \  (choose x y : ∃α. D α)"
                -: "(∃α. C (D α) (D α)) → ∃α. D α"
  -- Existentials don't match other stuff
  , "let x : ∃α. C α = C A in        \
    \let y : ∃α. C α = C A in        \
    \let P (C x') (C y') = P x y in  \
    \choose x y"
                -: "∃α. C α"
  , te "let x : ∃α. C α = C A in        \
       \let y : ∃α. C α = C A in        \
       \let P (C x') (C y') = P x y in  \
       \choose x' y'"
  , te "let x : ∃α. C α = C A in        \
       \let y : ∃α. C α = C A in        \
       \λ(f : ∀α. C α → C α → Z). f x x"
  , "let x : ∃α. C α = C A in        \
    \let y : ∃α. C α = C A in        \
    \λ(f : ∀α. C α → C α → Z). let z : C ε = x in f z z"
              -: "(∀α. C α → C α → Z) → Z"
  , te "let x : ∃α. C α = C A in        \
       \let y : ∃α. C α = C A in        \
       \λ(f : ∀α. C α → C α → Z). f x y"
  , "let x : ∃α. C α = C A in        \
    \let y : ∃α. C α = C A in        \
    \λ(f : ∀α. α → α → Z). f x y"
                -: "(∀α. α → α → Z) → Z"
  , te "let e : ∃α. Pair α (α → Int) = Pair Int (λx.x) in (snd e) (fst e)"
  , "let e : ∃α. Pair α (α → Int) = Pair Int (λx.x) in  \
    \(λp. (snd p) (fst p)) e"
                -: "Int"
  , te "let e : ∃α. Pair α (α → C α) = Pair Int (λx.C x) in (snd e) (fst e)"
  , "let e : ∃α. Pair α (α → C α) = Pair Int (λx.C x) in  \
    \(λp. (snd p) (fst p)) e"
                -: "∃α. C α"
  ----
  ---- Deep subsumption
  ----
  {-
  , "let f = λx.x in f : (∀α. α → α) → Z → Z"
                -: "(∀α. α → α) → Z → Z"
  , "λ_.choose id xauto"
                -: "∀α β. α → (∀γ. γ → γ) → β → β"
  -- previous and next -> odd
  , te "λ_.choose xauto id"
  -}
  -- don't allow existential hoisting
  -- , "λ(f : ∀α → ∃β. List β) x. f x"
  ]
  where
  a -: b = T.assertBool ("⊢ " ++ a ++ " : " ++ b)
             (showInfer (read a) == Right (fmap elimEmpty (read b)))
  te a   = T.assertBool ("¬⊢ " ++ a)
             (either (const True) (const False) (showInfer (read a)))
  pe a   = T.assertBool ("expected syntax error: " ++ a)
             (length (reads a ∷ [(Term Empty, String)]) /= 1)

-}
---
--- Debugging
---

-}
-- | Super sketchy!
unsafeReadTV ∷ TV s → Maybe (TypeR s)
unsafeReadTV TV { tvRef = r } = unsafeReadRef r

debug ∷ Bool
debug = False

trace ∷ (MonadU r m, Show a) ⇒ a → m ()
trace = if debug
          then unsafeIOToU . print
          else const (return ())

