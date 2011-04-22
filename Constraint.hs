{-#
  LANGUAGE
    FlexibleContexts,
    FlexibleInstances,
    FunctionalDependencies,
    ImplicitParams,
    KindSignatures,
    MultiParamTypeClasses,
    ParallelListComp,
    ScopedTypeVariables,
    TupleSections,
    UnicodeSyntax
  #-}
module Constraint {-(
  -- * Generic constraints
  Constraint(..), (~≤~),
  -- * An implementation
  SubtypeConstraint,
) -} where

import qualified Data.List  as List
import qualified Data.Map   as Map
import qualified Data.Set   as Set
import qualified Data.Tree  as Tree

-- From fgs:
import Data.Graph.Inductive.PatriciaTree (Gr)
import Data.Graph.Inductive.Basic        (preorder)
import qualified Data.Graph.Inductive.Graph             as Gr
import qualified NodeMap                                as NM
import qualified Data.Graph.Inductive.Query.DFS         as DFS
import qualified Data.Graph.Inductive.Query.TransClos   as TransClos

import Syntax
import MonadU
import MonadRef
import Util
import Ppr
import qualified UnionFind as UF

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
data Atom tv = VarAt !tv
             | ConAt !Name
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
      NM.insMapNodesM ["U", "R", "A", "L"]
      NM.insMapEdgesM [("U","R",()), ("U","A",()), ("R","L",()), ("A","L",())]

-- | Is one type constructor less than or equal to another?
tyConLe ∷ Name → Name → Bool
tyConLe c1 c2
  | c1 == c2  = True
  | otherwise = Gr.gelem n1 tyConOrder && n2 `elem` Gr.suc tyConOrder n1
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

-- | Find the join or meet of a pair of type constructors, if possible
tyConJoin, tyConMeet ∷ Monad m ⇒ Name → Name → m Name
tyConJoin = tyConCombine (Gr.suc tyConOrder) (Gr.outdeg tyConOrder)
                         "least upper bound"
tyConMeet = tyConCombine (Gr.pre tyConOrder) (Gr.indeg tyConOrder)
                         "greatest lower bound"

tyConCombine ∷ Monad m ⇒ 
               (Gr.Node → [Gr.Node]) → (Gr.Node → Int) → String →
               Name → Name → m Name
tyConCombine next countNext goalName c1 c2
  | c1 == c2               = return c1
  | n1 ← tyConNode c1
  , n2 ← tyConNode c2
  , Gr.gelem n1 tyConOrder
  , Gr.gelem n2 tyConOrder =
    let common  = [ (countNext n, Gr.lab tyConOrder n)
                  | n ← next n1 `List.intersect` next n2 ]
     in case reverse (List.sort common) of
          [(_,Just c)]               → return c
          (j,Just c):(k,_):_ | j > k → return c
          _                          → giveUp
  | otherwise              = giveUp
  where giveUp = fail $
          "Type constructors " ++ c1 ++ " and " ++ c2 ++
          " have no " ++ goalName ++ "."

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

-- | Simple subtype constraints relate pairs of types:
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
  --  1. decompose: subtype-unify all subtype constraints until we have
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
    let ?deref = readTV
    trace ("gen (begin)", c0, τ)
    skm1         ← internalize (SC c0)
    trace ("gen (internalized)", skm1)
    αs           ← occursCheck skm1
    trace ("gen (occursCheck)", αs)
    skm2         ← expand skm1 αs
    trace ("gen (expand)", skm2)
    c1           ← decompose c0
    γftv         ← ftvSet γ
    τftv         ← ftvVs τ
    trace ("gen (decompose)", c1, γftv, τftv, τ)
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
      -- decompose takes a list of subtype constraint pairs and a list
      -- of type variables, and returns when all of the constraint is
      -- reduced to pairs of atoms.
      decompose = concatMapM decompLe where
        decompLe (τ10, τ20) = do
          τ1 ← deref τ10
          τ2 ← deref τ20
          case (τ1, τ2) of
            (VarTy (FreeVar α), VarTy (FreeVar β))
              | α == β
              → return []
              | otherwise
              → return [(VarAt α, VarAt β)]
            (ConTy c [],        ConTy c' [])
              | c `tyConLe` c'
              → return []
            (VarTy (FreeVar α), ConTy c' [])
              | tyConHasPreds c'
              → return [(VarAt α, ConAt c')]
            (ConTy c [], VarTy (FreeVar β))
              | tyConHasSuccs c
              → return [(ConAt c, VarAt β)]
            (ConTy c1 τs1,      ConTy c2 τs2)
              | c1 == c2
              → concatMapM id
                  [ case var of
                      Covariant     → decompLe (τ1', τ2')
                      Contravariant → decompLe (τ2', τ1')
                      Invariant     → (++) <$> decompLe (τ1', τ2')
                                           <*> decompLe (τ2', τ1')
                      Omnivariant   → return []
                  | τ1' ← τs1
                  | τ2' ← τs2
                  | var ← getVariances c1 (length τs1) ]
              | otherwise
              → fail $
                  "Could not unify type constructors: " ++ c1 ++ " and " ++ c2
            (VarTy (FreeVar _), ConTy _ _)
              → fail "BUG! gen (decompose) saw unexpanded tyvar"
            (ConTy _ _,         VarTy (FreeVar _))
              → fail "BUG! gen (decompose) saw unexpanded tyvar"
            (_,                 _)
              → do
                τ1' ← derefAll τ1
                τ2' ← derefAll τ2
                fail $ "Could not unify: " ++ show τ2' ++ " ≤ " ++ show τ1'
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
        trace ("existentials are:", extvs)
        return (Set.fold (eliminateNode nm) g extvs)
        where
      -- Given a node label and a graph, remove the node, connecting
      -- all its predecessors to all its successors.
      eliminateNode nm α g =
        case (Gr.pre g node, Gr.suc g node) of
          (preds@(_:_), succs@(_:_)) →
            Gr.insEdges [ (n1, n2, ())
                        | n1 ← preds, n1 /= node
                        , n2 ← succs, n2 /= node, n2 /= n1 ]
                        (Gr.delNode node g)
          _                          → g
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
          findSingles = Map.foldrWithKey keep []
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

-- | A representation of equivalence classes of same-sized type
--   variables and their shapes.
newtype SkelMap tv m
  = SkelMap {
      -- | Associates each type variable with the “skeleton” that
      --   contains it, which is a set of related type variables and
      --   maybe a constructor applied to some type variables, which
      --   determines the shape of the skeleton.
      unSkelMap   ∷ Map.Map tv (Skeleton tv (URef m))
    }
type Skeleton tv r = UF.Proxy r (Set.Set tv, Maybe (Name, [tv]))

type ExtSkels tv = [(tv, [tv], Maybe (Name, [tv]))]

instance (Tv tv, MonadU tv m) ⇒
         Show (SkelMap tv m) where
  show skm = concat $
    [ " ⋀ {" ++ show α ++ " ∈ " ++
      concat (List.intersperse "≈" [ show (tvUniqueID β) | β ← βs ]) ++
      case shape of
        Nothing      → ""
        Just (c, γs) →
          " ≈ " ++ unwords (c : [ show (tvUniqueID γ) | γ ← γs ])
      ++ "}"
    | (α, βs, shape) ← extSkels skm ]

extSkels ∷ MonadU tv m ⇒ SkelMap tv m → ExtSkels tv
extSkels = unsafePerformU . extSkelsM

-- | Produce a showable representation of an internalized subtype
--   constraint
extSkelsM ∷ MonadU tv m ⇒ SkelMap tv m → m (ExtSkels tv)
extSkelsM = mapM each . Map.toList . unSkelMap
  where
    each (α, proxy) = do
      (set, mshape) ← UF.desc proxy
      return (α, Set.toList set, mshape)

newtype SHOW_GRAPH gr v = SHOW_GRAPH { unSHOW_GRAPH ∷ gr v () }

instance (Gr.Graph gr, Show v) ⇒ Show (SHOW_GRAPH gr v) where
  showsPrec _ (SHOW_GRAPH gr) =
    showChar '{' .
    foldr (.) id
      (List.intersperse (showString " ⋀ ")
         [ shows n1 . showChar '≤' . shows n2
         | (n1, n2) ← labEdges gr ])
    . showChar '}'

-- | Build an internal subtype constraint from an external subtype
--   constraint.
internalize ∷ MonadU tv m ⇒
              SubtypeConstraint tv → m (SkelMap tv m)
internalize sc0 = do
  rskels ← newRef Map.empty
  let -- | Record that @τ1@ is a subtype of @τ2@, and do some
      --   unification.
      addSubtype (τ1, τ2) = do
        α1 ← tvOf τ1
        α2 ← tvOf τ2
        relateTVs α1 α2
      -- | Relate two type variables in the same skeleton
      relateTVs α1 α2 = do
        skel1 ← getSkel α1
        skel2 ← getSkel α2
        UF.coalesce combiner skel1 skel2
      -- | Get the skeleton associated with a type variable. If it doesn't
      --   exist, create it. This may require creating a shape, which may
      --   recursively create skeletons for type constructor arguments.
      getSkel α = do
        skels ← readRef rskels
        case Map.lookup α skels of
          Just skel → return skel
          Nothing   → do
            shape ← getShape α
            skel  ← UF.create (Set.singleton α, shape)
            modifyRef (Map.insert α skel) rskels
            return skel
      -- | Build a new shape for a type variable. A shape is a "small type"
      --   comprising a type constructor name and type variables as
      --   arguments.  This may require generating more type variables to
      --   abstract concrete parameters appearing in the type.
      getShape α = do
        τ ← readTV α
        case τ of
          Left _               → return Nothing
          Right (ConTy con τs) → do
            αs     ← mapM tvOf τs
            mapM_ getSkel αs
            return (Just (con, αs))
          Right _              → fail $ "BUG! internalize"
      --
      -- Combine two skeletons
      combiner (αs1, shape1) (αs2, shape2) = do
        shape' ← case (shape1, shape2) of
          (Nothing, _)                   → return shape2
          (_, Nothing)                   → return shape1
          (Just (c1, []), Just (c2, [])) → Just . (,[]) <$> tyConJoin c1 c2
          (Just (c1, βs1), Just (c2, βs2))
            | c1 == c2 && length βs1 == length βs2
                                         → do
            sequence_ [ do
                          when (var /= Omnivariant) $ relateTVs β1 β2
                          when (var == Invariant) $ unifyTVs β1 β2
                      | var ← getVariances c1 (length βs1)
                      | β1  ← βs1
                      | β2  ← βs2 ]
            return (Just (c1, βs1))
          _                              → fail $
            "Could not unify " ++ show shape1 ++ " and " ++ show shape2
        return (Set.union αs1 αs2, shape')
      -- Unify (at equality) two type variables
      unifyTVs α1 α2 = do
        τ1 ← readTV α1
        τ2 ← readTV α2
        case (τ1, τ2) of
          (Left _, _) → linkTV α1 α2
          (_, Left _) → linkTV α2 α1
          (Right (ConTy c1 τs1), Right (ConTy c2 τs2))
            | c1 == c2 && length τs1 == length τs2 → do
                αs1 ← mapM tvOf τs1
                αs2 ← mapM tvOf τs2
                sequence_ [ when (var /= Omnivariant) $ unifyTVs α1 α2
                          | var ← getVariances c1 (length αs1)
                          | α1  ← αs1
                          | α2  ← αs2 ]
            | otherwise →
                fail $ "Could not unify " ++ show τ1 ++ " and " ++ show τ2
          _ → fail "BUG! internalize (unifyTVs): not yet supported"
      --
  mapM_ addSubtype (unSC sc0)
  SkelMap <$> readRef rskels

-- | Make sure an internal subtype constraint is consistent with a
--   finite model. Returns the type variables topologically sorted by
--   size (smallest first).
occursCheck ∷ ∀ tv m. MonadU tv m ⇒
              SkelMap tv m → m [tv]
occursCheck skm = do
  let skels = Map.toList (unSkelMap skm)
      gr0   = Gr.insNodes [ (tvUniqueID α, α) | (α, _) ← skels ] Gr.empty
  gr  ← foldM addSkel gr0 skels
  let scc = labScc (gr ∷ Gr tv ())
  trace ("occursCheck", Gr.edges gr, scc)
  mapM checkSCC scc
  where
  addSkel gr (α, proxy) = do
    (_, mshape) ← UF.desc proxy
    case mshape of
      Nothing      → return gr
      Just (_, βs) → foldM (assertGt α) gr βs
  assertGt α gr β = case Map.lookup β (unSkelMap skm) of
    Nothing        → fail "BUG! occursCheck (1)"
    Just proxy     → do
      (βs, _) ← UF.desc proxy
      return (foldr (addEdgeTo α) gr (Set.toList βs))
  addEdgeTo α β    = Gr.insEdge (tvUniqueID β, tvUniqueID α, ())
  checkSCC [(_,α)] = return α
  checkSCC lns     = fail $ "Occurs check failed: " ++ show (map snd lns)

-- | Expand all type variables to their full shape.
expand ∷ MonadU tv m ⇒
         SkelMap tv m → [tv] → m (SkelMap tv m)
expand skm0 αs0 = do
  rskels ← newRef (unSkelMap skm0)
  let expandTVs []     = return ()
      expandTVs (α:αs) = do
        αs' ← expandTV α
        expandTVs (αs'++αs)
      expandTV α = do
        eτ         ← readTV α
        case eτ of
          Right _ → return []
          Left α' → do
            Just proxy ← Map.lookup α <$> readRef rskels
            (_, shape) ← UF.desc proxy
            case shape of
              Nothing      → return []
              Just (_, []) → return []
              Just (c, βs) → do
                βs' ← replicateM (length βs) newTV
                writeTV α' (ConTy c (map fvTy βs'))
                sequence_
                  [ do
                      Just proxy   ← Map.lookup β <$> readRef rskels
                      (γs, shape') ← UF.desc proxy
                      UF.setDesc proxy (Set.insert β' γs, shape')
                      modifyRef (Map.insert β' proxy) rskels
                  | β  ← βs
                  | β' ← βs' ]
                return βs'
  expandTVs αs0
  skels' ← readRef rskels
  return skm0 { unSkelMap = skels' }

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

-- | Get the edges of a graph as pairs of node labels
labEdges ∷ Gr.Graph gr ⇒ gr n e → [(n, n)]
labEdges g =
  [ (α, β)
  | (n1, n2) ← Gr.edges g
  , let Just α = Gr.lab g n1
  , let Just β = Gr.lab g n2
  ]

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

{-
("gen (begin)",
 [(8 → 9 → 8, 7 → 10),
  (11 → List 11 → List 11, 7 → 12),
  (13 → List 13 → List 13, A → 14),
  (14,List 15 → 16), (12,16 → 17),
  (10, 17 → 18)],
 7 → 18)

("gen (decompose)",[(VarAt 20,VarAt 18),(VarAt 31,VarAt 32),(VarAt
30,VarAt 31),(VarAt 24,VarAt 30),(VarAt 29,VarAt 23),(VarAt
28,VarAt 29),(VarAt 15,VarAt 27),(VarAt 13,VarAt 28),(VarAt
27,VarAt 13),(ConAt "A",VarAt 13),(VarAt 11,VarAt 24),(VarAt
23,VarAt 11),(VarAt 7,VarAt 11),(VarAt 8,VarAt 20),(VarAt 7,VarAt
8)],fromList [],fromList [(7,[Contravariant]),(18,[Covariant])],7 →
18)

("existentials are:",fromList [8,11,13,15,20,23,24,27,28,29,30,31,32])

("gen (existentials)",SC {unSC = [(7,18)]},fromList [],fromList
[(7,[Contravariant]),(18,[Covariant])],7 → 18)


-}
