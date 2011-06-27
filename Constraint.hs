{-#
  LANGUAGE
    FlexibleContexts,
    FlexibleInstances,
    FunctionalDependencies,
    GeneralizedNewtypeDeriving,
    ImplicitParams,
    KindSignatures,
    MultiParamTypeClasses,
    ParallelListComp,
    ScopedTypeVariables,
    TupleSections,
    TypeFamilies,
    UndecidableInstances,
    UnicodeSyntax,
    ViewPatterns
  #-}
module Constraint {-(
  -- * Generic constraints
  Constraint(..), (~≤~),
  -- * An implementation
  SubtypeConstraint,
) -} where

import Prelude

import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.RWS
import Control.Monad.List
import qualified Data.List  as List
import qualified Data.Map   as Map
import qualified Data.Set   as Set

-- From fgs:
import Data.Graph.Inductive.PatriciaTree (Gr)
import qualified Graph   as Gr
import qualified NodeMap as NM

-- From incremental-sat-solver
import qualified Data.Boolean.SatSolver as SAT

import Syntax
import MonadU
import MonadRef
import Util
import Ppr
import Rank (Rank)
import qualified UnionFind as UF

---
--- A constraint-solving monad
---

class MonadU tv r m ⇒ MonadC tv r m | m → tv r where
  -- | Subtype and equality constraints
  (<:), (=:)    ∷ Type tv → Type tv → m ()
  -- | Subqualifier constraint
  (⊏:)          ∷ (Qualifier q1 tv, Qualifier q2 tv) ⇒ q1 → q2 → m ()
  -- | Constrain by the given variance
  rel           ∷ Variance → Type tv → Type tv → m ()
  rel v τ τ' = case v of
    Covariant      → τ <: τ'
    Contravariant  → τ' <: τ
    Invariant      → τ =: τ'
    QCovariant     → τ ⊏: τ'
    QContravariant → τ' ⊏: τ
    QInvariant     → τ ⊏: τ' >> τ' ⊏: τ
    Omnivariant    → return ()
  -- | Figure out which variables to generalize in a piece of syntax
  generalize'   ∷ Bool → Rank → Type tv → m ([tv], [QLit])
  -- | Generalize a type under a constraint and environment,
  --   given whether the the value restriction is satisfied or not
  generalize    ∷ Bool → Rank → Type tv → m (Type tv)
  generalize value γrank τ = do
    (αs, qls) ← generalize' value γrank τ
    standardizeMus =<< closeWithQuals qls AllQu αs <$> derefAll τ
  -- | Generalize a list of types together.
  generalizeList ∷ Bool → Rank → [Type tv] → m [Type tv]
  generalizeList value γrank τs = do
    (αs, qls) ← generalize' value γrank (tupleTy τs)
    mapM (standardizeMus <=< closeWithQuals qls AllQu αs <$$> derefAll) τs
  -- | Saves the constraint in an action that, when run, restores the
  --   saved constraint
  saveConstraint ∷ m (m ())
  -- | Return a string representation of the constraint
  showConstraint ∷ m String

infix 5 <:, =:, ⊏:

instance (MonadC tv s m, Monoid w) ⇒ MonadC tv s (WriterT w m) where
  (<:) = lift <$$> (<:)
  (=:) = lift <$$> (=:)
  (⊏:) = lift <$$> (⊏:)
  generalize'    = lift <$$$> generalize'
  saveConstraint = lift <$> lift saveConstraint
  showConstraint = lift showConstraint

instance (MonadC tv r m, Defaultable s) ⇒ MonadC tv r (StateT s m) where
  (<:) = lift <$$> (<:)
  (=:) = lift <$$> (=:)
  (⊏:) = lift <$$> (⊏:)
  generalize'    = lift <$$$> generalize'
  saveConstraint = lift <$> lift saveConstraint
  showConstraint = lift showConstraint

instance (MonadC tv p m, Defaultable r) ⇒ MonadC tv p (ReaderT r m) where
  (<:) = lift <$$> (<:)
  (=:) = lift <$$> (=:)
  (⊏:) = lift <$$> (⊏:)
  generalize'    = lift <$$$> generalize'
  saveConstraint = lift <$> lift saveConstraint
  showConstraint = lift showConstraint

instance (MonadC tv p m, Defaultable r, Monoid w, Defaultable s) ⇒
         MonadC tv p (RWST r w s m) where
  (<:) = lift <$$> (<:)
  (=:) = lift <$$> (=:)
  (⊏:) = lift <$$> (⊏:)
  generalize'    = lift <$$$> generalize'
  saveConstraint = lift <$> lift saveConstraint
  showConstraint = lift showConstraint

runConstraintT m = runEagerConstraintT m
-- runConstraintT m = runLazyConstraintT m

---
--- Lazy constraint solver using underlying subtyping constraint
---

newtype LazyConstraintT tv (r ∷ * → *) m a
  = LazyConstraintT {
      unLazyConstraintT_ ∷ StateT (SubtypeConstraint tv) m a
    }
  deriving (Functor, Applicative, Monad, MonadTrans)

runLazyConstraintT ∷ MonadU tv r m ⇒ LazyConstraintT tv r m a → m a
runLazyConstraintT m = evalStateT (unLazyConstraintT_ m) (⊤)

instance MonadRef r m ⇒ MonadRef r (LazyConstraintT tv r m) where
  newRef        = lift <$> newRef
  readRef       = lift <$> readRef
  writeRef      = lift <$$> writeRef
  unsafeIOToRef = lift <$> unsafeIOToRef

instance MonadU tv r m ⇒ MonadU tv r (LazyConstraintT tv r m) where
  newTVKind     = lift <$> newTVKind
  writeTV_      = lift <$$> writeTV_
  readTV_       = lift <$> readTV_
  getTVRank_    = lift <$> getTVRank_
  setTVRank_    = lift <$$> setTVRank_
  hasChanged    = lift hasChanged
  putChanged    = lift <$> putChanged
  unsafePerformU= error "No MonadU.unsafePerformU for LazyConstraintT"
  unsafeIOToU   = lift <$> unsafeIOToU

instance MonadU tv r m ⇒ MonadC tv r (LazyConstraintT tv r m) where
  τ <: τ' = LazyConstraintT (modify (⋀ τ ≤ τ'))
  τ =: τ' = LazyConstraintT (modify (⋀ τ ≤≥ τ'))
  τ ⊏: τ' = LazyConstraintT (modify (⋀ τ ⊏ τ'))
  generalize' value γrank τ = LazyConstraintT $ do
    c ← get
    (αs, qls, c') ← lift (gen' value c γrank τ)
    put c'
    return (αs, qls)
  saveConstraint = do
    c ← LazyConstraintT get
    return (LazyConstraintT (put c))
  showConstraint = show <$> LazyConstraintT get

---
--- Eager subtyping constraint solver
---

newtype EagerConstraintT tv r m a
  = EagerConstraintT {
      unEagerConstraintT_ ∷ StateT (EagerState tv r) m a
    }
  deriving (Functor, Applicative, Monad, MonadTrans)

data EagerState tv r
  = EagerState {
      esGraph   ∷ !(Gr (Atom tv) ()),
      esNodeMap ∷ !(NM.NodeMap (Atom tv)),
      esEquivs  ∷ !(ProxyMap tv r),
      esQuals   ∷ ![(Type tv, Type tv)]
    }
type TVProxy  tv r = UF.Proxy r (Set.Set tv)
type ProxyMap tv r = Map.Map tv (TVProxy tv r)

esQualsUpdate ∷ ([(Type tv, Type tv)] → [(Type tv, Type tv)]) →
                EagerState tv r → EagerState tv r
esQualsUpdate f es = es { esQuals = f (esQuals es) }

esEquivsUpdate ∷ (ProxyMap tv r → ProxyMap tv r) →
                 EagerState tv r → EagerState tv r
esEquivsUpdate f es = es { esEquivs = f (esEquivs es) }

instance Tv tv ⇒ Show (EagerState tv r) where
  showsPrec _ es = showString "EagerState { esGraph = "
                 . shows (Gr.ShowGraph (esGraph es))
                 . showString ", esQuals = "
                 . shows (esQuals es)
                 . showString " }"

runEagerConstraintT ∷ MonadU tv r m ⇒ EagerConstraintT tv r m a → m a
runEagerConstraintT m = evalStateT (unEagerConstraintT_ m) es0
  where es0        = EagerState {
                       esGraph   = gr0,
                       esNodeMap = nm0,
                       esEquivs  = Map.empty,
                       esQuals   = []
                     }
        (gr0, nm0) = NM.mkMapGraph
                       (map (ConAt . snd) (Gr.labNodes tyConOrder))
                       []

instance MonadRef r m ⇒ MonadRef r (EagerConstraintT tv r m) where
  newRef        = lift <$> newRef
  readRef       = lift <$> readRef
  writeRef      = lift <$$> writeRef
  unsafeIOToRef = lift <$> unsafeIOToRef

instance MonadU tv r m ⇒ MonadU tv r (EagerConstraintT tv r m) where
  newTVKind     = lift <$> newTVKind
  writeTV_      = lift <$$> writeTV_
  readTV_       = lift <$> readTV_
  getTVRank_    = lift <$> getTVRank_
  setTVRank_    = lift <$$> setTVRank_
  hasChanged    = lift hasChanged
  putChanged    = lift <$> putChanged
  unsafePerformU= error "No MonadU.unsafePerformU for EagerConstraintT"
  unsafeIOToU   = lift <$> unsafeIOToU

instance (Ord tv, Monad m) ⇒
         NM.MonadNM (Atom tv) () Gr (EagerConstraintT tv r m) where
  getNMState = EagerConstraintT (gets (esNodeMap &&& esGraph))
  getNodeMap = EagerConstraintT (gets esNodeMap)
  getGraph   = EagerConstraintT (gets esGraph)
  putNMState (nm, g) = EagerConstraintT . modify $ \es →
    es { esNodeMap = nm, esGraph = g }
  putNodeMap nm = EagerConstraintT . modify $ \es → es { esNodeMap = nm }
  putGraph g    = EagerConstraintT . modify $ \es → es { esGraph = g }

instance MonadU tv r m ⇒ MonadC tv r (EagerConstraintT tv r m) where
  τ <: τ' = runSeenT (subtypeTypesK 0 τ τ')
  τ =: τ' = runSeenT (unifyTypesK 0 τ τ')
  τ ⊏: τ' = EagerConstraintT . modify . esQualsUpdate $
              ((toQualifierType τ, toQualifierType τ') :)
  --
  generalize' value γrank τ = do
    let ?deref = readTV
    τftv ← ftvV τ;
    gtrace ("gen (begin)", value, γrank, τftv, τ)
    τftv ← coalesceSCCs τftv
    gtrace ("gen (scc)", τftv, τ)
    τftv ← satisfyTycons τftv
    gtrace ("gen (tycons)", τftv, τ)
    eliminateExistentials True (γrank, τftv)
    gtrace ("gen (existentials 1)", τftv, τ)
    removeRedundant
    gtrace ("gen (redundant)", τftv, τ)
    eliminateExistentials False (γrank, τftv)
    gtrace ("gen (existentials 2)", τftv, τ)
    τftv ← polarizedReduce τftv
    gtrace ("gen (polarized)", τftv, τ)
    eliminateExistentials False (γrank, τftv)
    gtrace ("gen (existentials 3)", τftv, τ)
    -- Guessing starts here
    τftv ← coalesceComponents value (γrank, τftv)
    gtrace ("gen (components)", τftv, τ)
    -- Guessing ends here
    qc    ← EagerConstraintT (gets esQuals)
    cftv  ← ftvSet . map snd =<< NM.getsGraph Gr.labNodes
    qcftv ← ftvSet qc
    αs    ← Set.fromDistinctAscList <$$>
              removeByRank γrank <$>
                Set.toAscList $
                  (qcftv `Set.union` Map.keysSet τftv) Set.\\ cftv
    (qc, αqs, τ) ← solveQualifiers value αs qc τ
    EagerConstraintT (modify (esQualsUpdate (const qc)))
    gtrace ("gen (finished)", αqs, τ)
    mapM_ (deleteTVProxy . fst) αqs
    return (map fst αqs, map snd αqs)
    where
      --
      -- Make sure the graph is satisfiable and figure out anything that
      -- is implied by the transitive closure of type constructors
      satisfyTycons τftv0 = do
        NM.insMapEdgesM [ (ConAt c1, ConAt c2, ())
                        | (c1, c2) ← Gr.labNodeEdges tyConOrder ]
        NM.modifyGraph Gr.trcnr
        satisfyTycons' τftv0
        where
        satisfyTycons' = iterChanging $ \τftv →
          foldM each τftv =<< NM.getsGraph Gr.labNodes
        each τftv (n, VarAt α) = do
          (nm, g) ← NM.getNMState
          let assign c = do
                τftv ← assignTV α (ConAt c) τftv
                let n' = Gr.nmLab nm (ConAt c)
                assignNode n n'
                return τftv
              lbs = [ c | Just (ConAt c) ← map (Gr.lab g) (Gr.pre g n)]
              ubs = [ c | Just (ConAt c) ← map (Gr.lab g) (Gr.suc g n)]
          glb ← case lbs of
                  []   → return Nothing
                  c:cs → Just <$> foldM tyConJoin c cs
          lub ← case ubs of
                  []   → return Nothing
                  c:cs → Just <$> foldM tyConMeet c cs
          case (glb, lub) of
            (Just c1, Just c2) | c1 == c2         → assign c1
            (Just c1, _) | not (tyConHasSuccs c1) → assign c1
            (_, Just c2) | not (tyConHasPreds c2) → assign c2
            _ → do
              case glb of
                Just lb | lb `notElem` lbs
                  → NM.insMapEdgeM (ConAt lb, VarAt α, ())
                _ → return ()
              case lub of
                Just ub | ub `notElem` ubs
                  → NM.insMapEdgeM (VarAt α, ConAt ub, ())
                _ → return ()
              return τftv
        each τftv (n, ConAt c1) = do
          g ← NM.getGraph
          sequence_
            [ if c1 `tyConLe` c2
                then return ()
                else fail $ "Cannot unify: " ++ c1 ++ " ≤ " ++ c2
            | Just (ConAt c2) ← map (Gr.lab g) (Gr.suc g n)]
          return τftv
      --
      -- Eliminate existentially-quantified type variables from the
      -- constraint
      eliminateExistentials trans (γrank, τftv) = do
        extvs ← getExistentials (γrank, τftv)
        trace ("existentials are:", extvs)
        mapM (eliminateNode trans) (Set.toList extvs)
      -- Get the existential type variables
      getExistentials (γrank, τftv) = do
        lnodes ← NM.getsGraph Gr.labNodes
        cftv   ← removeByRank γrank [ α | (_, VarAt α) ← lnodes ]
        return (Set.fromList cftv Set.\\ Map.keysSet τftv)
      -- Remove a node unless it is necessary to associate some of its
      -- neighbors -- in particular, a node with multiple predecessors
      -- but no successor (or dually, multiple successors but no
      -- predecessor) should not be removed.
      eliminateNode trans α = do
        (nm, g) ← NM.getNMState
        let node = Gr.nmLab nm (VarAt α)
        case (Gr.pre g node, Gr.suc g node) of
          (_:_:_, []) → return ()
          ([], _:_:_) → return ()
          (pre, suc)  → NM.putGraph $
            let g' = Gr.delNode node g in
            if trans
              then g'
              else foldr ($) g'
                     [ Gr.insEdge (n1, n2, ())
                     | n1 ← pre
                     , n2 ← suc ]
      --
      -- Remove redundant edges:
      --  • Edges implied by transitivity
      --  • Edges relating type constructors to type constructors
      removeRedundant = do
        NM.modifyGraph Gr.untransitive
        edges ← NM.getsGraph Gr.labNodeEdges
        NM.delMapEdgesM [ (ConAt c1, ConAt c2)
                        | (ConAt c1, ConAt c2) ← edges ]
      --
      -- Remove type variables based on polarity-related rules:
      --  • Coalesce positive type variables with a single predecessor
      --    and negative type variables with a single successor
      --  • Coalesce positive type variables that share all their
      --    predecessors and negative type variables that share all
      --    their successors.
      polarizedReduce = iterChanging $ \τftv → do
        nm ← NM.getNodeMap
        foldM tryRemove τftv (findPolar nm τftv)
          where
          tryRemove τftv (n, α, var) = do
            let ln = (n, VarAt α)
            mτ ← readTV α
            g  ← NM.getGraph
            case (mτ, Gr.gelem n g) of
              (Left _, True) →
                case (var, Gr.pre g n, Gr.suc g n) of
                  -- Should we consider QCo(ntra)variance here too?
                  (Covariant,     [pre], _)
                    → snd <$> coalesce ln (Gr.labelNode g pre) τftv
                  (Contravariant, _,     [suc])
                    → snd <$> coalesce ln (Gr.labelNode g suc) τftv
                  (Covariant,     pres,  _)
                    → siblings g τftv (ln,  1) pres (Gr.pre,Gr.suc)
                  (Contravariant, _,     sucs)
                    → siblings g τftv (ln, -1) sucs (Gr.suc,Gr.pre)
                  _ → return τftv
              _ → return τftv
          findPolar nm τftv = [ (Gr.nmLab nm (VarAt α), α, var)
                              | (α, var) ← Map.toList τftv
                              , var == 1 || var == -1 ]
          siblings g τftv (lnode@(n,_), var) pres (gpre, gsuc) = do
            lnodes ← liftM ordNub . runListT $ do
              pre ← ListT (return pres)
              sib ← ListT (return (gsuc g pre))
              guard $ sib /= n
              Just (VarAt β) ← return (Gr.lab g sib)
              guard $ Map.lookup β τftv == Just var
              guard $ gpre g sib == pres
              return (sib, VarAt β)
            case lnodes of
              _:_ → do
                  τftv' ← snd <$> coalesceList τftv (lnode:lnodes)
                  return τftv'
              _   → return τftv
      --
      -- Coalesce the strongly-connected components to single atoms
      coalesceSCCs τftv = do
        foldM (liftM snd <$$> coalesceList) τftv =<< NM.getsGraph Gr.labScc 
      -- Given a list of atoms, coalesce them to one atom
      coalesceList τftv0 (ln:lns) =
        foldM (\(ln1, state) ln2 → coalesce ln1 ln2 state) (ln, τftv0) lns
      coalesceList _      [] = fail "BUG! coalesceList got []"
      -- Assign n2 to n1, updating the graph, type variables, and ftvs,
      -- and return whichever node survives
      coalesce (n1, lab1) (n2, lab2) τftv = do
        case (lab1, lab2) of
          (VarAt α,  _)        → (n1, α) `gets` (n2, lab2)
          (_,        VarAt α)  → (n2, α) `gets` (n1, lab1)
          (ConAt c1, ConAt c2)
            | c1 == c2         → do
            assignNode n1 n2
            return ((n2, lab2), τftv)
          _                    →
            fail $ "Could not unify: " ++ show lab1 ++ " = " ++ show lab2
        where
          (n1', α) `gets` (n2', lab') = do
            let ?deref = readTV
            ftv2 ← ftvSet lab'
            if α `Set.member` ftv2
              then return ((n2', lab'), τftv)
              else do
                τftv' ← assignTV α lab' τftv
                assignNode n1' n2'
                return ((n2', lab'), τftv')
      -- Update the graph to remove node n1, assigning all of its
      -- neighbors to n2
      assignNode n1 n2 = NM.modifyGraph $ \g →
        Gr.insEdges [ (n', n2, ())
                    | n' ← Gr.pre g n1, n' /= n1, n' /= n2 ] $
        Gr.insEdges [ (n2, n', ())
                    | n' ← Gr.suc g n1, n' /= n1, n' /= n2 ] $
        Gr.delNode n1 g
      -- Update the type variables to assign atom2 to α1, updating the
      -- ftvs appropriately
      assignTV α atom τftv = do
        deleteTVProxy α
        writeTV α (atomTy atom)
        assignFtvMap α atom τftv
      -- Given two type variables, where α ← atom, update a map of free
      -- type variables to variance lists accordingly
      assignFtvMap α atom vmap =
        case Map.lookup α vmap of
          Just vs → case atom of
            VarAt β → return $ Map.insertWith (+) β vs vmap'
            ConAt _ → return vmap'
          Nothing → return vmap
        where vmap' = Map.delete α vmap
      -- Coalesce and remove fully-generalizable components
      coalesceComponents value (γrank, τftv) = do
        extvs  ← getExistentials (γrank, τftv)
        τcands ← genCandidates value τftv γrank
        let candidates = Set.mapMonotonic VarAt $ extvs `Set.union` τcands
            each τftv component@(_:_)
              | all (`Set.member` candidates) (map snd component)
              = do
                  ((node, _), τftv')
                    ← coalesceList τftv component
                  NM.getGraph >>= NM.putGraph . Gr.delNode node
                  return τftv'
            each τftv _
              = return τftv
        foldM each τftv =<< NM.getsGraph Gr.labComponents
      -- Find the generalization candidates, which are free in τ but
      -- not in γ (restricted further if not a value)
      genCandidates value τftv γrank =
        Set.fromDistinctAscList <$>
          removeByRank γrank (map fst (Map.toAscList (restrict τftv)))
          where
          restrict = if value
                       then id
                       else Map.filter (`elem` [1, -1, 2, -2])
      -- Remove type variables from a list if their rank indicates that
      -- they're in the environment
      removeByRank γrank = filterM keep
        where
          keep α = do
            rank ← getTVRank α
            return (rank > γrank)
  --
  saveConstraint = do
    c ← EagerConstraintT get
    return (EagerConstraintT (put c))
  showConstraint = show <$> EagerConstraintT get

type SeenT tv r m = StateT (Map.Map (REC_TYPE tv, REC_TYPE tv) Bool)
                           (EagerConstraintT tv r m)

runSeenT ∷ MonadU tv r m ⇒ SeenT tv r m a → EagerConstraintT tv r m a
runSeenT m = do
  gtrace "runSeenT {"
  result ← evalStateT m Map.empty
  gtrace "} runSeenT"
  return result

compareTypesK ∷ MonadU tv r m ⇒
                Variance → Int → Type tv → Type tv → SeenT tv r m ()
compareTypesK var = case var of
  Invariant     → unifyTypesK
  Covariant     → subtypeTypesK
  Contravariant → flip . subtypeTypesK
  QInvariant    → \_ τ1 τ2 → τ1 ⊏: τ2 >> τ2 ⊏: τ1
  QCovariant    → \_ τ1 τ2 → τ1 ⊏: τ2
  QContravariant→ \_ τ1 τ2 → τ2 ⊏: τ1
  Omnivariant   → \_ _ _   → return ()

subtypeTypesK ∷ MonadU tv r m ⇒ Int → Type tv → Type tv → SeenT tv r m ()
subtypeTypesK k0 τ10 τ20 = do
  lift $ gtrace ("subtypeTypesK", k0, τ10, τ20)
  check k0 τ10 τ20
  where
  check k τ1 τ2 = do
    τ1'  ← derefAll τ1
    τ2'  ← derefAll τ2
    seen ← get
    if Map.member (REC_TYPE τ1', REC_TYPE τ2') seen
      then return ()
      else do
        put (Map.insert (REC_TYPE τ1', REC_TYPE τ2') False seen)
        decomp k τ1' τ2'
  add a1 a2 = do
    NM.insNewMapNodeM a1
    NM.insNewMapNodeM a2
    NM.insMapEdgeM (a1, a2, ())
  decomp k τ1 τ2 = case (τ1, τ2) of
    (VarTy v1, VarTy v2)
      | v1 == v2 → return ()
    (VarTy (FreeVar r1), VarTy (FreeVar r2)) → do
      lift (makeEquivTVs r1 r2)
      add (VarAt r1) (VarAt r2)
    (VarTy (FreeVar r1), ConTy c2 []) →
      add (VarAt r1) (ConAt c2)
    (ConTy c1 [], VarTy (FreeVar r2)) →
      add (ConAt c1) (VarAt r2)
    (VarTy (FreeVar r1), _) → do
      lift (sizeCheck r1 τ2)
      τ2' ← copyType τ2
      unifyVarK k r1 τ2'
      subtypeTypesK k τ2' τ2
    (_, VarTy (FreeVar r2)) → do
      lift (sizeCheck r2 τ1)
      τ1' ← copyType τ1
      unifyVarK k r2 τ1'
      subtypeTypesK k τ1 τ1'
    (QuaTy q1 αs1 τ1', QuaTy q2 αs2 τ2')
      | q1 == q2 && αs1 == αs2 → check (k + 1) τ1' τ2'
    (ConTy c1 [], ConTy c2 [])
      | c1 `tyConLe` c2 → return ()
    (ConTy c1 τs1, ConTy c2 τs2)
      | c1 == c2 && length τs1 == length τs2 →
      sequence_
        [ compareTypesK var k τ1' τ2'
        | var ← getVariances c1 (length τs1)
        | τ1' ← τs1
        | τ2' ← τs2 ]
    (RowTy n1 τ11 τ12, RowTy n2 τ21 τ22)
      | n1 == n2
                    → check k τ11 τ21
                   >> check k τ12 τ22
      | otherwise   → do
        α ← newTVTy
        check k (RowTy n1 τ11 α) τ22
        β ← newTVTy
        check k τ12 (RowTy n2 τ21 β)
        check k α β
    (RecTy _ τ1', _)
                    → decomp k (openTy 0 [τ1] τ1') τ2
    (_, RecTy _ τ2')
                    → decomp k τ1 (openTy 0 [τ2] τ2')
    _               → fail $ "cannot subtype " ++ show τ1 ++ " and " ++ show τ2

unifyTypesK    ∷ MonadU tv r m ⇒ Int → Type tv → Type tv → SeenT tv r m ()
unifyTypesK k0 τ10 τ20 = do
  lift $ gtrace ("unifyTypesK", k0, τ10, τ20)
  check k0 τ10 τ20
  where
  check k τ1 τ2 = do
    τ1'  ← derefAll τ1
    τ2'  ← derefAll τ2
    seen ← get
    case Map.lookup (REC_TYPE τ1', REC_TYPE τ2') seen of
      Just True → return ()
      _         → do
        put (Map.insert (REC_TYPE τ1', REC_TYPE τ2') True seen)
        decomp k τ1' τ2'
  decomp k τ1 τ2 = case (τ1, τ2) of
    (VarTy v1, VarTy v2)
      | v1 == v2    → return ()
    (VarTy (FreeVar r1), _)
                    → unifyVarK k r1 τ2
    (_, VarTy (FreeVar r2))
                    → unifyVarK k r2 τ1
    (QuaTy q1 αs1 τ1', QuaTy q2 αs2 τ2')
      | q1 == q2 && αs1 == αs2
                    → check (k + 1) τ1' τ2'
    (ConTy c1 τs1, ConTy c2 τs2)
      | c1 == c2 && length τs1 == length τs2
                    → sequence_
                        [ if isQVariance var
                            then τ1' ⊏: τ2'
                            else check k τ1' τ2'
                        | τ1' ← τs1
                        | τ2' ← τs2
                        | var ← getVariances c1 (length τs1) ]
    (RowTy n1 τ11 τ12, RowTy n2 τ21 τ22)
      | n1 == n2    → check k τ11 τ21
                   >> check k τ12 τ22
      | otherwise   → do
        α ← newTVTy
        check k (RowTy n1 τ11 α) τ22
        check k τ12 (RowTy n2 τ21 α)
    (RecTy _ τ1', _)
                    → decomp k (openTy 0 [τ1] τ1') τ2
    (_, RecTy _ τ2')
                    → decomp k τ1 (openTy 0 [τ2] τ2')
    _               → fail $ "cannot unify " ++ show τ1 ++ " and " ++ show τ2

-- | Unify a type variable with a type, where the type must have
--   no bound variables pointing further than @k@.
--   ASSUMPTION: @α@ has not been substituted.
unifyVarK ∷ MonadU tv r m ⇒ Int → tv → Type tv → SeenT tv r m ()
unifyVarK k α τ0 = do
  lift $ gtrace ("unifyVarK", k, α, τ0)
  let ?deref = readTV
  τ ← derefAll τ0
  unless (lcTy k τ) $
    fail "cannot unify because insufficiently polymorphic"
  αs ← ftvSet τ
  when (α `Set.member` αs) $
    fail "occurs check failed"
  lift (deleteTVProxy α)
  writeTV α τ
  (n, _) ← NM.mkNodeM (VarAt α)
  gr     ← NM.getGraph
  case Gr.match n gr of
    (Nothing,                 _)   → return ()
    (Just (pres, _, _, sucs), gr') → do
      NM.putGraph gr'
      sequence_ $
        [ case Gr.lab gr' n' of
            Nothing → return ()
            Just a  → subtypeTypesK k (atomTy a) τ
        | (_, n') ← pres ]
        ++
        [ case Gr.lab gr' n' of
            Nothing → return ()
            Just a  → subtypeTypesK k τ (atomTy a)
        | (_, n') ← sucs ]

sizeCheck ∷ MonadU tv r m ⇒ tv → Type tv → EagerConstraintT tv r m ()
sizeCheck α τ = do
  gtrace ("sizeCheck", α, τ)
  let ?deref = readTV
  βs ← Set.toList <$> ftvSet τ
  bs ← mapM (checkEquivTVs α) βs
  when (any id bs) $
    fail "Occurs check failed (size check)"

makeEquivTVs  ∷ MonadU tv r m ⇒ tv → tv → EagerConstraintT tv r m ()
makeEquivTVs α β = do
  pα ← getTVProxy α
  pβ ← getTVProxy β
  UF.coalesce_ (return <$$> Set.union) pα pβ

checkEquivTVs ∷ MonadU tv r m ⇒ tv → tv → EagerConstraintT tv r m Bool
checkEquivTVs α β = do
  pα ← getTVProxy α
  pβ ← getTVProxy β
  UF.sameRepr pα pβ

deleteTVProxy ∷ MonadU tv r m ⇒ tv → EagerConstraintT tv r m ()
deleteTVProxy α = do
  equivs ← EagerConstraintT (gets esEquivs)
  case Map.lookup α equivs of
    Just pα → do
      set ← UF.desc pα
      UF.setDesc pα (Set.delete α set)
      EagerConstraintT (modify (esEquivsUpdate (Map.delete α)))
    Nothing → return ()

getTVProxy ∷ MonadU tv r m ⇒ tv → EagerConstraintT tv r m (TVProxy tv r)
getTVProxy α = do
  equivs ← EagerConstraintT (gets esEquivs)
  case Map.lookup α equivs of
    Just pα → return pα
    Nothing → do
      pα ← UF.create (Set.singleton α)
      EagerConstraintT (modify (esEquivsUpdate (Map.insert α pα)))
      return pα

-- | Copy a type while replacing all the type variables with fresh ones
--   of the same kind.
copyType ∷ MonadU tv r m ⇒ Type tv → m (Type tv)
copyType =
  let ?deref = readTV
   in foldTypeM (mkQuaF (return <$$$> QuaTy))
                (mkBvF (return <$$$> bvTy))
                (fvTy <$$> newTVKind . tvKind)
                fcon
                (return <$$$> RowTy)
                (mkRecF (return <$$> RecTy))
  where
    fcon c []
      | tyConHasSuccs c || tyConHasPreds c
      = newTVTy
    fcon c τs
      = ConTy c <$> sequence
          [ if isQVariance var
              then fvTy <$> newTVKind QualKd
              else return τ
          | τ   ← τs
          | var ← getVariances c (length τs) ]

gtrace ∷ (MonadU tv r m, Show a) ⇒ a → EagerConstraintT tv r m ()
gtrace =
  if debug
    then \info → do
      es ← EagerConstraintT get
      trace (info, es)
    else \_ → return ()

---
--- Abstract constraints
---

class (Ftv c tv, Monoid c) ⇒ Constraint c tv | c → tv where
  -- | The trivial constraint
  (⊤)        ∷ c
  (⊤)        = mempty
  -- | A conjunction of constraints
  (⋀)        ∷ c → c → c
  (⋀)        = mappend
  -- | A subtype constraint
  (≤), (≥), (≤≥) ∷ Type tv → Type tv → c
  τ1 ≥ τ2        = τ2 ≤ τ1
  τ1 ≤≥ τ2       = τ1 ≤ τ2 ⋀ τ2 ≤ τ1
  -- | A subtype constraint in the given variance
  relate     ∷ Variance → Type tv → Type tv → c
  relate v τ τ' = case v of
    Covariant      → τ ≤ τ'
    Contravariant  → τ ≥ τ'
    Invariant      → τ ≤≥ τ'
    QCovariant     → τ ⊏ τ'
    QContravariant → τ' ⊏ τ
    QInvariant     → τ ⊏ τ' ⋀ τ' ⊏ τ
    Omnivariant    → (⊤)
  -- | A qualifier subsumption constraint
  (⊏)        ∷ (Qualifier q1 tv, Qualifier q2 tv) ⇒ q1 → q2 → c
  --
  -- | Figure out which variables to generalize in a piece of syntax
  gen'       ∷ MonadU tv r m ⇒
               Bool → c → Rank → Type tv → m ([tv], [QLit], c)
  -- | Generalize a type under a constraint and environment,
  --   given whether the the value restriction is satisfied or not
  gen        ∷ MonadU tv r m ⇒
               Bool → c → Rank → Type tv → m (Type tv, c)
  gen value c0 γrank τ = do
    (αs, qls, c) ← gen' value c0 γrank τ
    σ ← standardizeMus =<< closeWithQuals qls AllQu αs <$> derefAll τ
    return (σ, c)
  -- | Generalize a list of types together.
  genList    ∷ MonadU tv r m ⇒
               Bool → c → Rank → [Type tv] → m ([Type tv], c)
  genList value c0 γrank τs = do
    (αs, qls, c) ← gen' value c0 γrank (tupleTy τs)
    σs ← mapM (standardizeMus <=< closeWithQuals qls AllQu αs <$$> derefAll) τs
    return (σs, c)

infixr 4 ⋀
infix  5 ≤, ≥, ≤≥, ⊏

-- | We reduce constraints to inequalities on atoms, which are either
--   type variables or nullary type constructors.
data Atom tv = VarAt !tv
             | ConAt !Name
  deriving (Eq, Ord)

instance Tv tv ⇒ Show (Atom tv) where
  show (VarAt α) = show (tvUniqueID α)
  show (ConAt c) = c

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
(tyConNode, tyConOrder) = (Gr.nmLab nm, Gr.trcnr g)
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

-- | Are there any type constructors greater or lesser than
--   this one?
tyConHasSuccs, tyConHasPreds ∷ Name → Bool
tyConHasSuccs c = Gr.gelem n tyConOrder && Gr.outdeg tyConOrder n > 0
  where n = tyConNode c
tyConHasPreds c = Gr.gelem n tyConOrder && Gr.indeg tyConOrder n > 0
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
                  | n ← next' n1 `List.intersect` next' n2 ]
     in case reverse (List.sort common) of
          [(_,Just c)]               → return c
          (j,Just c):(k,_):_ | j > k → return c
          _                          → giveUp
  | otherwise              = giveUp
  where next' n = n : next n
        giveUp = fail $
          "Type constructors " ++ c1 ++ " and " ++ c2 ++
          " have no " ++ goalName ++ "."

---
--- An implementation of constraints
---

-- | Simple subtype constraints relate pairs of types:
data SubtypeConstraint r
  = SC {
      scTypes ∷ [(Type r, Type r)],
      scQuals ∷ [(Type r, Type r)]
    }

instance Ppr r ⇒ Show (SubtypeConstraint r) where
  showsPrec _ sc = case sc of
    SC [] [] → id
    SC ts [] → brak $ showsTypes ts
    SC [] qs → brak $ showsQuals qs
    SC ts qs → brak $ showsTypes ts . showString "; " . showsQuals qs
    where
      brak s         = showChar '[' . s . showChar ']'
      showsTypes     = showsIneqs " <: "
      showsQuals     = showsIneqs " ⊑ "
      showsIneqs cmp = foldr (.) id
                     . List.intersperse (showString ", ")
                     . map (\(x,y) → shows x . showString cmp . shows y)

instance Monoid (SubtypeConstraint r) where
  mempty      = SC [] []
  mconcat scs = SC (concatMap scTypes scs) (concatMap scQuals scs)
  mappend c d = mconcat [c, d]

instance Ord r ⇒ Ftv (SubtypeConstraint r) r where
  ftvTree sc = do
    let (lowers, uppers) = unzip (scTypes sc)
    ftvLowers ← ftvTree lowers
    ftvUppers ← ftvTree uppers
    return (FTBranch [ftvLowers, FTVariance negate ftvUppers])

{-
type CState r = (Gr (Atom r) (), Set.Set r, Map.Map r [Variance])
type LN r = Gr.LNode (Atom r)
-}

instance Tv r ⇒ Constraint (SubtypeConstraint r) r where
  τ  ≤ τ' = SC [(τ, τ')] []
  q  ⊏ q' = SC [] [(toQualifierType q, toQualifierType q')]
  --
  -- Generalization proceeds in several steps:
  --
  --  1. skeletonize: sort type variables into equivalence classes of
  --     related type variables, each potentially associated with a
  --     shape, which is a type constructor applied to equivalence
  --     classes.
  --
  --  2. occursCheck: check for cycles (which are inconsistent in a
  --     finite model) by building a containment order on skeletons
  --     and looking for cycles in the graph representating the order.
  --
  --  3. expand: ensure that all related type variables in each skeleton
  --     are expanded to the same shape.
  --
  --  4. decompose: subtype-unify all subtype constraints until we have
  --     constraints only on atoms (type variables and nullary type
  --     constructors).
  --
  --  5. buildGraph: build a graph representing the subtype constraints
  --     on atoms, and add in all of the known subtype order as well.
  --     Leave out irrelevant contraints: upper bounds on covariant
  --     variables and lower bounds on contravariant.
  --
  --  6. scc: each strongly-connected component is coalesced into a
  --     single atom.  (If an scc contains two different nullary type
  --     constructors, this is a type error.)
  --     POSTCONDITION: the graph is acyclic.
  --
  --  7. tycons: construct the transitive closure of the graph and check
  --     for inconsistencies or inferences implied by the nullary type
  --     constructors present.  Type error if two type constructors are
  --     related wrongly.  For type variables related to multiple type
  --     constructors, we may be able to tighten the bounds and
  --     potentially unify the variable with a bound.
  --     POSTCONDITION: the graph is transitive and satisfiable
  --
  --  8. existentials: most type variables that appear in the constraint
  --     but not the type nor context can be existentially quantified in
  --     the constraint; the exception is type variables that may
  --     provide the only associating between multiple predecessors (or
  --     successors) because they have no successor (or predecessor).
  --     PRECONDITION: the graph is transitive and acyclic
  --
  --  9. removeRedundant: remove redundant edges that are implied by
  --     transitivity or the subtyping relation.
  --     PRECONDITION: the graph is transitive
  --     POSTCONDITION: the graph is non-transitive
  --
  -- (repeat existentials step)
  --
  -- 10. polarized:
  --      - positive type variables with exactly one
  --        lower bound (in degree 1) are unified with their lower bound
  --      - dually, for negative of out degree 1
  --      - pairs of positive (dually negative) type variables that share
  --        all predecessors (successors) are coalesced
  --
  -- (repeat existentials step)
  --
  -- 11. components: coalesce and remove any components that consist only
  --     of generalization candidates:
  --      - if we're dealing with a value, ftv τ \ ftv γ
  --      - otherwise, limit the above those that appear only positively
  --        or only negatively in τ
  --
  -- 12. reconstruct: turn the graph back into a constraint
  --
  -- 13. generalize: candidates that are not free in the constraint
  gen' value (SC c qc) γrank τ = do
    let ?deref = readTV
    trace ("gen (begin)", SC c qc, γrank, τ)
    c            ← unrollRecs c
    trace ("gen (unrollRecs)", c)
    skm1         ← skeletonize c
    trace ("gen (skeletonized)", skm1, (c, qc), τ)
    (expandSks, skipSks)
                 ← occursCheck skm1
    (_, noX)     ← expand skm1 expandSks skipSks
    trace ("gen (expand)", noX, (c, qc), τ)
    (c, qc)      ← decompose noX (c, qc)
    τftv         ← ftvV τ
    trace ("gen (decompose)", (c, qc), τftv, τ)
    let (nm, g) = buildGraph (Set.toList c) τftv
    trace ("gen (buildGraph)", Gr.ShowGraph g, τftv, τ)
    (g, τftv)   ← coalesceSCCs (g, τftv)
    trace ("gen (scc)", Gr.ShowGraph g, τftv, τ)
    (g, τftv)   ← satisfyTycons nm (g, τftv)
    trace ("gen (tycons)", Gr.ShowGraph g, τftv, τ)
    g            ← eliminateExistentials True nm (g, γrank, τftv)
    trace ("gen (existentials 1)", Gr.ShowGraph g, τftv, τ)
    g            ← return (removeRedundant nm g)
    trace ("gen (redundant)", Gr.ShowGraph g, τftv, τ)
    g            ← eliminateExistentials False nm (g, γrank, τftv)
    trace ("gen (existentials 2)", Gr.ShowGraph g, τftv, τ)
    (g, τftv)    ← polarizedReduce nm (g, τftv)
    trace ("gen (polarized)", Gr.ShowGraph g, τftv, τ)
    g            ← eliminateExistentials False nm (g, γrank, τftv)
    trace ("gen (existentials 3)", Gr.ShowGraph g, τftv, τ)
    -- Guessing starts here
    (g, τftv)    ← coalesceComponents value (g, γrank, τftv)
    trace ("gen (components)", Gr.ShowGraph g, τftv, τ)
    -- Guessing ends here
    cftv         ← ftvSet (map snd (Gr.labNodes g))
    qcftv        ← ftvSet qc
    αs           ← Set.fromDistinctAscList <$$>
                     removeByRank γrank <$>
                       Set.toAscList $
                         (qcftv `Set.union` Map.keysSet τftv) Set.\\ cftv
    (qc, αqs, τ) ← solveQualifiers value αs qc τ
    let c        = reconstruct g qc
    trace ("gen (finished)", αqs, τ, c)
    return (map fst αqs, map snd αqs, c)
    where
      unrollRecs = execWriterT . mapM_ unrollIneq where
        unrollIneq (τ1, τ2) = do
          τ1' ← unroll τ1
          τ2' ← unroll τ2
          tell [(τ1', τ2')]
        unroll τ0 = case τ0 of
          QuaTy q ns τ           → QuaTy q ns <$> unroll τ
          VarTy (FreeVar r)      → either (return . fvTy) unroll =<< readTV r
          VarTy (BoundVar i j n) → return (bvTy i j n)
          ConTy c τs             → ConTy c <$> mapM unroll τs
          RowTy n τ1 τ2          → RowTy n <$> unroll τ1 <*> unroll τ2
          RecTy _ τ1             → do
            β ← newTVTy
            let τ1' = openTy 0 [β] τ1
            tell [(β, τ1'), (τ1', β)]
            return β
      -- decompose takes a list of subtype constraint pairs and a list
      -- of type variables, and returns when all of the constraint is
      -- reduced to pairs of atoms.
      decompose recTVs (c, qc) = do
        initT <$$> doRWST $ do
          tell (Set.empty, qc, [])
          loop c
        where
        doRWST m = snd <$> execRWST m () Set.empty
        a1 ≤! a2 = tell (Set.singleton (a1, a2), [], [])
        τ1 ⊏! τ2 = tell (Set.empty, [(τ1, τ2)], [])
        τ1 ≤* τ2 = tell (Set.empty, [], [(τ1, τ2)])
        loop c' = do
          again ← lastT . snd <$> listen (mapM_ decompLe c')
          if null again
            then return ()
            else loop again
        unexpanded α =
          fail $ "BUG! gen (decompose) saw unexpanded tv: " ++ show α
        substRec α τ = do
          let ?deref = readTV
          βs ← lift (ftvSet τ)
          let τ' = if α `Set.member` βs
                then RecTy Nope (closeTy 0 [α] τ)
                else τ
          writeTV α τ'
        checkLe (τ1, τ2) k = do
          τ1'  ← derefAll τ1
          τ2'  ← derefAll τ2
          seen ← get
          unless ((τ1', τ2') `Set.member` seen) $
            case (τ1', τ2') of
              (VarTy (FreeVar α), VarTy (FreeVar _))
                | α `Set.member` recTVs
                → τ1' ≤* τ2'
              _ → do
                put (Set.insert (τ1', τ2') seen)
                k (τ1', τ2')
        decompLe (τ10, τ20) = checkLe (τ10, τ20) $ \(τ1, τ2) →
          trace ("decompLe", τ1, τ2) >>
          case (τ1, τ2) of
            (VarTy (BoundVar _ _ _), VarTy (BoundVar _ _ _))
              | τ1 == τ2
              → return ()
            (VarTy (FreeVar α), VarTy (FreeVar β))
              | α == β
              → return ()
              | otherwise
              → VarAt α ≤! VarAt β
            (VarTy (FreeVar α), _)
              | α `Set.member` recTVs
              → substRec α τ2
            (_,                 VarTy (FreeVar β))
              | β `Set.member` recTVs
              → substRec β τ1
            (ConTy c1 [],       ConTy c2 [])
              | c1 `tyConLe` c2
              → return ()
            (VarTy (FreeVar α), ConTy c2 [])
              → VarAt α ≤! ConAt c2
            (ConTy c1 [],       VarTy (FreeVar β))
              → ConAt c1 ≤! VarAt β
            (ConTy c1 τs1,      ConTy c2 τs2)
              | c1 == c2
              → sequence_
                  [ case var of
                      Covariant      → decompLe (τ1', τ2')
                      Contravariant  → decompLe (τ2', τ1')
                      Invariant      → decompLe (τ1', τ2') >>
                                       decompLe (τ2', τ1')
                      QCovariant     → τ1' ⊏! τ2'
                      QContravariant → τ2' ⊏! τ1'
                      QInvariant     → τ1' ⊏! τ2' >>
                                       τ2' ⊏! τ1'
                      Omnivariant    → return ()
                  | τ1' ← τs1
                  | τ2' ← τs2
                  | var ← getVariances c1 (length τs1) ]
              | otherwise
              → fail $
                  "Could not unify type constructors: " ++ c1 ++ " ≤ " ++ c2
            (τ1@(RowTy _ _ _),    τ2@(RowTy _ _ _)) → do
              τ1' ← derefAll τ1
              τ2' ← derefAll τ2
              let r@(matches, (extra1, rest1), (extra2, rest2))
                    = matchLabels τ1' τ2'
              trace ("decomp row", τ1, τ2, r)
              unless (null extra1 && null extra2) $ fail "EXTRA!"
              sequence
                [ decompLe (τ1i, τ2i)
                | ((_, τ1i), (_, τ2i)) ← matches ]
              decompLe (rest1, rest2)
            (RecTy _ τ1',       _)
              → decompLe (openTy 0 [τ1] τ1', τ2)
            (_,           RecTy _ τ2')
              → decompLe (τ1, openTy 0 [τ2] τ2')
            (VarTy (FreeVar α), ConTy _ _)          → unexpanded α
            (ConTy _ _,         VarTy (FreeVar β))  → unexpanded β
            (VarTy (FreeVar α), RowTy _ _ _)        → unexpanded α
            (RowTy _ _ _,       VarTy (FreeVar β))  → unexpanded β
            _ → fail $ "Could not unify: " ++ show τ1 ++ " ≤ " ++ show τ2
      --
      -- Given a list of pairs, build the graph
      buildGraph pairs τftv =
        snd . NM.run (Gr.empty ∷ Gr (Atom r) ()) $ do
          let varianceOf (VarAt α) = Map.lookup α τftv
              varianceOf (ConAt _) = Nothing
          NM.insMapNodesM (map fst pairs)
          NM.insMapNodesM (map snd pairs)
          NM.insMapNodesM (map (ConAt . snd) (Gr.labNodes tyConOrder))
          NM.insMapEdgesM [ (α, α', ())
                          | (α, α') ← pairs
                          , α /= α'
                          , not (varianceOf α == Just Covariant &&
                                 varianceOf α' == Just Contravariant)
                          ]
          NM.insMapEdgesM [ (ConAt c1, ConAt c2, ())
                          | (c1, c2) ← Gr.labNodeEdges tyConOrder]
          return ()
      --
      -- Make sure the graph is satisfiable and figure out anything that
      -- is implied by the transitive closure of type constructors
      satisfyTycons nm (g0, τftv0) =
        satisfyTycons' (Gr.trcnr g0, τftv0)
        where
        satisfyTycons' = iterChanging $ \(g, τftv) →
          foldM each (g, τftv) (Gr.labNodes g)
        each (g, τftv) (n, VarAt α) = do
          let assign c = do
                τftv ← assignTV α (ConAt c) τftv
                let n' = Gr.nmLab nm (ConAt c)
                return (assignNode n n' g, τftv)
              lbs = [ c | Just (ConAt c) ← map (Gr.lab g) (Gr.pre g n)]
              ubs = [ c | Just (ConAt c) ← map (Gr.lab g) (Gr.suc g n)]
          glb ← case lbs of
                  []   → return Nothing
                  c:cs → Just <$> foldM tyConJoin c cs
          lub ← case ubs of
                  []   → return Nothing
                  c:cs → Just <$> foldM tyConMeet c cs
          case (glb, lub) of
            (Just c1, Just c2) | c1 == c2         → assign c1
            (Just c1, _) | not (tyConHasSuccs c1) → assign c1
            (_, Just c2) | not (tyConHasPreds c2) → assign c2
            _ → do
              g ← NM.execNodeMapT nm g $ do
                case glb of
                  Just lb | lb `notElem` lbs
                    → NM.insMapEdgeM (ConAt lb, VarAt α, ())
                  _ → return ()
                case lub of
                  Just ub | ub `notElem` ubs
                    → NM.insMapEdgeM (VarAt α, ConAt ub, ())
                  _ → return ()
              return (g, τftv)
        each (g, τftv) (n, ConAt c1) = do
          g ← NM.execNodeMapT nm g $ sequence_
            [ if c1 `tyConLe` c2
                then return ()
                else fail $ "Cannot unify: " ++ c1 ++ " ≤ " ++ c2
            | Just (ConAt c2) ← map (Gr.lab g) (Gr.suc g n)]
          return (g, τftv)
      --
      -- Eliminate existentially-quantified type variables from the
      -- constraint
      eliminateExistentials trans nm (g, γrank, τftv) = do
        extvs ← getExistentials (g, γrank, τftv)
        trace ("existentials are:", extvs)
        return (Set.fold (eliminateNode trans nm) g extvs)
      -- Get the existential type variables
      getExistentials (g, γrank, τftv) = do
        cftv ← removeByRank γrank [ α | (_, VarAt α) ← Gr.labNodes g ]
        return (Set.fromList cftv Set.\\ Map.keysSet τftv)
      -- Remove a node unless it is necessary to associate some of its
      -- neighbors -- in particular, a node with multiple predecessors
      -- but no successor (or dually, multiple successors but no
      -- predecessor) should not be removed.
      eliminateNode trans nm α g = do
        case (Gr.pre g node, Gr.suc g node) of
          (_:_:_, []) → g
          ([], _:_:_) → g
          (pre, suc)  →
            let g' = Gr.delNode node g in
            if trans
              then g'
              else foldr ($) g'
                     [ Gr.insEdge (n1, n2, ())
                     | n1 ← pre
                     , n2 ← suc ]
        where node = Gr.nmLab nm (VarAt α)
      --
      -- Remove redundant edges:
      --  • Edges implied by transitivity
      --  • Edges relating type constructors to type constructors
      removeRedundant nm g = NM.delMapEdges nm conEdges g'
        where g'       = Gr.untransitive g
              conEdges = [ (ConAt c1, ConAt c2)
                         | (ConAt c1, ConAt c2) ← Gr.labNodeEdges g' ]
      --
      -- Remove type variables based on polarity-related rules:
      --  • Coalesce positive type variables with a single predecessor
      --    and negative type variables with a single successor
      --  • Coalesce positive type variables that share all their
      --    predecessors and negative type variables that share all
      --    their successors.
      polarizedReduce nm = iterChanging $ \state → do
        foldM tryRemove state (findPolar (snd state))
          where
          tryRemove state@(g,_) (n, α, var) = do
            let ln = (n, VarAt α)
            mτ ← readTV α
            case (mτ, Gr.gelem n g) of
              (Left _, True) →
                case (var, Gr.pre g n, Gr.suc g n) of
                  -- Should we consider QCo(ntra)variance here too?
                  (Covariant,     [pre], _)
                    → snd <$> coalesce ln (Gr.labelNode g pre) state
                  (Contravariant, _,     [suc])
                    → snd <$> coalesce ln (Gr.labelNode g suc) state
                  (Covariant,     pres,  _)
                    → siblings state (ln,  1) pres (Gr.pre,Gr.suc)
                  (Contravariant, _,     sucs)
                    → siblings state (ln, -1) sucs (Gr.suc,Gr.pre)
                  _ → return state
              _ → return state
          findPolar τftv = [ (Gr.nmLab nm (VarAt α), α, var)
                           | (α, var) ← Map.toList τftv
                           , var == 1 || var == -1 ]
          siblings state@(g,τftv) (lnode@(n,_), var)
                   pres (gpre, gsuc) = do
            lnodes ← liftM ordNub . runListT $ do
              pre ← ListT (return pres)
              sib ← ListT (return (gsuc g pre))
              guard $ sib /= n
              Just (VarAt β) ← return (Gr.lab g sib)
              guard $ Map.lookup β τftv == Just var
              guard $ gpre g sib == pres
              return (sib, VarAt β)
            case lnodes of
              _:_ → do
                  state' ← snd <$> coalesceList state (lnode:lnodes)
                  return state'
              _   → return state
      --
      -- Coalesce the strongly-connected components to single atoms
      coalesceSCCs state =
        foldM (liftM snd <$$> coalesceList) state (Gr.labScc (prj1 state))
      -- Given a list of atoms, coalesce them to one atom
      coalesceList state0 (ln:lns) =
        foldM (\(ln1, state) ln2 → coalesce ln1 ln2 state) (ln, state0) lns
      coalesceList _      [] = fail "BUG! coalesceList got []"
      -- Assign n2 to n1, updating the graph, type variables, and ftvs,
      -- and return whichever node survives
      coalesce (n1, lab1) (n2, lab2) (g, τftv) = do
        case (lab1, lab2) of
          (VarAt α,  _)        → (n1, α) `gets` (n2, lab2)
          (_,        VarAt α)  → (n2, α) `gets` (n1, lab1)
          (ConAt c1, ConAt c2)
            | c1 == c2         →
            return ((n2, lab2), (assignNode n1 n2 g, τftv))
          _                    →
            fail $ "Could not unify: " ++ show lab1 ++ " = " ++ show lab2
        where
          (n1', α) `gets` (n2', lab') = do
            let ?deref = readTV
            ftv2 ← ftvSet lab'
            if α `Set.member` ftv2
              then return ((n2', lab'), (g, τftv))
              else do
                τftv' ← assignTV α lab' τftv
                return ((n2', lab'), (assignNode n1' n2' g, τftv'))
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
      assignTV α atom τftv = do
        writeTV α (atomTy atom)
        assignFtvMap α atom τftv
      -- Given two type variables, where α ← atom, update a map of free
      -- type variables to variance lists accordingly
      assignFtvMap α atom vmap =
        case Map.lookup α vmap of
          Just vs → case atom of
            VarAt β → return $ Map.insertWith (+) β vs vmap'
            ConAt _ → return vmap'
          Nothing → return vmap
        where vmap' = Map.delete α vmap
      -- Coalesce and remove fully-generalizable components
      coalesceComponents value (g, γrank, τftv) = do
        extvs  ← getExistentials (g, γrank, τftv)
        τcands ← genCandidates value τftv γrank
        let candidates = Set.mapMonotonic VarAt $ extvs `Set.union` τcands
            each state component@(_:_)
              | all (`Set.member` candidates) (map snd component)
              = do
                  ((node, _), (g', τftv'))
                    ← coalesceList state component
                  return (Gr.delNode node g', τftv')
            each state _
              = return state
        foldM each (g, τftv) (Gr.labComponents g)
      -- Find the generalization candidates, which are free in τ but
      -- not in γ (restricted further if not a value)
      genCandidates value τftv γrank =
        Set.fromDistinctAscList <$>
          removeByRank γrank (map fst (Map.toAscList (restrict τftv)))
          where
          restrict = if value
                       then id
                       else Map.filter (`elem` [1, -1, 2, -2])
      -- Remove type variables from a list if their rank indicates that
      -- they're in the environment
      removeByRank γrank = filterM keep
        where
          keep α = do
            rank ← getTVRank α
            return (rank > γrank)
      -- Reconstruct a constraint from the remaining graph
      reconstruct g qc =
        SC {
          scTypes = do
            (n1, n2) ← Gr.edges g
            let Just α1 = Gr.lab g n1
                Just α2 = Gr.lab g n2
            return (atomTy α1, atomTy α2),
          scQuals = qc
        }

-- | A representation of equivalence classes of same-sized type
--   variables and their shapes.
newtype SkelMap tv r m
  = SkelMap {
      -- | Associates each type variable with the “skeleton” that
      --   contains it, which is a set of related type variables and
      --   maybe a constructor applied to some type variables, which
      --   determines the shape of the skeleton.
      unSkelMap   ∷ Map.Map tv (Skeleton tv r m)
    }
type Skeleton tv r (m ∷ * → *) = UF.Proxy r (Set.Set tv, Shape tv r m)

data Shape tv r (m ∷ * → *)
  = ConShape Name [Skeleton tv r m]
  | RowShape Name (Skeleton tv r m) (Skeleton tv r m)
  | NoShape

type ExtSkels tv = [(tv, [tv], Maybe (Type tv))]

skeletonTV ∷ MonadU tv r m ⇒ Skeleton tv r m → m tv
skeletonTV = Set.findMin . fst <$$> UF.desc

shapeToType ∷ forall tv r m. MonadU tv r m ⇒
              Shape tv r m → Maybe (Type tv)
shapeToType shape = unsafePerformU (shapeToTypeM shape ∷ m (Maybe (Type tv)))

shapeToTypeM ∷ MonadU tv r m ⇒ Shape tv r m → m (Maybe (Type tv))
shapeToTypeM shape = do
  case shape of
    ConShape n sks     → Just . ConTy n <$> mapM conv sks
    RowShape n sk1 sk2 → Just <$$> RowTy n <$> conv sk1 <*> conv sk2
    NoShape            → return Nothing
  where conv = fvTy <$$> skeletonTV

extSkels ∷ MonadU tv r m ⇒ SkelMap tv r m → ExtSkels tv
extSkels = unsafePerformU . extSkelsM

-- | Produce a showable representation of an skeletonized subtype
--   constraint
extSkelsM ∷ MonadU tv r m ⇒ SkelMap tv r m → m (ExtSkels tv)
extSkelsM = mapM each . Map.toList . unSkelMap
  where
    each (α, proxy) = do
      (set, shape) ← UF.desc proxy
      τ ← shapeToTypeM shape
      return (α, Set.toList set, τ)

instance (Tv tv, MonadU tv r m) ⇒ Show (Shape tv r m) where
  showsPrec p = maybe (showChar '_') (showsPrec p) . shapeToType

instance (Tv tv, MonadU tv r m) ⇒ Show (SkelMap tv r m) where
  show skm = concat $
    [ "\n⋀ {" ++ show α ++ " ∈ " ++
      concat (List.intersperse "≈" [ show (tvUniqueID β) | β ← βs ]) ++
        maybe "" ((" ≈ " ++) . show) mτ
      ++ "}"
    | (α, βs, mτ) ← List.sortBy (\(_,x,_) (_,y,_) → compare x y)
                                (extSkels skm) ]

data FoldWriterT m a =
  FoldWriterT { unfoldWriterT ∷ WriterT [FoldWriterT m a] m a }

-- | Build an internal subtype constraint from an external subtype
--   constraint.
skeletonize ∷ MonadU tv r m ⇒ [(Type tv, Type tv)] → m (SkelMap tv r m)
skeletonize sc0 = do
  rskels ← newRef Map.empty
  let -- | Record that @τ1@ is a subtype of @τ2@, and do some
      --   unification.
      delay action = tell [FoldWriterT action]
      relateTypes τ1 τ2 = do
        (_, skel1) ← registerType τ1
        (_, skel2) ← registerType τ2
        relateSkels skel1 skel2
      -- | Relate two type variables in the same skeleton
      relateTVs α1 α2 = relateTypes (fvTy α1) (fvTy α2)
      -- |
      relateSkels = UF.coalesce_ combiner
      --
      -- Given a type, create a shape and skeleton for it, store them in
      -- the relevant data structures, and return the type variable that
      -- associates the type with its skeleton.
      registerType τ = do
        case τ of
          ConTy c τs → do
            (αs, skels) ← unzip <$> mapM registerType τs
            α  ← tvOf (ConTy c (map fvTy αs))
            newSkel α (ConShape c skels)
          RowTy n τ1 τ2 → do
            (α1, skel1) ← registerType τ1
            (α2, skel2) ← registerType τ2
            α  ← tvOf (RowTy n (fvTy α1) (fvTy α2))
            newSkel α (RowShape n skel1 skel2)
          VarTy (FreeVar α) → registerTV α
          _ → fail $ "BUG! skeletonize"
      --
      -- Lookup or register a type variable.
      registerTV α = do
        mskel ← Map.lookup α <$> readRef rskels
        case mskel of
          Just skel → return (α, skel)
          Nothing   → do
            mτ ← readTV α
            case mτ of
              Left α'  → newSkel α' NoShape
              Right τ' → do
                (α', skel) ← registerType τ'
                rewriteTV α (fvTy α')
                return (α', skel)
      --
      -- Given a type variable and shape, construct a new skeleton
      newSkel α shape = do
        skel ← UF.create (Set.singleton α, shape)
        modifyRef (Map.insert α skel) rskels
        return (α, skel)
      --
      -- Combine two skeletons
      combiner (αs1, shape1) (αs2, shape2) = do
        shape' ← case (shape1, shape2) of
          (NoShape, _)                    → return shape2
          (_, NoShape)                    → return shape1
          (ConShape c1 [], ConShape _ []) → return (ConShape c1 [])
          (ConShape c1 sks1, ConShape c2 sks2)
            | c1 == c2 && length sks1 == length sks2
                                         → do
            sequence_ [ unless (var ⊑ QInvariant) $
                          delay (relateSkels sk1 sk2)
                      | var ← getVariances c1 (length sks1)
                      | sk1  ← sks1
                      | sk2  ← sks2 ]
            return (ConShape c1 sks1)
          (RowShape n1 sk1 sk1', RowShape n2 sk2 sk2')
            | n1 < n2   → mutate (n1, sk1, sk1') αs2
            | n1 > n2   → mutate (n2, sk2, sk2') αs1
            | otherwise → do
                delay (relateSkels sk1 sk2)
                delay (relateSkels sk1' sk2')
                return (RowShape n1 sk1 sk1')
          _             → fail $
            "Could not unify " ++ show shape1 ++ " and " ++ show shape2
        return (Set.union αs1 αs2, shape')
      --
      -- Permute rows to bring matching labels together.
      mutate (la, sk, sk') βs = do
        α  ← lift $ skeletonTV sk
        α' ← lift $ skeletonTV sk'
        sequence_
          [ do
              eτ ← readTV β
              case eτ of
                Left _  → return ()
                Right (RowTy lb τ τ') → do
                  δ  ← newTV
                  δ' ← tvOf (RowTy lb τ (fvTy δ))
                  delay $ relateTypes τ' (RowTy la (fvTy α) (fvTy δ))
                  delay $ relateTVs α' δ'
                  rewriteTV β (RowTy la (fvTy α) (fvTy δ'))
                Right x → fail $ "BUG! bad skeleton: " ++ show x
          | β  ← Set.toList βs ]
        return (RowShape la sk sk')
      --
  let loop []      = return ()
      loop actions = do
        actions' ← execWriterT (sequence_ actions)
        loop (map unfoldWriterT actions')
  loop (map (uncurry relateTypes) sc0)
  SkelMap <$> readRef rskels

-- | Make sure an internal subtype constraint is consistent with a
--   finite model. Returns the skeletons topologically sorted by
--   size (largest first), and a list of skeletons to avoid
--   expanding because they are involved in (legal) cycles.
occursCheck ∷ ∀ tv r m. MonadU tv r m ⇒
              SkelMap tv r m → m ([Skeleton tv r m], [Skeleton tv r m])
occursCheck skm = do
  gr ← foldM addSkel Gr.empty (Map.toList (unSkelMap skm))
  let scc = Gr.labScc (gr ∷ Gr (Skeleton tv r m) Bool)
  trace ("occursCheck", List.nub (Gr.edges gr), map (map fst) scc)
  mconcatMapM (checkSCC gr) scc
  where
  addSkel gr (_, sk1) = do
    (_, shape) ← UF.desc sk1
    case shape of
      NoShape         → return gr
      ConShape c sks2 → foldM (assertGt False sk1) gr
                          [ sk2
                          | (sk2, v) ← zip sks2 (getVariances c (length sks2))
                          , not (v ⊑ QInvariant) ]
      RowShape _ sk2 sk2' → do
        gr ← assertGt True sk1 gr sk2
        assertGt False sk1 gr sk2'
  assertGt ok sk1 gr sk2 = do
    (gr, node1) ← insertNew sk1 gr
    (gr, node2) ← insertNew sk2 gr
    return (Gr.insEdge (node1, node2, ok) gr)
  insertNew skel gr = do
    node ← tvUniqueID <$> skeletonTV skel
    case Gr.lab gr node of
      Just _  → return (gr, node)
      Nothing → return (Gr.insNode (node, skel) gr, node)
  checkSCC gr [(n,α)] | lookup n (Gr.lsuc gr n) == Nothing
                      = return ([α], [])
  checkSCC gr lns     =
    let nodes = Set.fromList (map fst lns) in
     if null [ ()
             | (n, _)     ← lns
             , (n', True) ← Gr.lsuc gr n
             , n' `Set.member` nodes ]
      then fail $ "Occurs check failed: " ++ show (map fst lns)
      else return ([], map snd lns)

-- | Expand all type variables to their full shape.
expand ∷ MonadU tv r m ⇒
         -- | the skeletons
         SkelMap tv r m →
         -- | skeletons in order of expansion
         [Skeleton tv r m] →
         -- | skeletons not to expand
         [Skeleton tv r m] →
         m (SkelMap tv r m, Set.Set tv)
expand skm0 skels skipSkels = do
  rskels   ← newRef (unSkelMap skm0)
  noExpand ← Set.fromList <$> mapM skeletonTV skipSkels
  let expandSkel skel = do
        α ← skeletonTV skel
        unless (α `Set.member` noExpand) $ do
          (αs, shape) ← UF.desc skel
          mapM_ (expandShape shape) (Set.toList αs)
      expandShape shape α = do
        eτ ← readTV α
        case eτ of
          Right _ → return ()
          Left α' → case shape of
            NoShape        → return ()
            ConShape _ []  → return ()
            ConShape c sks → do
              let kinds = map varianceToKind (getVariances c (length sks))
              βs' ← zipWithM newSkelTV sks kinds
              writeTV α' (ConTy c (map fvTy βs'))
            RowShape n sk1 sk2 → do
              β1 ← newSkelTV sk1 TypeKd
              β2 ← newSkelTV sk2 TypeKd
              writeTV α' (RowTy n (fvTy β1) (fvTy β2))
      newSkelTV skel kind = do
        β ← newTVKind kind
        (αs, shape) ← UF.desc skel
        UF.setDesc skel (Set.insert β αs, shape)
        modifyRef (Map.insert β skel) rskels
        return β
      noExpandVars skels = Set.unions <$> sequence
        [ fst <$> UF.desc (fromJust (Map.lookup α skels))
        | α ← Set.toList noExpand ]
  mapM_ expandSkel skels
  skels'    ← readRef rskels
  noExpand' ← noExpandVars skels'
  return (skm0 { unSkelMap = skels' }, noExpand')

{-

Syntactic metavariables:

 γ:  any type variable
 α:  generalization candidates
 β:  type variables with Q-variance
 δ:  generalization candidates with Q-variance
 q:  qualifier literals
 _s: a collection of _

 qe  ::=  q  |  γs  |  q γs     (qualifier expressions)

First rewrite as follows:

(DECOMPOSE)
  γs₁ \ γs₂ = γ₁ ... γⱼ
  βs  = { γ ∈ γs₂ | γ is Q-variant }
  βsᵢ = if γᵢ is Q-variant then γs₂ else βs
  -----------------------------------------------------------------------
  q₁ γs₁ ⊑ q₂ γs₂  --->  q₁ \-\ q₂ ⊑ βs ⋀ γ₁ ⊑ q₁ βs₁ ⋀ ... ⋀ γⱼ ⊑ q₁ βsᵢ

(BOT-SAT)
  ---------------
  U ⊑ βs  --->  ⊤

(TOP-SAT)
  -----------------
  γ ⊑ L βs  --->  ⊤

(BOT-UNSAT)
  q ≠ U
  -----------------
  q ⊑ U  --->  fail

(COMBINE-QLIT)
  --------------------------------------------
  γ ⊑ q ⋀ γ ⊑ q' ⋀ C; τ  --->  γ ⊑ q⊓q' ⋀ C; τ

(COMBINE-LE)
  q ⊑ q'   βs ⊆ βs'
  ---------------------------------------------------
  γ ⊑ q βs ⋀ γ ⊑ q' βs' ⋀ C; τ  --->  γ ⊑ q βs ⋀ C; τ

Then we have a constraint where each inequality is in one of two forms:

  γ ⊑ q βs
  q ⊑ βs

Now we continue to rewrite and perform substitutions as well.  Continue
to apply the above rules when they apply.  These new rewrites apply to a
whole constraint and type together, not to single atomic constraints.

For a type variable γ and type τ, let V(γ,τ) be γ's variance in τ.  We
also refer to the free type variables in only the lower or upper bounds
of a constraint C as lftv(C) and uftv(C), respectively.

These are non-lossy rewrites. Repeat them as much as possible,
continuing to apply the rewrites above when applicable:

(FORCE-U)
  -------------------------------
  β ⊑ U ⋀ C; τ  --->  [U/β](C; τ)

(SUBST-NEG)
  δ ∉ lftv(C)   V(δ,τ) ⊑ Q-
  ---------------------------------
  δ ⊑ qe ⋀ C; τ  --->  [qe/δ](C; τ)

(SUBST-NEG-TOP)
  δ ∉ lftv(C)   V(δ,τ) ⊑ Q-
  -------------------------
  C; τ  --->  [L/δ](C; τ)

(SUBST-POS)
  δ ∉ uftv(C)   V(δ,τ) ⊑ Q+
  -----------------------------------------------------------
  qe₁ ⊑ δ ⋀ ... ⋀ qeⱼ ⊑ δ ⋀ C; τ  --->  [qe₁⊔...⊔qeⱼ/δ](C; τ)

(SUBST-INV)
  δ ∉ uftv(C)   V(δ,τ) = Q=   δ' fresh
  --------------------------------------------------------------
  qe₀ ⊑ δ ⋀ ... ⋀ qeⱼ ⊑ δ ⋀ C; τ  --->  [δ'⊔qe₀⊔...⊔qeⱼ/δ](C; τ)

Substitute for contravariant qualifier variables by adding these lossy
rewrites:

(SUBST-NEG-LOSSY)
  δ ∉ lftv(C)   V(δ,τ) = Q-
  -----------------------------------------------
  δ ⊑ q₁ βs₁ ⋀ ... ⋀ δ ⊑ qⱼ βsⱼ ⋀ C; τ
    --->  [(q₁⊓...⊓qⱼ) (βs₁ ∩ ... ∩ βsⱼ)/δ](C; τ)

Run SAT as below for anything we missed.  Then, add bounds:

(BOUND)
  α ∉ lftv(C)   V(α,τ) ∈ { -, +, =, Q= }   q = q₁⊓...⊓qⱼ
  ------------------------------------------------------
  α ⊑ q₁ βs₁ ⋀ ... ⋀ α ⊑ qⱼ βsⱼ ⋀ C; τ
    ---> [U/α]C; ∀α:q. τ


We convert it to SAT as follows:

  Define:

    πr(Q)       = R ⊑ Q
    πr(β)       = 2 * tvId β
    πr(q1 ⊔ q2) = πr(q1) ⋁ πr(q2)
    πr(q1 ⊓ q2) = πr(q1) ⋀ πr(q2)

    πa(Q) = A ⊑ Q
    πa(β) = 2 * tvId β + 1
    πa(q1 ⊔ q2) = πa(q1) ⋁ πa(q2)
    πa(q1 ⊓ q2) = πa(q1) ⋀ πa(q2)

    Then given the constraint

      q1 ⊑ q1' ⋀ ... ⋀ qk ⊑ qk'

    generate the formula:

      (πr(q1) ⇒ πr(q1')) ⋀ (πa(q1) ⇒ πa(q1'))
        ⋀ ... ⋀
      (πr(qk) ⇒ πr(qk')) ⋀ (πa(qk) ⇒ πa(qk'))

-}

data QE tv = QE { qeQLit ∷ !QLit, qeQSet ∷ !(Set.Set tv) }

instance Tv tv ⇒ Show (QE tv) where
  show (QE L _)  = "L"
  show (QE q γs) = concat (List.intersperse "⊔" (q' γs'))
    where γs' = map (show . tvUniqueID) (Set.toList γs)
          q'  = if q == U && not (Set.null γs) then id else (show q :)

instance Eq tv ⇒ Eq (QE tv) where
    QE L  _   == QE L  _   = True
    QE q1 γs1 == QE q2 γs2 = q1 == q2 && γs1 == γs2

instance Ord tv ⇒ Ord (QE tv) where
    QE L  _   `compare` QE L  _   = EQ
    QE q1 γs1 `compare` QE q2 γs2
      | q1 == q2  = γs1 `compare` γs2
      | q1 ⊑  q2  = LT
      | otherwise = GT

instance Bounded (QE tv) where
  minBound = QE U Set.empty
  maxBound = QE L Set.empty

instance Ord tv ⇒ Lattice (QE tv) where
  QE L _    ⊔ _         = maxBound
  _         ⊔ QE L _    = maxBound
  QE q1 γs1 ⊔ QE q2 γs2 = QE (q1 ⊔ q2) (γs1 `Set.union` γs2)
  --
  QE L _    ⊓ qe2       = qe2
  qe1       ⊓ QE L _    = qe1
  QE q1 γs1 ⊓ QE q2 γs2 = QE (q1 ⊓ q2) (γs1 `Set.intersection` γs2)
  --
  _         ⊑ QE L  _   = True
  QE q1 γs1 ⊑ QE q2 γs2 = q1 ⊑ q2 && γs1 `Set.isSubsetOf` γs2

instance Qualifier (QE tv) tv where
  toQualifierType (QE q γs) =
    toQualifierType (QExp q (FreeVar <$> Set.toList γs))

instance Ord tv ⇒ Ftv (QE tv) tv where
  ftvTree (QE _ γs) = return (FTBranch (map FTSingle (Set.toList γs)))

qeSubst ∷ Ord tv ⇒ tv → QE tv → QE tv → QE tv
qeSubst β (QE q βs) (QE q' βs')
  | Set.member β βs' = QE (q ⊔ q') (Set.union βs (Set.delete β βs'))
  | otherwise        = QE q' βs'

-- | Represents the meet of several qualifier expressions, which happens
--   when some variable has multiple upper bounds.  These are normalized
--   to implement COMBINE-QLIT and COMBINE-LE.
newtype QEMeet tv = QEMeet { unQEMeet ∷ [QE tv] }

instance Bounded (QEMeet tv) where
  minBound = QEMeet [minBound]
  maxBound = QEMeet []

instance Tv tv ⇒ Show (QEMeet tv) where
  show (QEMeet [])  = "L"
  show (QEMeet qem) = concat (List.intersperse " ⊓ " (map show qem))

instance Ord tv ⇒ Ftv (QEMeet tv) tv where
  ftvTree = ftvTree . unQEMeet

qemSingleton ∷ QE tv → QEMeet tv
qemSingleton (QE L _) = maxBound
qemSingleton qe       = QEMeet [qe]

qemInsert ∷ Ord tv ⇒ QE tv → QEMeet tv → QEMeet tv
qemInsert qe (QEMeet qem) = QEMeet (loop qe qem) where
  loop (QE L _)       qem = qem
  loop qe             []  = [qe]
  loop (qe@(QE q γs)) (qe'@(QE q' γs'):qem)
    | Set.null γs, Set.null γs'
                          = loop (QE (q ⊓ q') Set.empty) qem
    | qe ⊑ qe'            = loop qe qem
    | qe' ⊑ qe            = qe':qem
    | otherwise           = qe':loop qe qem

qemSubst ∷ Ord tv ⇒ tv → QE tv → QEMeet tv → QEMeet tv
qemSubst β qe = foldr (qemInsert . qeSubst β qe) mempty . unQEMeet

instance Ord tv ⇒ Monoid (QEMeet tv) where
  mempty  = maxBound
  mappend = foldr qemInsert <$.> unQEMeet

data SQState a tv
  = SQState {
      sq_αs    ∷ !(Set.Set tv),
      sq_τftv  ∷ !(VarMap tv),
      sq_βlst  ∷ ![(QLit, Set.Set tv)],
      sq_vmap  ∷ !(Map.Map tv (QEMeet tv)),
      sq_τ     ∷ !a
    }
  deriving Show

-- | Given a list of type variables that need qlit bounds and a set
--   of qualifier inequalities, solve and produce bounds.  Also return
--   any remaining inequalities (which must be satisfiable, but we
--   haven't guessed how to satisfy them yet.)
solveQualifiers
  ∷ MonadU tv r m ⇒
    Bool → Set.Set tv → [(Type tv, Type tv)] →
    Type tv → m ([(Type tv, Type tv)], [(tv, QLit)], Type tv)
solveQualifiers value αs qc τ = do
  let ?deref = readTV
  trace ("solveQ (init)", αs, qc)
  -- Clean up the constraint, standardize types to qualifier form, and
  -- deal with trivial stuff right away:
  qc             ← stdize qc
  trace ("solveQ (stdize)", qc)
  -- Decompose implements DECOMPOSE, TOP-SAT, BOT-SAT, and BOT-UNSAT.
  τftv           ← ftvV τ
  state          ← decompose qc SQState {
                     sq_αs   = αs,
                     sq_τftv = τftv,
                     sq_βlst = [],
                     sq_vmap = Map.empty,
                     sq_τ    = τ
                   }
  trace ("solveQ (decompose)", state)
  -- Rewrite until it stops changing
  state          ← iterChanging
                     (stdizeType        >=>
                      forceU            >=>
                      substNeg False    >=>!
                      substPosInv       >=>!
                      substNeg True)
                     state
  trace ("solveQ (rewrites)", state)
  -- Try the SAT solver, then recheck
  state          ← runSat state True
  trace ("solveQ (sat)", state)
  runSat state False
  -- Finish by reconstructing the constraint and returning the bounds
  -- for the variables to quantify.
  state          ← genVars state
  return (recompose state, getBounds state, τ)
  where
  --
  -- Given a list of qualifier inequalities on types, produce a list of
  -- inequalities on standard-form qualifiers, omitting trivial
  -- inequalities along the way.
  stdize qc = foldM each [] qc where
    each qc' (τl, τh) = do
      qe1 ← makeQE τl
      qe2 ← makeQE τh
      if qe1 ⊑ qe2
        then return qc'
        else return ((qe1, qe2) : qc')
  --
  -- Given a list of inequalities on qualifiers, rewrite them into
  -- the two decomposed forms:
  --
  --  • γ ⊑ q βs
  --
  --  • q ⊑ βs
  --
  -- This implements DECOMPOSE, BOT-SAT, TOP-SAT, and BOT-UNSAT.
  decompose qc state0 = foldM each state0 qc where
    each state (QE q1 γs1, QE q2 γs2) = do
      let γs' = γs1 Set.\\ γs2
          βs' = Set.filter (tvKindIs QualKd) γs2
      fβlst ← case q1 \-\ q2 of
        -- (BOT-SAT)
        U  →   return id
        -- (BOT-UNSAT)
        q' | Set.null βs' →
               fail $ "Qualifier inequality unsatisfiable: " ++
                      show (toQualifierType (QE q1 γs1)) ++
                      " ⊑ " ++ show (toQualifierType (QE q2 γs2))
           | otherwise →
               return ((q', βs') :)
      let fvmap = if q2 == L
                    then id     -- (TOP-SAT)
                    else Map.unionWith mappend (setToMapWith bound γs')
          bound γ
            | tvKindIs QualKd γ = qemSingleton (QE q2 γs2)
            | otherwise         = qemSingleton (QE q2 βs')
      return state {
               sq_βlst = fβlst (sq_βlst state),
               sq_vmap = fvmap (sq_vmap state)
             }
  --
  -- Standardize the qualifiers in the type
  stdizeType state = do
    τ    ← derefAll τ
    let meet = bigMeet . map qeQLit . filter (Set.null . qeQSet) . unQEMeet
        qm   = Map.map meet (sq_vmap state)
        τ'   = standardizeQuals qm τ
    trace ("stdizeType", τ, τ', qm)
    let ?deref = readTV
    τftv ← ftvV τ'
    return state {
             sq_τ    = τ',
             sq_τftv = τftv
           }
  --
  -- Substitute U for qualifier variables upper bounded by U (FORCE-U).
  forceU state =
    subst "forceU" state $
      Map.fromDistinctAscList
      [ (β, minBound)
      | (β, QEMeet [QE U γs]) ← Map.toAscList (sq_vmap state)
      , tvKindIs QualKd β
      , Set.null γs ]
  --
  -- Replace Q- or 0 variables by a single upper bound, if they have only
  -- one (SUBST-NEG), or by L if they have none (SUBST-NEG-TOP).  If
  -- 'doLossy', then we include SUBST-NEG-LOSSY as well, which uses
  -- approximate lower bounds for combining multiple upper bounds.
  substNeg doLossy state =
    subst who state $ Map.fromDistinctAscList $ do
      δ ← Set.toAscList (sq_αs state)
      guard (Map.findWithDefault 0 δ (sq_τftv state) ⊑ QContravariant)
      case Map.lookup δ (sq_vmap state) of
        Nothing            → return (δ, maxBound)
        Just (QEMeet [])   → return (δ, maxBound)
        Just (QEMeet [qe]) → return (δ, qe)
        Just (QEMeet qes)
          | doLossy        → return (δ, bigMeet qes)
          | otherwise      → mzero
    where who = if doLossy then "substNeg (lossy)" else "substNeg"
  --
  -- Replace Q+ and Q= variables with tight lower bounds.
  substPosInv state = do
    let add qe (QE U (Set.toList → [β]))
          | β `Set.member` sq_αs state
          = Map.insertWith (liftM2 (⊔)) β (Just qe)
        add _  (QE _ βs)
          = Map.union (setToMap Nothing βs)
        lbs0 = setToMap (Just minBound)
                        (Set.filter (tvKindIs QualKd) (sq_αs state))
                 Map.\\ sq_vmap state
        lbs1 = Map.foldrWithKey each lbs0 (sq_vmap state) where
          each γ (QEMeet qem) = foldr (add (QE U (Set.singleton γ))) <-> qem
        lbs2 = Map.mapMaybe id (foldr each lbs1 (sq_βlst state)) where
          each (q, βs) = add (QE q Set.empty) (QE U βs)
        pos  = lbs2 Map.\\ Map.filter (/= QCovariant) (sq_τftv state)
        inv  = lbs2 `Map.intersection`
                 Map.filter (== QInvariant) (sq_τftv state)
    (δ's, inv) ← first Set.fromDistinctAscList . unzip <$> sequence
      [ do
          δ' ← newTVKind QualKd
          return (δ', (δ, QE q (Set.insert δ' βs)))
      | (δ, qe@(QE q βs)) ← Map.toAscList inv
      , qe /= minBound ]
    subst "substPosInv"
          state {
            sq_αs = sq_αs state `Set.union` δ's
          }
          (pos `Map.union` Map.fromDistinctAscList inv)
  --
  -- Given a list of type variables and qualifiers, substitute for each,
  -- updating the state as necessary.
  subst who state γqes0
    | Map.null γqes0 = return state
    | otherwise      = do
    trace (who, γqes0, state)
    let sanitize _    []  []
          = fail $ "BUG! (subst)" ++ who ++
                   " attempt impossible substitution: " ++ show γqes0
        sanitize _    acc []
          = unsafeSubst state (Map.fromDistinctAscList (reverse acc))
        sanitize seen acc ((γ, QE q γs):rest)
          | Set.member γ (Set.union seen γs)
          = sanitize seen acc rest
          | otherwise
          = sanitize (seen `Set.union` γs) ((γ, QE q γs):acc) rest
    sanitize Set.empty [] (Map.toAscList γqes0)
  --
  -- This does the main work of substitution, and it has a funny
  -- precondition (which is enforced by 'subst', above), namely:
  -- the type variables will be substituted in increasing order, so the
  -- image of later variables must not contain earlier variables.
  --
  -- This is okay:     { 1 ↦ 2 3, 2 ↦ 4 }
  -- This is not okay: { 1 ↦ 3 4, 2 ↦ 1 }
  unsafeSubst state γqes = do
    sequence [ writeTV γ (toQualifierType qe) | (γ, qe) ← Map.toList γqes ]
    let γset          = Map.keysSet γqes
        unchanged set = Set.null (γset `Set.intersection` set)
        (βlst, βlst') = List.partition (unchanged . snd) (sq_βlst state)
        (vmap, vmap') = Map.partitionWithKey
                          (curry (unchanged . Map.keysSet . ftvPure))
                          (sq_vmap state)
    ineqs ← stdize $
      [ (toQualifierType ql, toQualifierType (QE U βs))
      | (ql, βs) ← βlst' ]
        ++
      [ (fvTy γ, toQualifierType qe)
      | (γ, qem) ← Map.toList vmap'
      , qe       ← unQEMeet qem ]
    state ← decompose ineqs
      state {
        sq_αs   = sq_αs state Set.\\ γset,
        sq_τftv = Map.foldrWithKey (\γ (QE _ γs) → substMap γ γs)
                                   (sq_τftv state) γqes,
        sq_βlst = βlst,
        sq_vmap = vmap
      }
    trace ("subst", γqes, state)
    return state
  --
  -- As a last ditch effort, use a simple SAT solver to find a
  -- decent literal-only substitution.
  runSat state doIt = do
    let formula = toSat state
        sols    = SAT.solve =<< SAT.assertTrue formula SAT.newSatSolver
        δs      = Set.filter (tvKindIs QualKd) (sq_αs state)
    trace ("runSat", formula, sols)
    case sols of
      []  → fail "Qualifier constraints unsatisfiable"
      sat:_ | doIt
          → subst "sat" state =<<
              Map.fromDistinctAscList <$> sequence
                [ do
                    βs ← case var of
                      QInvariant → Set.singleton <$> newTVKind QualKd
                      _          → return Set.empty
                    -- warn $ "\nSAT: substituting " ++ show (QE q βs) ++
                    --        " for type variable " ++ show δ
                    return (δ, QE q βs)
                | δ ← Set.toAscList δs
                , let (q, var) = decodeSatVar δ (sq_τftv state) sat
                , q /= U || var /= QInvariant ]
      _   → return state
  --
  toSat state = foldr (SAT.:&&:) SAT.Yes $
      [ (πr vm q ==> πr vm (U,βs)) SAT.:&&: (πa vm q ==> πa vm (U,βs))
      | (q, βs) ← sq_βlst state ]
    ++
      [ (πr vm (FreeVar α) ==> πr vm (q,αs)) SAT.:&&:
        (πa vm (FreeVar α) ==> πa vm (q,αs))
      | (α, QEMeet qes) ← Map.toList (sq_vmap state)
      , QE q αs         ← qes
      , tvKindIs QualKd α ]
    where
      p ==> q = SAT.Not p SAT.:||: q
      vm = sq_τftv state
  --
  -- Find the variables to generalize
  genVars state = return state { sq_αs = αs' } where
    αs'  = sq_αs state `Set.intersection` kset
    kset = Map.keysSet (keep (sq_τftv state))
    keep = if value then id else Map.filter (`elem` [-2,-1,1,2])
  --
  -- Find the the bounds of variables to generalize
  getBounds state =
    map (id &&& getBound) (Set.toList (sq_αs state)) where
      getBound α = case Map.lookup α (sq_vmap state) of
        Nothing           → L
        Just (QEMeet qes) → bigMeet (map qeQLit qes)
  --
  -- Turn the decomposed constraint back into a list of pairs of types.
  recompose state =
      [ (fvTy γ, clean (q, βs))
      | (γ, QEMeet qem) ← Map.toList (sq_vmap state)
      , γ `Set.notMember` sq_αs state
      , QE q βs ← qem ]
    ++
      [ (toQualifierType q, clean (U, βs))
      | (q, βs) ← sq_βlst state ]
    where
    clean (q, βs) = toQualifierType (q, βs Set.\\ sq_αs state)
  --
  makeQE q = do
    let ?deref = readTV
    QExp ql γs ← qualifier (toQualifierType q)
    return (QE ql (Set.fromList (fromVar <$> γs)))
  --
  fromVar (FreeVar α) = α
  fromVar _           = error "BUG! solveQualifiers got bound tyvar"

substSet ∷ Ord tv ⇒ tv → Set.Set tv → Set.Set tv → Set.Set tv
substSet β βs γs
  | Set.member β γs = Set.union βs (Set.delete β γs)
  | otherwise       = γs

substMap ∷ Ord tv ⇒ tv → Set.Set tv → VarMap tv → VarMap tv
substMap β βs vmap = case takeMap β vmap of
  (Just v, vmap') → Map.unionWith (⊔) vmap' (setToMap v βs)
  _               → vmap

takeMap ∷ Ord k ⇒ k → Map.Map k v → (Maybe v, Map.Map k v)
takeMap = Map.updateLookupWithKey (\_ _ → Nothing)

setToMap   ∷ a → Set.Set k → Map.Map k a
setToMap   = setToMapWith . const

setToMapWith   ∷ (k → a) → Set.Set k → Map.Map k a
setToMapWith f = Map.fromDistinctAscList . map (id &&& f) . Set.toAscList

class SATable a v where
  πa ∷ VarMap v → a → SAT.Boolean
  πr ∷ VarMap v → a → SAT.Boolean

instance SATable QLit v where
  πa _ ql | A ⊑ ql    = SAT.Yes
          | otherwise = SAT.No
  πr _ ql | R ⊑ ql    = SAT.Yes
          | otherwise = SAT.No

instance Tv v ⇒ SATable (Var v) v where
  πa vm (FreeVar β) = encodeSatVar A β vm
  πa _  _           = SAT.No
  πr vm (FreeVar β) = encodeSatVar R β vm
  πr _  _           = SAT.No

instance (Tv v, SATable (Var v) v) ⇒ SATable (QLit, Set.Set v) v where
  πa vm (q, vs) = Set.fold ((SAT.:||:) . πa vm . FreeVar) (πa vm q) vs
  πr vm (q, vs) = Set.fold ((SAT.:||:) . πr vm . FreeVar) (πr vm q) vs

-- | Given a type variable and a SAT solution, return a bound
--   for that type variable as implied by the solution.
decodeSatVar ∷ Tv tv ⇒ tv → VarMap tv → SAT.SatSolver → (QLit, Variance)
decodeSatVar β vm solver = (q, var) where
  (maximize, var) = maximizeVariance β vm
  q   = case (maximize, mba, mbr) of
    -- For minimizing variables, each component tells us whether that
    -- component may be omitted from the substitution, so we choose the
    -- smallest qualifier literal that includes the required components.
    (False, Just False, Just False) → L
    (False, Just False, _         ) → A
    (False, _         , Just False) → R
    (False, _         , _         ) → U
    -- For maximizing variables, each component tells us whether that
    -- component may be included in the substitution, so we choose the
    -- largest qualifier literal that omits the forbidden components.
    (True , Just False, Just False) → U
    (True , Just False, _         ) → R
    (True , _         , Just False) → A
    (True , _         , _         ) → L
  mba = SAT.lookupVar βa solver
  mbr = SAT.lookupVar βr solver
  βa  = varComponent A β
  βr  = varComponent R β

-- | Encode the 'q' component of type variable 'β'.  We want to maximize
--   contravariant variables and minimize all the others.  Since the
--   solver tries true before false, we use a positive literal to stand
--   for the 'q' component of a maximized variable and a negative
--   literal for a minimized variable.
encodeSatVar ∷ Tv tv ⇒ QLit → tv → VarMap tv → SAT.Boolean
encodeSatVar q β vm
  | fst (maximizeVariance β vm) = SAT.Var z
  | otherwise                 = SAT.Not (SAT.Var z)
  where z = varComponent q β

maximizeVariance ∷ Ord tv ⇒ tv → VarMap tv → (Bool, Variance)
maximizeVariance γ vm = case Map.findWithDefault 0 γ vm of
  v@QCovariant  → (False, v)
  v@QInvariant  → (False, v)
  v             → (True,  v)

-- | We encode the A and R “components” of a variable via this
--   bijection.
varComponent ∷ Tv tv ⇒ QLit → tv → Int
varComponent A β = 2 * tvUniqueID β
varComponent _ β = 2 * tvUniqueID β + 1

{-

OPTIMIZATIONS FROM SIMONET 2003

6.1 Collapsing Cycles

  This is the SCC phase

6.2 Polarities (implemented in buildGraph)

  Upper bounds on positive variables and lower bounds on negative
  variables are irrelevant, e.g.:

    f : ∀ α ≤ A. 1 → α × α
    f : ∀ α. 1 → α × α

  Or:

    let rec f = λx. f (f x) in f
    f : α → β [β ≤ α]
    f : ∀α. ∀β ≤ α. α → β
    f : ∀α. ∀β. α → β

6.3 Reducing Chains (implemented in polarizedReduce)

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
λf. f f

0 <: C 1   ⋀   1 <: C 0

0 <: C 1
  0: C 2
C 2 <: C 1
2 <: 1
    (2 ~ 1)
1 <: C (C 2)

-}

