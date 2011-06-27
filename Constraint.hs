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
module Constraint (
  MonadC(..), runConstraintT,
) where

import Prelude

import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.RWS
import Control.Monad.List
import qualified Data.List  as List
import qualified Data.Map   as Map
import qualified Data.Set   as Set
import qualified Text.PrettyPrint as Ppr

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
  (⊏:), (~:)    ∷ (Qualifier q1 tv, Qualifier q2 tv) ⇒ q1 → q2 → m ()
  -- | Constrain by the given variance
  rel           ∷ Variance → Type tv → Type tv → m ()
  --
  τ1 =: τ2   = τ1 <: τ2 >> τ2 <: τ1
  τ1 ~: τ2   = τ1 ⊏: τ2 >> τ2 ⊏: τ1
  rel v τ τ' = case v of
    Covariant      → τ <: τ'
    Contravariant  → τ' <: τ
    Invariant      → τ =: τ'
    QCovariant     → τ ⊏: τ'
    QContravariant → τ' ⊏: τ
    QInvariant     → τ ~: τ'
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

---
--- Eager subtyping constraint solver
---

newtype ConstraintT tv r m a
  = ConstraintT {
      unConstraintT_ ∷ StateT (EagerState tv r) m a
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
  showsPrec _ es
    | null (Gr.edges (esGraph es)) && null (esQuals es)
        = id
    | otherwise
        = showString "EagerState { esGraph = "
        . shows (Gr.ShowGraph (esGraph es))
        . showString ", esQuals = "
        . shows (esQuals es)
        . showString " }"

runConstraintT ∷ MonadU tv r m ⇒ ConstraintT tv r m a → m a
runConstraintT m = evalStateT (unConstraintT_ m) es0
  where es0        = EagerState {
                       esGraph   = gr0,
                       esNodeMap = nm0,
                       esEquivs  = Map.empty,
                       esQuals   = []
                     }
        (gr0, nm0) = NM.mkMapGraph
                       (map (ConAt . snd) (Gr.labNodes tyConOrder))
                       []

instance MonadRef r m ⇒ MonadRef r (ConstraintT tv r m) where
  newRef        = lift <$> newRef
  readRef       = lift <$> readRef
  writeRef      = lift <$$> writeRef
  unsafeIOToRef = lift <$> unsafeIOToRef

instance MonadU tv r m ⇒ MonadU tv r (ConstraintT tv r m) where
  newTVKind     = lift <$> newTVKind
  writeTV_      = lift <$$> writeTV_
  readTV_       = lift <$> readTV_
  getTVRank_    = lift <$> getTVRank_
  setTVRank_    = lift <$$> setTVRank_
  hasChanged    = lift hasChanged
  putChanged    = lift <$> putChanged
  unsafePerformU= error "No MonadU.unsafePerformU for ConstraintT"
  unsafeIOToU   = lift <$> unsafeIOToU

instance (Ord tv, Monad m) ⇒
         NM.MonadNM (Atom tv) () Gr (ConstraintT tv r m) where
  getNMState = ConstraintT (gets (esNodeMap &&& esGraph))
  getNodeMap = ConstraintT (gets esNodeMap)
  getGraph   = ConstraintT (gets esGraph)
  putNMState (nm, g) = ConstraintT . modify $ \es →
    es { esNodeMap = nm, esGraph = g }
  putNodeMap nm = ConstraintT . modify $ \es → es { esNodeMap = nm }
  putGraph g    = ConstraintT . modify $ \es → es { esGraph = g }

instance MonadU tv r m ⇒ MonadC tv r (ConstraintT tv r m) where
  τ <: τ' = runSeenT (subtypeTypesK 0 τ τ')
  τ =: τ' = runSeenT (unifyTypesK 0 τ τ')
  τ ⊏: τ' = ConstraintT . modify . esQualsUpdate $
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
    qc    ← ConstraintT (gets esQuals)
    cftv  ← ftvSet . map snd =<< NM.getsGraph Gr.labNodes
    qcftv ← ftvSet qc
    αs    ← Set.fromDistinctAscList <$$>
              removeByRank γrank <$>
                Set.toAscList $
                  (qcftv `Set.union` Map.keysSet τftv) Set.\\ cftv
    (qc, αqs, τ) ← solveQualifiers value αs qc τ
    ConstraintT (modify (esQualsUpdate (const qc)))
    gtrace ("gen (finished)", αqs, τ)
    resetEquivTVs
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
    c ← ConstraintT get
    return (ConstraintT (put c))
  showConstraint = show <$> ConstraintT get

type SeenT tv r m = StateT (Map.Map (REC_TYPE tv, REC_TYPE tv) Bool)
                           (ConstraintT tv r m)

runSeenT ∷ MonadU tv r m ⇒ SeenT tv r m a → ConstraintT tv r m a
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
  QInvariant    → const (~:)
  QCovariant    → const (⊏:)
  QContravariant→ const (flip (⊏:))
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
      τ2' ← lift (occursCheck r1 τ2) >>= copyType
      unifyVarK k r1 τ2'
      subtypeTypesK k τ2' τ2
    (_, VarTy (FreeVar r2)) → do
      τ1' ← lift (occursCheck r2 τ1) >>= copyType
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
    (VarTy (FreeVar r1), VarTy (FreeVar r2)) →
      unifyVarK k r1 (fvTy r2)
    (VarTy (FreeVar r1), _) → do
      unifyVarK k r1 =<< lift (occursCheck r1 τ2)
    (_, VarTy (FreeVar r2)) → do
      unifyVarK k r2 =<< lift (occursCheck r2 τ1)
    (QuaTy q1 αs1 τ1', QuaTy q2 αs2 τ2')
      | q1 == q2 && αs1 == αs2
                    → check (k + 1) τ1' τ2'
    (ConTy c1 τs1, ConTy c2 τs2)
      | c1 == c2 && length τs1 == length τs2
                    → sequence_
                        [ if isQVariance var
                            then τ1' ~: τ2'
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
  τ ← derefAll τ0
  unless (lcTy k τ) $
    fail "cannot unify because insufficiently polymorphic"
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

-- | Performs the occurs check and returns a type suitable for unifying
--   with the given type variable, if possible.  This is possible if all
--   occurrences of @α@ in @τ@ occur guarded by a type constructor that
--   permits recursion, in which case we roll up @τ@ as a recursive type
--   and return that.
occursCheck ∷ MonadU tv r m ⇒ tv → Type tv → ConstraintT tv r m (Type tv)
occursCheck α τ = do
  gtrace ("occursCheck", α, τ)
  let ?deref = readTV
  (βsGuarded, βsUnguarded)
    ← (Map.keys *** Map.keys) . Map.partition id <$> ftvG τ
  whenM (anyM (checkEquivTVs α) βsUnguarded) $
    fail "Occurs check failed (size check)"
  recVars ← filterM (checkEquivTVs α) βsGuarded
  when (not (null recVars)) $
    gtrace ("occursCheck (recvars)", recVars)
  return (foldr closeRec τ recVars)

makeEquivTVs  ∷ MonadU tv r m ⇒ tv → tv → ConstraintT tv r m ()
makeEquivTVs α β = do
  pα ← getTVProxy α
  pβ ← getTVProxy β
  UF.coalesce_ (return <$$> Set.union) pα pβ

checkEquivTVs ∷ MonadU tv r m ⇒ tv → tv → ConstraintT tv r m Bool
checkEquivTVs α β = do
  pα ← getTVProxy α
  pβ ← getTVProxy β
  UF.sameRepr pα pβ

resetEquivTVs ∷ MonadU tv r m ⇒ ConstraintT tv r m ()
resetEquivTVs = do
  ConstraintT (modify (esEquivsUpdate (const Map.empty)))
  g     ← NM.getGraph
  mapM_ (uncurry makeEquivTVs)
        [ (α, β) | (VarAt α, VarAt β) ← Gr.labNodeEdges g ]

getTVProxy ∷ MonadU tv r m ⇒ tv → ConstraintT tv r m (TVProxy tv r)
getTVProxy α = do
  equivs ← ConstraintT (gets esEquivs)
  case Map.lookup α equivs of
    Just pα → return pα
    Nothing → do
      pα ← UF.create (Set.singleton α)
      ConstraintT (modify (esEquivsUpdate (Map.insert α pα)))
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

gtrace ∷ (MonadU tv r m, Show a) ⇒ a → ConstraintT tv r m ()
gtrace =
  if debug
    then \info → do
      trace info
      es ← ConstraintT get
      unsafeIOToU (print (indent es))
    else \_ → return ()
  where
    indent = Ppr.nest 4 . Ppr.fsep . map Ppr.text . words . show

---
--- Abstract constraints
---

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

