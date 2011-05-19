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

import Control.Monad.State
import Control.Monad.Writer
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
  (≤), (≥), (≤≥) ∷ Type r → Type r → c
  τ1 ≥ τ2        = τ2 ≤ τ1
  τ1 ≤≥ τ2       = τ1 ≤ τ2 ⋀ τ2 ≤ τ1
  -- | A subtype constraint in the given variance
  relate     ∷ Variance → Type r → Type r → c
  relate v τ τ' = case v of
    Covariant      → τ ≤ τ'
    Contravariant  → τ ≥ τ'
    Invariant      → τ ≤≥ τ'
    QCovariant     → τ ⊏ τ'
    QContravariant → τ' ⊏ τ
    QInvariant     → τ ⊏ τ' ⋀ τ' ⊏ τ
    Omnivariant    → (⊤)
  -- | A qualifier subsumption constraint
  (⊏)        ∷ (Qualifier q1 r, Qualifier q2 r) ⇒ q1 → q2 → c
  -- | Constrain a list of types against the occurrences of the rib-0
  --   variables of a term
  (⊏*)       ∷ Qualifier q r ⇒ [q] → Term Empty → c
  τs ⊏* e    = mconcat (zipWith (⊏) τs (countOccs e))
  --
  -- | Figure out which variables to generalize in a piece of syntax
  gen'       ∷ (MonadU r m, Ftv γ r, Ftv a r, Show a) ⇒
               Bool → c → γ → a → m ([r], [QLit], c)
  -- | Generalize a type under a constraint and environment,
  --   given whether the the value restriction is satisfied or not
  gen        ∷ (MonadU r m, Ftv γ r) ⇒
               Bool → c → γ → Type r → m (Type r, c)
  gen value c0 γ τ = do
    (αs, qls, c) ← gen' value c0 γ τ
    σ            ← closeWithQuals qls AllQu αs <$> derefAll τ
    return (σ, c)
  -- | Generalize a list of types together.
  genList    ∷ (MonadU r m, Ftv γ r) ⇒
               Bool → c → γ → [Type r] → m ([Type r], c)
  genList value c0 γ τs = do
    (αs, qls, c) ← gen' value c0 γ τs
    σs           ← mapM (closeWithQuals qls AllQu αs <$$> derefAll) τs
    return (σs, c)

infixr 4 ⋀
infix  5 ≤, ≥, ≤≥, ⊏, ⊏*

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
  deriving (Show)

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
  τ  ≤ τ'  = SC [(τ, τ')] []
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
  gen' value (SC c qc) γ τ = do
    let ?deref = readTV
    trace ("gen (begin)", (c, qc), τ)
    skm1         ← skeletonize c
    trace ("gen (skeletonized)", skm1, c, τ)
    αs           ← occursCheck skm1
    trace ("gen (occursCheck)", αs)
    skm2         ← expand skm1 αs
    trace ("gen (expand)", skm2, c, τ)
    (c, qc)      ← decompose (c, qc)
    γftv         ← ftvSet γ
    τftv         ← ftvV τ
    trace ("gen (decompose)", (c, qc), γftv, τftv, τ)
    let (nm, g) = buildGraph (Set.toList c) τftv
    trace ("gen (buildGraph)", Gr.ShowGraph g, γftv, τftv, τ)
    (g, γftv, τftv)
                 ← coalesceSCCs (g, γftv, τftv)
    trace ("gen (scc)", Gr.ShowGraph g, γftv, τftv, τ)
    (g, γftv, τftv)
                 ← satisfyTycons nm (g, γftv, τftv)
    trace ("gen (tycons)", Gr.ShowGraph g, γftv, τftv, τ)
    g            ← eliminateExistentials True nm (g, γftv, τftv)
    trace ("gen (existentials 1)", Gr.ShowGraph g, γftv, τftv, τ)
    g            ← return (removeRedundant nm g)
    trace ("gen (redundant)", Gr.ShowGraph g, γftv, τftv, τ)
    g            ← eliminateExistentials False nm (g, γftv, τftv)
    trace ("gen (existentials 2)", Gr.ShowGraph g, γftv, τftv, τ)
    (g, γftv, τftv)
                 ← polarizedReduce nm (g, γftv, τftv)
    trace ("gen (polarized)", Gr.ShowGraph g, γftv, τftv, τ)
    g            ← eliminateExistentials False nm (g, γftv, τftv)
    trace ("gen (existentials 3)", Gr.ShowGraph g, γftv, τftv, τ)
    -- Guessing starts here
    (g, γftv, τftv)
                 ← coalesceComponents value (g, γftv, τftv)
    trace ("gen (components)", Gr.ShowGraph g, γftv, τftv, τ)
    -- Guessing ends here
    cγftv        ← ftvV (map snd (Gr.labNodes g), γ)
    qcftv        ← Map.map (const QInvariant) <$> ftvV qc
    let αs       = Map.keysSet $
                     (τftv `Map.union` qcftv) Map.\\ cγftv
        βs       = Map.keysSet $
                     Map.filter isQVariance $
                       Map.unionsWith (⊔) [cγftv, qcftv, τftv]
    (qc, αqs)    ← solveQualifiers value αs βs τftv qc
    let c        = reconstruct g qc
    trace ("gen (finished)", αqs, τ, c)
    return (map fst αqs, map snd αqs, c)
    where
      -- decompose takes a list of subtype constraint pairs and a list
      -- of type variables, and returns when all of the constraint is
      -- reduced to pairs of atoms.
      decompose (c, qc) = execWriterT $ do
        tell (Set.empty, qc)
        mapM_ decompLe c
        where
        a1 ≤! a2 = tell (Set.singleton (a1, a2), [])
        τ1 ⊏! τ2 = tell (Set.empty, [(τ1, τ2)])
        decompLe (τ10, τ20) = do
          τ1 ← deref τ10
          τ2 ← deref τ20
          case (τ1, τ2) of
            (VarTy (FreeVar α), VarTy (FreeVar β))
              | α == β
              → return ()
              | otherwise
              → VarAt α ≤! VarAt β
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
            (VarTy (FreeVar α), ConTy _ _)
              → fail $ "BUG! gen (decompose) saw unexpanded tyvar: " ++ show α
            (ConTy _ _,         VarTy (FreeVar β))
              → fail $ "BUG! gen (decompose) saw unexpanded tyvar: " ++ show β
            (_,                 _)
              → do
                τ1' ← derefAll τ1
                τ2' ← derefAll τ2
                fail $ "Could not unify: " ++ show τ2' ++ " ≤ " ++ show τ1'
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
                          , varianceOf α  /= Just Covariant
                          , varianceOf α' /= Just Contravariant
                          ]
          NM.insMapEdgesM [ (ConAt c1, ConAt c2, ())
                          | (c1, c2) ← Gr.labNodeEdges tyConOrder]
          return ()
      --
      -- Make sure the graph is satisfiable and figure out anything that
      -- is implied by the transitive closure of type constructors
      satisfyTycons nm (g0, γftv0, τftv0) =
        satisfyTycons' (Gr.trcnr g0, γftv0, τftv0)
        where
        satisfyTycons' = iterChanging $ \(g, γftv, τftv) →
          foldM each (g, γftv, τftv) (Gr.labNodes g)
        each (g, γftv, τftv) (n, VarAt α) = do
          let assign c = do
                (γftv, τftv) ← assignTV α (ConAt c) (γftv, τftv)
                let n' = Gr.nmLab nm (ConAt c)
                return (assignNode n n' g, γftv, τftv)
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
              return (g, γftv, τftv)
        each (g, γftv, τftv) (n, ConAt c1) = do
          g ← NM.execNodeMapT nm g $ sequence_
            [ if c1 `tyConLe` c2
                then return ()
                else fail $ "Cannot unify: " ++ c1 ++ " ≤ " ++ c2
            | Just (ConAt c2) ← map (Gr.lab g) (Gr.suc g n)]
          return (g, γftv, τftv)
      --
      -- Eliminate existentially-quantified type variables from the
      -- constraint
      eliminateExistentials trans nm (g, γftv, τftv) = do
        extvs ← getExistentials (g, γftv, τftv)
        trace ("existentials are:", extvs)
        return (Set.fold (eliminateNode trans nm) g extvs)
      -- Get the existential type variables
      getExistentials (g, γftv, τftv) = do
        cftv ← ftvSet (map snd (Gr.labNodes g))
        return (cftv Set.\\ (γftv `Set.union` Map.keysSet τftv))
      -- Remove a node unless it is necessary to associate some of its
      -- neighbors -- in particular, a node with multiple predecessors
      -- but no successor (or dually, multiple successors but no
      -- predecessor) should not be removed.
      eliminateNode trans nm α g =
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
        foldM tryRemove state (findPolar (prj3 state))
          where
          tryRemove state@(g,_,_) (n, α, var) = do
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
          siblings state@(g,_,τftv) (lnode@(n,_), var)
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
      coalesce (n1, lab1) (n2, lab2) (g, γftv, τftv) = do
        case (lab1, lab2) of
          (VarAt α,  _)        → (n1, α) `gets` (n2, lab2)
          (_,        VarAt α)  → (n2, α) `gets` (n1, lab1)
          (ConAt c1, ConAt c2)
            | c1 == c2         →
            return ((n2, lab2), (assignNode n1 n2 g, γftv, τftv))
            | otherwise        →
            fail $ "Could not unify: " ++ c1 ++ " = " ++ c2
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
            VarAt β → Map.insertWith (+) β vs (Map.delete α vmap)
            ConAt _ → Map.delete α vmap
          Nothing → vmap
      -- Coalesce and remove fully-generalizable components
      coalesceComponents value (g, γftv, τftv) = do
        extvs ← getExistentials (g, γftv, τftv)
        let candidates = Set.mapMonotonic VarAt $
                           extvs `Set.union` genCandidates value τftv γftv
            each state component@(_:_)
              | all (`Set.member` candidates) (map snd component)
              = do
                  ((node, _), (g', γftv', τftv'))
                    ← coalesceList state component
                  return (Gr.delNode node g', γftv', τftv')
            each state _
              = return state
        foldM each (g, γftv, τftv) (Gr.labComponents g)
      -- Find the generalization candidates, which are free in τ but
      -- not in γ (restricted further if not a value)
      genCandidates value τftv γftv =
        Map.keysSet (restrict τftv) Set.\\ γftv
          where
          restrict = if value
                       then id
                       else Map.filter (`elem` [-1, 1])
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

-- | Produce a showable representation of an skeletonized subtype
--   constraint
extSkelsM ∷ MonadU tv m ⇒ SkelMap tv m → m (ExtSkels tv)
extSkelsM = mapM each . Map.toList . unSkelMap
  where
    each (α, proxy) = do
      (set, mshape) ← UF.desc proxy
      return (α, Set.toList set, mshape)

-- | Build an internal subtype constraint from an external subtype
--   constraint.
skeletonize ∷ MonadU tv m ⇒
              [(Type tv, Type tv)] → m (SkelMap tv m)
skeletonize sc0 = do
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
          Right _              → fail $ "BUG! skeletonize"
      --
      -- Combine two skeletons
      combiner (αs1, shape1) (αs2, shape2) = do
        shape' ← case (shape1, shape2) of
          (Nothing, _)                  → return shape2
          (_, Nothing)                  → return shape1
          (Just (c1, []), Just (_, [])) → return (Just (c1, []))
          (Just (c1, βs1), Just (c2, βs2))
            | c1 == c2 && length βs1 == length βs2
                                         → do
            sequence_ [ do
                          unless (var ⊑ QInvariant) $ relateTVs β1 β2
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
          (Right τ1'@(ConTy c1 τs1), Right τ2'@(ConTy c2 τs2))
            | c1 == c2 && length τs1 == length τs2 → do
                αs1 ← mapM tvOf τs1
                αs2 ← mapM tvOf τs2
                sequence_ [ when (var /= Omnivariant) $ unifyTVs α1 α2
                          | var ← getVariances c1 (length αs1)
                          | α1  ← αs1
                          | α2  ← αs2 ]
            | otherwise →
                fail $ "Could not unify " ++ show τ1' ++ " and " ++ show τ2'
          _ → fail "BUG! skeletonize (unifyTVs): not yet supported"
      --
  mapM_ addSubtype sc0
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
  let scc = Gr.labScc (gr ∷ Gr tv ())
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
                return .
                   map fst .
                     filter (not . isQVariance . snd) $
                       zip βs' (getVariances c (length βs'))
  expandTVs αs0
  skels' ← readRef rskels
  return skm0 { unSkelMap = skels' }

{-

Rewrite as follows:

  not (q ⊑ q')
  no β in vs'
  ---------------------------
  q vs ⊑ q' vs'   --->   fail

  not (q ⊑ q')
  vs \ vs' = v1 ... vk
  βs' in vs'
  not (null βs')
  ---------------------------------------------------------------
  q vs ⊑ q' vs'   --->  q ⊑ βs' ⋀ v1 ⊑ q' βs' ⋀ ... ⋀ vk ⊑ q' βs'

  q ⊑ q'
  vs \ vs' = v1 ... vk
  βs' in vs'
  -----------------------------------------------------
  q vs ⊑ q' vs'   --->  v1 ⊑ q' βs' ⋀ ... ⋀ vk ⊑ q' βs'

Then we have a constraint of the form:

  v1 ⊑ (q11 βs11) ⊓ ... ⊓ (q1k1 βs1k1)
  ...
  vj ⊑ (qj1 βsj1) ⊓ ... ⊓ (qjkj βsjkj)
  q1 ⊑ βs1
  ...
  qm ⊑ βsm

We can convert it to SAT as follows:

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

-- | Given a list of type variables that need qlit bounds and a set
--   of qualifier inequalities, solve and produce bounds.  Also return
--   any remaining inequalities (which must be satisfiable, but we
--   haven't guessed how to satisfy them yet.)
solveQualifiers      ∷ MonadU tv m ⇒
                       Bool → Set.Set tv → Set.Set tv →
                       Map.Map tv Variance →
                       [(Type tv, Type tv)] →
                       m ([(Type tv, Type tv)], [(tv, QLit)])
solveQualifiers value αs βs τftv qc = do
  let ?deref = readTV
  trace ("solveQ (init)", αs, βs, qc)
  qc             ← stdize qc
  trace ("solveQ (stdize)", qc)
  (αs, τftv, qc) ← substUppers (αs, τftv, qc)
  trace ("solveQ (uppers)", αs, τftv, qc)
  (αs, τftv, qc) ← unifyBounds (αs, τftv, qc)
  trace ("solveQ (unify)", αs, τftv, qc)
  (vmap, βlst)   ← decompose qc
  trace ("solveQ (decompose)", vmap, βlst)
  (αs, τftv, vmap, βlst)
                 ← findBottoms (αs, τftv, vmap, βlst)
  trace ("solveQ (bottoms)", αs, τftv, vmap, βlst)
  (αs, τftv, vmap, βlst)
                 ← runSat (αs, τftv, vmap, βlst) True
  trace ("solveQ (sat)", αs, τftv, vmap, βlst)
  runSat (αs, τftv, vmap, βlst) False
  αs             ← genVars αs τftv
  return (reconstruct αs vmap βlst, getBounds αs vmap)
  where
  stdize qc = foldM each [] qc where
    each qc' (τl, τh) = do
      QExp q1 vs1 ← qualifier τl
      QExp q2 vs2 ← qualifier τh
      let vs1' = Set.fromList (fromVar <$> vs1)
          vs2' = Set.fromList (fromVar <$> vs2)
      if q2 == L || q1 ⊑ q2 && vs1' `Set.isSubsetOf` vs2'
        then return qc'
        else return (((q1, vs1'), (q2, vs2')) : qc')
  --
  unstdize qc = (toQualifierType *** toQualifierType) <$> qc
  --
  substUppers (αs, τftv, qc) =
    subst
        [ α
        | α ← Set.toList (αs Set.\\ Set.unions (snd . fst <$> qc))
        , Map.findWithDefault 0 α τftv ⊑ QContravariant ]
      (repeat (L, Set.empty))
      (αs, τftv, qc)
  --
  unifyBounds state0 = flip iterChanging state0 $ \state@(αs,τftv,qc) → do
    trace ("unifyBounds", state)
    let lbs    = Map.fromListWith joinQ
                   [ (β, (q, vs))
                   | ((q, vs), (U, Set.toList → [β])) ← qc ]
        ubs    = Map.fromListWith meetQ
                   [ (β, (q, vs))
                   | ((U, Set.toList → [β]), (q, vs)) ← qc ]
        look q = Map.findWithDefault (q, Set.empty)
        (pos, neg, inv) = foldr each mempty (Set.toList αs) where
          each α (pos, neg, inv) = case Map.lookup α τftv of
            Just QCovariant     → (α:pos, neg,   inv)
            Just QContravariant → (pos,   α:neg, inv)
            Just QInvariant
              | value
              , Just lb@(q, βs) ← Map.lookup α lbs
              , not (q == U && Set.null βs)
                                → (pos,   neg,   (α,lb):inv)
            _                   → (pos,   neg,   inv)
    case (pos, neg, inv) of
      (_:_, _  , _       ) → subst pos (map (look U <-> lbs) pos) state
      (_  , _  , (β,lb):_) → subst [β] [lb] state
      (_  , β:_, _       ) → subst [β] [look L β ubs] state
      _                    → return state
  --
  subst βs bounds (αs0, τftv0, qc0) = do
    let αs   = foldr Set.delete αs0 βs
        τftv = foldr2 each τftv0 βs bounds where
          each β (_,γs) τftv = case Map.lookup β τftv of
            Just v  → Map.unionWith (+)
                        (Map.delete β τftv)
                        (setToMap (const v) γs)
            Nothing → τftv
    zipWithM_ writeTV βs (map toQualifierType bounds)
    qc ← stdize (unstdize qc0)
    return (αs, τftv, qc)
  --
  joinQ (q1,βs1) (q2,βs2) = case q1 ⊔ q2 of
    L → (L, Set.empty)
    q → (q, βs1 `Set.union` βs2)
  meetQ (q1,βs1) (q2,βs2) = case q1 ⊓ q2 of
    L → (L, Set.empty)
    q → (q, βs1 `Set.intersection` βs2)
  --
  decompose qc = foldM each (Map.empty, []) qc where
    each (vmap, βlst) ((q1,βs1), (q2,βs2)) = do
      let βs' = Set.filter (`Set.member` βs) βs2
      when (not (q1 ⊑ q2) && Set.null βs') $
        fail $ "Qualifier inequality unsatisfiable: " ++
               show (toQualifierType (q1,βs1)) ++
               " ⊑ " ++ show (toQualifierType (q2,βs2))
      let βdiff = Set.toList (βs1 Set.\\ βs2)
          βbnds = [ (β, [(q2, βs')]) | β ← βdiff, q2 /= L ]
          vmap' = foldr (uncurry (Map.insertWith (++))) vmap βbnds
          βlst' = if q1 ⊑ q2
                    then βlst
                    else (q1, βs') : βlst
      return (vmap', βlst')
  --
  findBottoms = iterChanging $ \(αs, τftv, vmap, βlst) →
    doSubst
        [ (α, U)
        | (α, ubs) ← Map.toList vmap
        , Set.member α αs
        , Set.member α βs
        , maybe True (== QCovariant) (Map.lookup α τftv)
        , bigMeet [ ql | (ql, γs) ← ubs, Set.null γs ] == U ]
      (αs, τftv, vmap, βlst)
  --
  runSat (αs, τftv, vmap, βlst) doIt = do
    let formula = toSat vmap βlst
        sats    = SAT.solve =<< SAT.assertTrue formula SAT.newSatSolver
        αs'     = Set.toList (αs `Set.intersection` βs)
        finish  = if doIt then doSubst else const return
    trace ("runSat", formula, sats)
    γqs ← case sats of
      []    → fail "Qualifier constraints unsatisfiable"
      sat:_ → return
        [ (α, lb)
        | α  ← αs'
        , let lb = satVarLB α sat
        , lb /= U || Map.lookup α τftv == Just Covariant ]
    finish γqs (αs, τftv, vmap, βlst)
  --
  toSat vmap βlst = foldr (SAT.:&&:) SAT.Yes $
      [ (πr q ==> πr (U,βs)) SAT.:&&: (πa q ==> πa (U,βs))
      | (q, βs) ← βlst ]
    ++
      [ (πr (FreeVar α) ==> πr (q,αs)) SAT.:&&: (πa (FreeVar α) ==> πa (q,αs))
      | (α, qes) ← Map.toList vmap
      , (q, αs)  ← qes
      , α `Set.member` βs ]
    where
      p ==> q = SAT.Not p SAT.:||: q
  --
  doSubst γqs (αs0, τftv0, vmap0, βlst0) = do
    mapM_ (uncurry writeTV . second toQualifierType) γqs
    let γmap = Map.fromList γqs
        γset = Map.keysSet γmap
        αs   = αs0 Set.\\ γset
        τftv = τftv0 Map.\\ γmap
        vmap = vmap0 Map.\\ γmap
        βlst = [ (q, βs')
               | (q, βs) ← βlst0
               , let βs' = βs Set.\\ γset
               , not (Set.null βs') ]
    return (αs, τftv, vmap, βlst)
  --
  genVars αs τftv = return $ Set.filter keep αs where
    keep α = case Map.lookup α τftv of
      Just v  → value || v `elem` [-2,-1,1,2]
      Nothing → False
  --
  reconstruct αs vmap βlst =
    map (second clean) $
        [ (fvTy v, (q, βs))
        | (v, qes) ← Map.toList vmap
        , v `Set.notMember` αs
        , (q, βs) ← qes ]
      ++
        [ (toQualifierType q, (U, βs))
        | (q, βs) ← βlst ]
    where
    clean (q, βs) = toQualifierType (q, (Set.\\ αs) βs)
  --
  getBounds αs vmap = map (id &&& getBound) (Set.toList αs) where
    getBound α = case Map.lookup α vmap of
      Nothing  → L
      Just qes → bigMeet (map fst qes)
  --
  fromVar (FreeVar α) = α
  fromVar _           = error "BUG! solveQualifiers got bound tyvar"

setToMap   ∷ (k → a) → Set.Set k → Map.Map k a
setToMap f = Map.fromDistinctAscList . map (id &&& f) . Set.toAscList

{-
  #0 → #3

  expand:

  #1 → #1 -#1> #1 ≤ (#2 → #2) -L> #3

  1 ← #12 -#13> #14

  (#12 -#13> #14) → (#12 -#13> #14) -#13> (#12 -#13> #14)
    ≤ (#2 → #2) -L> #3

  3 ← #15 -#16> #17
  (#0 → #15 -#16> #17)

  (#12 -#13> #14) →   (#12 -#13> #14) -#13> (#12 -#13> #14)
  ≤
  (#2  →      #2) -L> #15             -#16> #17

  15 ← #18 -#19> #20
  (#0 → (#18 -#19> #20) -#16> #17)

  (#12 -#13> #14) →  (#12 -#13> #14) -#13> (#12 -#13> #14)
  ≤
  (#2  →     #2) -L> (#18 -#19> #20) -#16> #17

  17 ← #21 -#22> #23
  (#0 → (#18 -#19> #20) -#16> (#21 -#22> #23))

  (#12 -#13> #14) →  (#12 -#13> #14) -#13> #12 -#13> #14
  ≤
  (#2  →     #2) -L> (#18 -#19> #20) -#16> #21 -#22> #23

  decompose:

  2≤14, 12≤2, 20≤14, 12≤18, 21≤12, 14≤23
  U⊑13, U⊑L, 19⊑13, 13⊑16, 13⊑22
  (#0 → (#18 -#19> #20) -#16> (#21 -#22> #23))
-}

class SATable a where
  πa ∷ a → SAT.Boolean
  πr ∷ a → SAT.Boolean

instance SATable QLit where
  πr ql | R ⊑ ql    = SAT.Yes
        | otherwise = SAT.No
  πa ql | A ⊑ ql    = SAT.Yes
        | otherwise = SAT.No

instance Tv v ⇒ SATable (Var v) where
  πr (FreeVar β) = SAT.Not (SAT.Var (2 * tvUniqueID β))
  πr _           = SAT.No
  πa (FreeVar β) = SAT.Not (SAT.Var (2 * tvUniqueID β + 1))
  πa _           = SAT.No

instance (Tv v, SATable (Var v)) ⇒ SATable (QLit, Set.Set v) where
  πr (q, vs) = πr (QExp q (FreeVar <$> Set.toList vs))
  πa (q, vs) = πa (QExp q (FreeVar <$> Set.toList vs))

instance Tv v ⇒ SATable (QExp v) where
  πr (QExp ql vs) = foldr (SAT.:||:) (πr ql) (map πr vs)
  πa (QExp ql vs) = foldr (SAT.:||:) (πa ql) (map πa vs)

-- | Given a type variable and a SAT solution, return a lower bound
--   for that type variable as implied by the solution.
satVarLB ∷ Tv v ⇒ v → SAT.SatSolver → QLit
satVarLB β solver = case (mbr, mba) of
  (Just False, Just False) → L
  (Just False, _         ) → R
  (_         , Just False) → A
  _                        → U
  where mbr = SAT.lookupVar βr solver
        mba = SAT.lookupVar βa solver
        βr  = 2 * tvUniqueID β
        βa  = 2 * tvUniqueID β + 1

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

