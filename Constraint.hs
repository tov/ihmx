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
  --
  -- | Figure out which variables to generalize in a piece of syntax
  gen'       ∷ (MonadU r m, Ftv γ r, Ftv a r,
                Derefable a m, Standardizable a r, Show a) ⇒
               Bool → c → γ → a → m ([r], [QLit], c)
  -- | Generalize a type under a constraint and environment,
  --   given whether the the value restriction is satisfied or not
  gen        ∷ (MonadU r m, Ftv γ r) ⇒
               Bool → c → γ → Type r → m (Type r, c)
  gen value c0 γ τ = do
    (αs, qls, c) ← gen' value c0 γ τ
    σ ← standardizeMus =<< closeWithQuals qls AllQu αs <$> derefAll τ
    return (σ, c)
  -- | Generalize a list of types together.
  genList    ∷ (MonadU r m, Ftv γ r) ⇒
               Bool → c → γ → [Type r] → m ([Type r], c)
  genList value c0 γ τs = do
    (αs, qls, c) ← gen' value c0 γ τs
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
  gen' value (SC c qc) γ τ = do
    let ?deref = readTV
    trace ("gen (begin)", SC c qc, τ)
    c            ← unrollRecs c
    trace ("gen (unrollRecs)", c)
    skm1         ← skeletonize c
    trace ("gen (skeletonized)", skm1, (c, qc), τ)
    (expandSks, skipSks)
                 ← occursCheck skm1
    (_, noX)     ← expand skm1 expandSks skipSks
    trace ("gen (expand)", noX, (c, qc), τ)
    (c, qc)      ← decompose noX (c, qc)
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
    (qc, αqs, τ) ← solveQualifiers value αs βs qc τ
    let c        = reconstruct g qc
    trace ("gen (finished)", αqs, τ, c)
    trace (Here ())
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
            (RecTy _ τ1',       RecTy _ τ2')
              → decompLe (τ1', τ2')
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
        let cftv = Set.fromList [ α | (_, VarAt α) ← Gr.labNodes g ]
        return (cftv Set.\\ (γftv `Set.union` Map.keysSet τftv))
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
          _                    →
            fail $ "Could not unify: " ++ show lab1 ++ " = " ++ show lab2
        where
          (n1', α) `gets` (n2', lab') = do
            ftv2 ← ftvSet lab'
            if α `Set.member` ftv2
              then return ((n2', lab'), (g, γftv, τftv))
              else do
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
        (,) <$> assignFtvSet α atom γftv <*> assignFtvMap α atom τftv
      -- Given two type variables, where α ← atom, update a set of free
      -- type variables accordingly
      assignFtvSet α atom set =
        if Set.member α set
          then case atom of
            VarAt β → return $ Set.insert β set'
            ConAt _ → return set'
          else return set
        where set' = Set.delete α set
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
      unSkelMap   ∷ Map.Map tv (Skeleton tv m)
    }
type Skeleton tv m = UF.Proxy (URef m) (Set.Set tv, Shape tv m)

data Shape tv m
  = ConShape Name [Skeleton tv m]
  | RowShape Name (Skeleton tv m) (Skeleton tv m)
  | NoShape

type ExtSkels tv = [(tv, [tv], Maybe (Type tv))]

skeletonTV ∷ MonadU tv m ⇒ Skeleton tv m → m tv
skeletonTV = Set.findMin . fst <$$> UF.desc

shapeToType ∷ forall tv m. MonadU tv m ⇒
              Shape tv m → Maybe (Type tv)
shapeToType shape = unsafePerformU (shapeToTypeM shape ∷ m (Maybe (Type tv)))

shapeToTypeM ∷ MonadU tv m ⇒ Shape tv m → m (Maybe (Type tv))
shapeToTypeM shape = do
  case shape of
    ConShape n sks     → Just . ConTy n <$> mapM conv sks
    RowShape n sk1 sk2 → Just <$$> RowTy n <$> conv sk1 <*> conv sk2
    NoShape            → return Nothing
  where conv = fvTy <$$> skeletonTV

extSkels ∷ MonadU tv m ⇒ SkelMap tv m → ExtSkels tv
extSkels = unsafePerformU . extSkelsM

-- | Produce a showable representation of an skeletonized subtype
--   constraint
extSkelsM ∷ MonadU tv m ⇒ SkelMap tv m → m (ExtSkels tv)
extSkelsM = mapM each . Map.toList . unSkelMap
  where
    each (α, proxy) = do
      (set, shape) ← UF.desc proxy
      τ ← shapeToTypeM shape
      return (α, Set.toList set, τ)

instance (Tv tv, MonadU tv m) ⇒ Show (Shape tv m) where
  showsPrec p = maybe (showChar '_') (showsPrec p) . shapeToType

instance (Tv tv, MonadU tv m) ⇒ Show (SkelMap tv m) where
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
skeletonize ∷ MonadU tv m ⇒ [(Type tv, Type tv)] → m (SkelMap tv m)
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
occursCheck ∷ ∀ tv m. MonadU tv m ⇒
              SkelMap tv m → m ([Skeleton tv m], [Skeleton tv m])
occursCheck skm = do
  gr ← foldM addSkel Gr.empty (Map.toList (unSkelMap skm))
  let scc = Gr.labScc (gr ∷ Gr (Skeleton tv m) Bool)
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
expand ∷ MonadU tv m ⇒
         -- | the skeletons
         SkelMap tv m →
         -- | skeletons in order of expansion
         [Skeleton tv m] →
         -- | skeletons not to expand
         [Skeleton tv m] →
         m (SkelMap tv m, Set.Set tv)
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
              βs' ← mapM newSkelTV sks
              writeTV α' (ConTy c (map fvTy βs'))
            RowShape n sk1 sk2 → do
              β1 ← newSkelTV sk1
              β2 ← newSkelTV sk2
              writeTV α' (RowTy n (fvTy β1) (fvTy β2))
      newSkelTV skel = do
        β ← newTV
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
      sq_βs    ∷ !(Set.Set tv),
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
  ∷ (MonadU tv m, Derefable a m, Standardizable a tv, Ftv a tv, Show a) ⇒
    Bool → Set.Set tv → Set.Set tv → [(Type tv, Type tv)] →
    a → m ([(Type tv, Type tv)], [(tv, QLit)], a)
solveQualifiers value αs βs qc τ = do
  let ?deref = readTV
  trace ("solveQ (init)", αs, βs, qc)
  -- Clean up the constraint, standardize types to qualifier form, and
  -- deal with trivial stuff right away:
  qc             ← stdize qc
  trace ("solveQ (stdize)", qc)
  -- Decompose implements DECOMPOSE, TOP-SAT, BOT-SAT, and BOT-UNSAT.
  τftv           ← ftvV τ
  state          ← decompose qc SQState {
                     sq_αs   = αs,
                     sq_βs   = βs,
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
      QExp q1 γs1 ← qualifier τl
      QExp q2 γs2 ← qualifier τh
      let qe1 = QE q1 $ Set.fromList (fromVar <$> γs1)
          qe2 = QE q2 $ Set.fromList (fromVar <$> γs2)
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
          βs' = γs2 `Set.intersection` sq_βs state
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
            | γ `Set.member` sq_βs state = qemSingleton (QE q2 γs2)
            | otherwise                  = qemSingleton (QE q2 βs')
      return state {
               sq_βlst = fβlst (sq_βlst state),
               sq_vmap = fvmap (sq_vmap state)
             }
  --
  -- Standardize the qualifiers in the type
  stdizeType state = do
    τ    ← derefAll (sq_τ state)
    let meet = bigMeet . map qeQLit . filter (Set.null . qeQSet) . unQEMeet
        qm   = Map.map meet (sq_vmap state)
        τ'   = standardizeQuals qm τ
    trace ("stdizeType", τ, τ', qm)
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
      | (β, QEMeet [QE U βs]) ← Map.toAscList
           (sq_vmap state `Map.intersection` setToMap () (sq_βs state))
      , Set.null βs ]
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
                        (sq_αs state `Set.intersection` sq_βs state)
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
          δ' ← newTV
          return (δ', (δ, QE q (Set.insert δ' βs)))
      | (δ, qe@(QE q βs)) ← Map.toAscList inv
      , qe /= minBound ]
    subst "substPosInv"
          state {
            sq_αs = sq_αs state `Set.union` δ's,
            sq_βs = sq_βs state `Set.union` δ's
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
        sanitize _    (acc:_) [] -- XXX one at a time
          = unsafeSubst state (Map.fromDistinctAscList (return acc))
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
    let vmap = Map.fromDistinctAscList
          [ (γ, qem'')
          | (γ, qem) ← Map.toAscList (sq_vmap state)
          , let γqes' = γqes `Map.intersection` ftvPure qem
                qem'  = foldr (uncurry qemSubst) qem (Map.toList γqes')
                qem'' = QEMeet [ mkQE γ q γs
                               | QE q γs ← unQEMeet qem'
                               , Set.notMember γ γs ] ]
        γmap = Map.mapWithKey each γqes
          where each γ (QE q γs) = mkQE γ q γs
        mkQE γ q γs = QE q $ if γ `Set.member` sq_βs state
                               then γs
                               else γs `Set.intersection` sq_βs state
    βlst ← sequence $ do
      (q0, βs0) ← sq_βlst state
      let γmap'     = γmap `Map.intersection` setToMap () βs0
          QE q' βs' = bigJoin (Map.elems γmap')
          q''       = q0 \-\ q'
          βs''      = (βs0 Set.\\ Map.keysSet γmap') `Set.union` βs'
      guard (q'' /= U)
      return $ if Set.null βs''
        then fail $ "Qualifier error: " ++ show q'' ++ " /⊑ U."
        else return (q'', βs'')
    state ← decompose
      [ (qe, qe')
      | (qe, qem) ← Map.elems (Map.intersectionWith (,) γmap vmap)
      , qe'       ← unQEMeet qem ]
      state {
        sq_αs   = sq_αs state Set.\\ Map.keysSet γmap,
        sq_βs   = sq_βs state Set.\\ Map.keysSet γmap,
        sq_τftv = Map.foldrWithKey (\γ (QE _ γs) → substMap γ γs)
                                   (sq_τftv state) γqes,
        sq_βlst = βlst,
        sq_vmap = vmap Map.\\ γmap
      }
    trace ("subst", γqes, state)
    return state
  --
  -- As a last ditch effort, use a simple SAT solver to find a
  -- decent literal-only substitution.
  runSat state doIt = do
    let formula = toSat state
        sols    = SAT.solve =<< SAT.assertTrue formula SAT.newSatSolver
        δs      = sq_αs state `Set.intersection` sq_βs state
    trace ("runSat", formula, sols)
    case sols of
      []  → fail "Qualifier constraints unsatisfiable"
      sat:_ | doIt
          → subst "sat" state =<<
              Map.fromDistinctAscList <$> sequence
                [ do
                    βs ← case var of
                      QInvariant → Set.singleton <$> newTV
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
      , α `Set.member` βs ]
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

{0≤5 ⋀ 0≤9 ⋀ REC([ A: #5 | #6 ])≤3 ⋀ REC([ B: #4 | #3 ])≤9}
{0≤9 ⋀ REC([ A: #0 | #6 ])≤3 ⋀ REC([ B: #4 | #3 ])≤9}
{REC([ A: #0 | #6 ])≤3 ⋀ REC([ B: #4 | #3 ])≤0}
#0 <- mu α. REC([ B: #4 | [ A: α | #6 ] ])

data α t = S of α t | Z of α

α t = mu β. [ S: β | Z: α ]

((let rec f = λ x. match x with `Z f → f M : M | `S y → f y in f) (let rec x = λ _. choose (`Z (λ M.M)) (`S (x U)) in x U))

-}

