{-#
  LANGUAGE
    ImplicitParams,
    ScopedTypeVariables,
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
  infer0, infer,
  -- * Testing
  -- ** Interactive testing
  check, showInfer,
  -- ** Unit tests
  inferTests, tests,
) where

import qualified Data.Map   as Map
import qualified Test.HUnit as T
import Control.Monad.RWS    as RWS

import MonadU
import Constraint
import Syntax hiding (tests)
import Util

---
--- Inference
---

type Γ tv = [[Type tv]]
type Δ tv = Map.Map Name (Type tv)

-- | Infer the type of a term, given a type context
infer0 ∷ forall m tv. (MonadU tv m, Show tv, Tv tv) ⇒
         Γ tv → Term Empty → m (Type tv)
infer0 γ e = do
  (τ, c)  ← infer mempty γ e
  (τ', _) ← gen (syntacticValue e) (c ∷ SubtypeConstraint tv) γ τ
  return τ'

-- | To infer a type and constraint for a term
infer ∷ (MonadU tv m, Constraint c tv) ⇒
        Δ tv → Γ tv → Term Empty → m (Type tv, c)
infer δ γ e0 = case e0 of
  AbsTm π e                     → do
    α ← newTVTy
    (δ', c1, τs) ← inferPatt δ π α
    (τ2, c2)     ← infer δ' (τs:γ) e
    return (α ↦ τ2, c1 ⋀ c2)
  LetTm rec π e1 e2    → do
    α ← newTVTy
    (δ', c0, τs0) ← inferPatt δ π α
    (τ1, c1)      ← infer δ' (if rec then τs0:γ else γ) e1
    let genLoop []     σs c = return (reverse σs, c)
        genLoop (τ:τs) σs c = do
          (σ, c') ← gen (syntacticValue e1) c ((τs++σs):γ) τ
          genLoop τs (σ:σs) c'
    (σs, c1') ← genLoop τs0 [] (c0 ⋀ c1 ⋀ τ1 ≤ α ⋀
                                if rec then α ≤ τ1 else (⊤))
    (τ2, c2)  ← infer δ' (σs:γ) e2
    return (τ2, c1' ⋀ c2)
  VarTm (FreeVar ff)            → elimEmpty ff
  VarTm (BoundVar i j _)        → do
    τ ← inst (γ !! i !! j)
    return (τ, (⊤))
  ConTm n es                    → do
    (τs, cs) ← unzip <$> mapM (infer δ γ) es
    return (ConTy n τs, mconcat cs)
  AppTm e1 e2                   → do
    (τ1, c1) ← infer δ γ e1
    (τ2, c2) ← infer δ γ e2
    α        ← newTVTy
    return (α, c1 ⋀ c2 ⋀ τ1 ≤ τ2 ↦ α)
  AnnTm e annot                 → do
    (δ', τ', _) ← instAnnot δ annot
    (τ, c)      ← infer δ' γ e
    return (τ', c ⋀ τ ≤ τ')

-- | Instantiate a prenex quantifier
inst ∷ MonadU tv m ⇒ Type tv → m (Type tv)
inst σ0 = do
  σ ← deref σ0
  case σ of
    QuaTy AllQu ns τ → do
      αs ← replicateM (length ns) newTVTy
      return (openTy 0 αs τ)
    τ → return τ

-- | Given a type variable environment and a pattern, compute an updated
--   type variable environment, a type for the whole pattern, a
--   constraint, and a type for each variable bound by the pattern.
inferPatt ∷ (MonadU tv m, Constraint c tv) ⇒
           Δ tv → Patt Empty → Type tv →
           m (Δ tv, c, [Type tv])
inferPatt δ0 π0 τ0 = do
  (τs, δ, c) ← runRWST (loop π0 τ0) () δ0
  return (δ, c, τs)
  where
  loop (VarPa _)       τ = return [τ]
  loop WldPa           _ = return []
  loop (ConPa name πs) τ = do
    αs ← replicateM (length πs) (lift newTVTy)
    tell (τ ≤ ConTy name αs)
    concat <$> zipWithM loop πs αs
  loop (AnnPa π annot) τ = do
    δ ← get
    (δ', τ', _) ← lift (instAnnot δ annot)
    put δ'
    tell (τ ≤ τ')
    loop π τ'

-- | Given a tyvar environment (mapping some-bound names to tyvars) and
--   an annotation, create new universal type variables for any new
--   some-bound names in the annotation and update the environment
--   accordingly. Return the annotation instantiated to a type and the
--   list of new universal tyvars.
instAnnot ∷ MonadU tv m ⇒
            Δ tv → Annot →
            m (Δ tv, Type tv, [Type tv])
instAnnot δ (Annot names σ0) = do
  αs ← mapM eachName names
  let δ' = foldr2 insert δ names αs
      σ  = totalSubst names αs =<< σ0
  trace ("instAnnot", δ, δ', σ, αs)
  return (δ', σ, αs)
  where
    insert ('_':_) = const id
    insert k       = Map.insert k
    eachName name  = maybe newTVTy return (Map.lookup name δ)

---
--- Testing functions
---

check ∷ String → IO (Type String)
check e = case showInfer (read e) of
  Left err → fail err
  Right τ  → return τ

showInfer ∷ Term Empty → Either String (Type String)
showInfer e = runU $ do
  τ ← infer0 [map (fmap elimEmpty) γ0] e
  stringifyType τ

stringifyType ∷ (MonadU s m, Show s) ⇒ Type s → m (Type String)
stringifyType = foldType QuaTy bvTy (fvTy . show) ConTy where ?deref = readTV

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

-}

tests, inferTests ∷ IO ()

inferTests = tests
tests      = do
  syntaxTests
  T.runTestTT inferFnTests
  return ()

inferFnTests ∷ T.Test
inferFnTests = T.test
  [ "A"         -: "A"
  , "A B C"     -: "A B C"
  , "λx.x"      -: "∀ α. α → α"
  , "λa.id id"  -: "∀ α β. α → β → β"
  , "λx.choose id"
                -: "∀ β α. β → (α → α) → α → α"
  , "λx.choose (id : α → α)"
                -: "∀ α β. α → (β → β) → (β → β)"
  {-
  , "λ(f : ∀ α. α → α). P (f A) (f B)"
                -: "(∀ α. α → α) → P A B"
  -}
  , te "λf. P (f A) (f B)"
  {-
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
  -}
  , pe "λ(A x x). B"
  , "λ(A a (B b c) (C d (D e f g))). E"
                -: "∀ α β γ δ e f g. A α (B β γ) (C δ (D e f g)) → E"
  {-
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
  -}
  ]
  where
  a -: b = T.assertBool ("⊢ " ++ a ++ " : " ++ b)
             (showInfer (read a) == Right (fmap elimEmpty (read b)))
  te a   = T.assertBool ("¬⊢ " ++ a)
             (either (const True) (const False) (showInfer (read a)))
  pe a   = T.assertBool ("expected syntax error: " ++ a)
             (length (reads a ∷ [(Term Empty, String)]) /= 1)

