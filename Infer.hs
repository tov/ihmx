{-#
  LANGUAGE
    FlexibleContexts,
    FlexibleInstances,
    FunctionalDependencies,
    ImplicitParams,
    MultiParamTypeClasses,
    NoImplicitPrelude,
    ParallelListComp,
    ScopedTypeVariables,
    TupleSections,
    UndecidableInstances,
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

   - Scoped type variables: all some-bound type variables in an
     expression denote the same unification variable.

   - Binder patterns with type annotations for λ and let

   - Annotation propagation for let patterns:

        let x : π = e1 in e2
          ⇒
        let x : π = (e1 : π) in e2

   - Let rec.

   - Existentials with automatic unpack/pack.

   - Substructural types and subtyping.
-}
module Infer (
  inferTm, infer,
  -- * Testing
  -- ** Interactive testing
  check, showInfer,
  -- ** Unit tests
  inferTests, tests,
) where

import qualified Data.Map   as Map
import qualified Data.Set   as Set
import qualified Test.HUnit as T

import Data.Time.Clock.POSIX (POSIXTime, getPOSIXTime)
import System.IO (stderr, hPutStrLn)
import System.Timeout (timeout)
import qualified Text.PrettyPrint as Ppr

import Constraint
import Env
import qualified Rank
import Syntax hiding (tests)
import TV
import Ppr
import Util

---
--- Inference
---

-- | Infer the type of a term, given a type context
inferTm ∷ (MonadTV tv r m, Show tv, Tv tv) ⇒
          Γ tv → Term Empty → m (Type tv, String)
inferTm γ e = do
  traceN 2 ("inferTm", γ, e)
  runConstraintT $ do
    δ ← instAnnotTVs (ftvPure e)
    τ ← infer (request AllQu ExQu) δ γ e Nothing
    σ ← generalize False (rankΓ γ) τ
    c ← showConstraint
    return (σ, c)

---
--- Type inference for terms and patterns, including matching and
--- application terms
---

-- | To infer the type of a term.
infer ∷ MonadC tv r m ⇒
        -- | Which quantifiers are requested on the resulting type, which
        --   may result in generalization or instantiation.
        Request tv →
        -- | The type annotation environment mapping names of some-bound
        --   type variables to unification variables.
        Δ tv →
        -- | The type environment mapping term variables to types.
        Γ tv →
        -- | The term to type.
        Term Empty →
        -- | Maybe the expected result type, used for annotation
        --   propagation.
        Maybe (Type tv) →
        m (Type tv)
infer φ0 δ γ e0 mσ0 = do
  traceN 1 (TraceIn ("infer", φ0, γ, e0, mσ0))
  mσ ← mapM substDeep mσ0
  let φ = maybe id prenexFlavors mσ φ0
  σ  ← case e0 of
    AbsTm π e                     → do
      [mσ1,_,mσ2]      ← splitCon (<:) mσ "->" 3
      ((σ1, σs), αs) ← collectTV $
        inferPatt δ π mσ1 (countOccsPatt π e)
      αs'              ← filterM (isMonoType . fst) ((fvTy &&& tvDescr) <$> αs)
      γ'               ← γ &+&! π &:& σs
      σ2               ← infer (request ExQu γ αs) δ γ' e mσ2
      qe               ← arrowQualifier γ (AbsTm π e)
      sequence_
        [ unlessM (isMonoType α) $
            fail $ "Type error: Used " ++ descr ++ " polymorphically"
        | (α, descr) ← αs' ]
      maybeGen e0 φ γ (arrTy σ1 qe σ2)
    LetTm π e1 e2                 → do
      mσ1              ← extractPattAnnot δ π
      ((_, σs), αs)    ← collectTV $ do
        σ1               ← infer (request AllQu ExQu) δ γ e1 mσ1
        inferPatt δ π (Just σ1) (countOccsPatt π e2)
      γ'               ← γ &+&! π &:& σs
      infer (request φ γ αs) δ γ' e2 mσ
    MatTm e1 bs                   → do
      (σ1, αs)         ← collectTV (infer request δ γ e1 Nothing)
      inferMatch (request φ γ αs) δ γ σ1 bs mσ
    RecTm bs e2                   → do
      let (ns, es) = unzip bs
          mas      = getTermAnnot <$> es
      σs           ← mapM (maybe newTVTy (instAnnot δ)) mas
      γ'           ← γ &+&! ns &:& σs
      σs'          ← sequence
        [ do
            unless (syntacticValue ei) $
              fail $ "In let rec, binding for ‘" ++ ni ++
                     "’ is not a syntactic value"
            σi ⊏: U
            infer request δ γ' ei (σi <$ mai)
        | (ni, ei) ← bs
        | mai      ← mas
        | σi       ← σs ]
      zipWithM (<:) σs' σs
      σs''             ← generalizeList True (rankΓ γ) σs'
      γ'               ← γ &+&! ns &:& σs''
      infer φ δ γ' e2 mσ
    VarTm n                       → maybeInstGen e0 φ γ =<< γ &.& n
    ConTm n es                    → do
      mσs              ← splitCon (flip (<:)) mσ n (length es)
      ρs               ← zipWithM (infer request δ γ) es mσs
      maybeGen e0 φ γ (ConTy n ρs)
    LabTm b n                     → do
      instantiate . elimEmptyF . read $
        "∀α r. " ++ (if b then 'α' else 'r') : " → [ " ++ n ++ " : α | r ]"
    AppTm _ _                     → do
      let (e, es) = unfoldApp e0
      (σ, αs)          ← collectTV $ do
        σ1               ← infer request δ γ e Nothing
        inferApp δ γ σ1 es
      maybeInstGen e0 (request φ γ αs) γ σ
    AnnTm e annot                 → do
      -- infer φ δ γ (AppTm (AbsTm (AnnPa (VarPa "x") annot) (VarTm "x")) e) mσ
      σ                ← instAnnot δ annot
      αs               ← collectTV_ . withPinnedTVs σ $ do
        σ'               ← infer request δ γ e (Just σ)
        σ' ≤ σ
      maybeGen e0 (request φ γ αs) γ σ
  traceN 1 (TraceOut ("infer", σ))
  return σ

-- | To infer a type of a match form, including refinement when matching
--   open variants.
inferMatch ∷ MonadC tv r m ⇒
             Request tv → Δ tv → Γ tv → Type tv →
             [(Patt Empty, Term Empty)] → Maybe (Type tv) → 
             m (Type tv)
inferMatch _ _ _ _ [] _ = newTVTy
inferMatch φ δ γ σ ((InjPa n πi, ei):bs) mσ | totalPatt πi = do
  β               ← newTVTy
  mσ12            ← extractLabel n <$> substDeep σ
  (σ1, σ2)        ← case mσ12 of
    Just σ12 → return σ12
    Nothing  → do
      σ1 ← newTVTy
      σ2 ← newTVTy
      σ =: RowTy n σ1 σ2
      return (σ1, σ2)
  ((_, σs), αs)   ← collectTV $ inferPatt δ πi (Just σ1) (countOccsPatt πi ei)
  γ'              ← γ &+&! πi &:& σs
  σi              ← infer (request φ γ αs) δ γ' ei mσ
  σk              ← if null bs
                      then do σ2 <: endTy; return β
                      else inferMatch φ δ γ σ2 bs mσ
  mapM_ (σ ⊏:) (countOccsPatt πi ei)
  if (isAnnotated ei)
    then σi <: β
    else σi ≤  β
  σk <: β
  return β
inferMatch φ δ γ σ ((πi, ei):bs) mσ = do
  β               ← newTVTy
  ((_, σs), αs)   ← collectTV $ inferPatt δ πi (Just σ) (countOccsPatt πi ei)
  γ'              ← γ &+&! πi &:& σs
  σi              ← infer (request φ γ αs) δ γ' ei mσ
  σk              ← inferMatch φ δ γ σ bs mσ
  if (isAnnotated ei)
    then σi <: β
    else σi ≤  β
  σk <: β
  return β

-- | Given a type variable environment, a pattern, maybe a type to
--   match, and a list of how each bound variable will be used,
--   and compute an updated type variable environment,
--   a type for the whole pattern, a type for each variable bound by
--   the pattern, and a list of some-quantified type variables.
--   PRECONDITION: mσ0 is fully substituted
inferPatt ∷ MonadC tv r m ⇒
            Δ tv → Patt Empty → Maybe (Type tv) → [Occurrence] →
            m (Type tv, [Type tv])
inferPatt δ π0 mσ0 occs = do
  traceN 1 (TraceIn ("inferPatt", δ, π0, mσ0, occs))
  (σ, σs) ← runWriterT (loop π0 mσ0)
  zipWithM_ (⊏:) σs occs
  traceN 1 (TraceOut ("inferPatt", σ, σs))
  return (σ, σs)
  where
  loop (VarPa n)       mσ = do
    σ ← maybeFresh mσ $ "unannotated parameter ‘" ++ n ++ "’"
    bind σ
    return σ
  loop WldPa           mσ = do
    σ ← maybeFresh mσ $ "unannotated wildcard pattern"
    return σ
  loop (ConPa name πs) mσ = do
    mαs ← splitCon (<:) mσ name (length πs)
    σs  ← zipWithM loop πs mαs
    mσ ?≤ ConTy name σs
  loop (InjPa name π)  mσ = do
    (mα, mβ) ← splitRow (<:) mσ name
    σ1 ← loop π mα
    σ2 ← maybeFresh mβ $ ""
    mσ ?≤ RowTy name σ1 σ2
  loop (AnnPa π annot) mσ = do
    σ' ← instAnnot δ annot
    σ  ← mσ ?≤ σ'
    loop π (Just σ')
    return σ
  --
  bind τ         = tell [τ]
  maybeFresh mσ doc = case mσ of
    Nothing → newTVTy' doc
    Just σ  → do
      σ' ← substRoot σ
      case σ' of
        VarTy (FreeVar α) → reportTV α
        _ → return ()
      return σ'
  --
  Nothing ?≤ σ' = return σ'
  Just σ  ?≤ σ' = do σ ≤ σ'; return σ

inferApp ∷ MonadC tv r m ⇒
           Δ tv → Γ tv → Type tv → [Term Empty] → m (Type tv)
inferApp δ γ ρ e1n = do
  traceN 2 (TraceIn ("inferApp", γ, ρ, e1n))
  (σ1m, σ) ← funmatchN (length e1n) ρ
  withPinnedTVs ρ $
    subsumeN [ -- last arg to infer (Just σi) is for
               -- formal-to-actual propagation
               (σi, do
                      σi' ← infer (request ExQu) δ γ ei (Just σi)
                      traceN 2 ("subsumeI", i, ei, σi', σi)
                      if isAnnotated ei
                        then σi' <: σi
                        else σi' ≤  σi)
             | i  ← [0 ∷ Int ..]
             | σi ← σ1m
             | ei ← e1n ]
  if length σ1m < length e1n
    then do
      ρ' ← instantiate σ
      inferApp δ γ ρ' (drop (length σ1m) e1n)
    else do
      traceN 2 (TraceOut ("inferApp", σ))
      return σ

--
-- Inference helpers
--

-- | Determine which quantifiers may appear at the beginning of
--   a type scheme, given a list of quantifiers that may be presumed
--   to belong to an unsubstituted variable.
prenexFlavors ∷ Type tv → Request tv' → Request tv'
prenexFlavors σ φ =
  case σ of
    QuaTy ExQu _ (QuaTy AllQu _ _) → φ { rqEx = True, rqAll = True }
    QuaTy ExQu _ (VarTy _)         → φ { rqEx = True }
    QuaTy ExQu _ _                 → φ { rqEx = True, rqAll = False }
    QuaTy AllQu _ _                → φ { rqEx = False, rqAll = True }
    VarTy _                        → φ
    _                              → φ { rqEx = False, rqAll = False }

-- | To compute the qualifier expression for a function type.
arrowQualifier ∷ MonadTV tv r m ⇒ Γ tv → Term a → m (QExp tv)
arrowQualifier γ e =
  qualifier (ConTy "U" [ σ
                       | n ← Set.toList (termFv e)
                       , σ ← γ &.& n ])

-- | To extend the environment and update the ranks of the free type
--   variables of the added types.
(&+&!) ∷ MonadTV tv r m ⇒ Γ tv → Map.Map Name (Type tv) → m (Γ tv)
γ &+&! m = do
  lowerRank (Rank.inc (rankΓ γ)) (Map.elems m)
  return (bumpΓ γ &+& m)
infixl 2 &+&!

-- | Extract the annotations in a pattern as an annotation.
extractPattAnnot ∷ MonadTV tv r m ⇒
                   Δ tv → Patt Empty → m (Maybe (Type tv))
extractPattAnnot δ π0
  | pattHasAnnot π0 = Just <$> loop π0
  | otherwise       = return Nothing
  where
  loop (VarPa _)    = newTVTy
  loop WldPa        = newTVTy
  loop (ConPa n πs) = ConTy n <$> mapM loop πs
  loop (InjPa n π)  = RowTy n <$> loop π <*> newTVTy
  loop (AnnPa _ an) = instAnnot δ an

-- | Given a list of type/U-action pairs, run all the U actions, but
--   in an order that does all U-actions not assocated with tyvars
--   before those associated with tyvars. Checks dynamically after each
--   action, since an action can turn a tyvar into a non-tyvar.
subsumeN ∷ MonadC tv r m ⇒ [(Type tv, m ())] → m ()
subsumeN [] = return ()
subsumeN σs = subsumeOneOf σs >>= subsumeN
  where
    subsumeOneOf []             = return []
    subsumeOneOf [(_, u1)]      = [] <$ u1
    subsumeOneOf ((σ1, u1):σs)  = do
      σ ← substRoot σ1
      case σ of
        VarTy (FreeVar α) | tvFlavorIs Universal α
          → ((σ, u1):) <$> subsumeOneOf σs
        _ → σs <$ u1

-- | Given a function arity and a type, extracts a list of argument
--   types and a result type of at most the given arity.
funmatchN ∷ MonadC tv r m ⇒ Int → Type tv → m ([Type tv], Type tv)
funmatchN n0 σ = do
  σ' ← substRoot σ
  case σ' of
    ConTy "->" [_, _, _] → unroll n0 σ'
    VarTy (FreeVar α) | tvFlavorIs Universal α → do
      β1 ← newTVTy
      qe ← newTV' QualKd
      β2 ← newTVTy
      σ' =: arrTy β1 (qvarexp (FreeVar qe)) β2
      return ([β1], β2)
    RecTy _ σ1 →
      funmatchN n0 (openTy 0 [σ'] σ1)
    _ → fail $ "Type error: In application expression, expected " ++
               "operator to have a function type, but got ‘" ++
               show σ' ++ "’ instead"
  where
    unroll n (ConTy "->" [σ1, _, σ']) | n > 0 = do
      (σ2m, σ) ← unroll (n - 1) =<< substRoot σ'
      return (σ1:σ2m, σ)
    unroll _ σ                           = return ([], σ)

-- | Subsumption
(≤)   ∷ MonadC tv r m ⇒ Type tv → Type tv → m ()
σ1 ≤ σ2 = do
  traceN 2 ("≤", σ1, σ2)
  subsumeBy (<:) σ1 σ2

subsumeBy ∷ MonadC tv r m ⇒
            (Type tv → Type tv → m ()) → Type tv → Type tv → m ()
subsumeBy (<*) σ1 σ2 = do
  σ1' ← substRoot σ1
  σ2' ← substRoot σ2
  case (σ1', σ2') of
    (VarTy (FreeVar α), _) | tvFlavorIs Universal α → do
      σ1' <* σ2'
    (_, VarTy (FreeVar α)) | tvFlavorIs Universal α → do
      σ1' ← instAll True =<< substDeep σ1'
      σ1' <* σ2'
    _ → do
      ρ1        ← instantiate σ1'
      (ρ2, αs2) ← collectTV (instantiateNeg σ2')
      ρ1 <* ρ2
      let (us1, _, ss1) = partitionFlavors αs2
      freeSkolems ← Set.filter (tvFlavorIs Skolem) <$>
                      ftvSet (σ1, σ2, fvTy <$> us1)
      when (any (`Set.member` freeSkolems) ss1) $ do
        traceN 3 (αs2, freeSkolems)
        fail $ "Type error: cannot subsume type ‘" ++ show σ1 ++
               "’ to type ‘" ++ show σ2 ++ "’ because the former is " ++
               "insufficiently polymorphic."
      return ()

-- | Given a list of type variables, partition it into a triple of lists
--   of 'Universal', 'Existential', and 'Skolem' flavored type variables.
partitionFlavors ∷ Tv tv ⇒
                   [tv] → ([tv], [tv], [tv])
partitionFlavors = loop [] [] [] where
  loop us es ss []     = (us, es, ss)
  loop us es ss (α:αs) = case tvFlavor α of
    Universal   → loop (α:us) es     ss     αs
    Existential → loop us     (α:es) ss     αs
    Skolem      → loop us     es     (α:ss) αs

---
--- Conditional generalization/instantiation
---

-- We start with a system for specifying requested
-- generalization/instantiation

-- | Used by 'infer' and helpers to specify a requested
--   generalization/instantiation state.
data Request tv
  = Request {
      -- | Request the type to have ∀ quantifiers generalized
      rqAll  ∷ !Bool,
      -- | Request the type to have ∃ quantifiers generalized
      rqEx   ∷ !Bool,
      -- | Require that the existentials type variables among these
      --   type variables be generalizable
      rqTVs  ∷ [(tv, Rank.Rank)],
      -- | Rank to which to generalize
      rqRank ∷ !Rank.Rank
    }

instance Ppr tv ⇒ Ppr (Request tv) where
  ppr φ = (if rqAll φ then Ppr.char '∀' else Ppr.empty)
          Ppr.<>
          (if rqEx φ then Ppr.char '∃' else Ppr.empty)
          Ppr.<>
          (if null (rqTVs φ)
             then Ppr.empty
             else ppr (rqTVs φ) Ppr.<> Ppr.char '/' Ppr.<> ppr (rqRank φ))

-- | Defines a variadic function for building 'Request' states.  Minimal
--   definition: 'addToRequest'
class MkRequest r tv | r → tv where
  -- | Variadic function that constructs a 'Request' state given some
  --   number of parameters to modify it, as shown by instances below.
  request      ∷ r
  request      = addToRequest Request {
    rqAll       = False,
    rqEx        = False,
    rqTVs       = [],
    rqRank      = Rank.infinity
  }
  addToRequest ∷ Request tv → r

instance MkRequest (Request tv) tv where
  addToRequest = id

instance MkRequest r tv ⇒ MkRequest (Request tv → r) tv where
  addToRequest _ r' = addToRequest r'

instance (Tv tv, MkRequest r tv) ⇒ MkRequest (Γ tv' → [tv] → r) tv where
  addToRequest r γ αs = addToRequest r {
    rqTVs  = [(α, rank) | α ← αs, tvFlavorIs Existential α] ++ rqTVs r,
    rqRank = rank `min` rqRank r
  }
    where rank = rankΓ γ

instance MkRequest r tv ⇒ MkRequest (Rank.Rank → r) tv where
  addToRequest r rank = addToRequest r {
    rqRank = rank `min` rqRank r
  }

{-
instance MkRequest r tv ⇒ MkRequest (Γ tv' → r) tv where
  addToRequest r γ = addToRequest r (rankΓ γ)
  -}

instance MkRequest r tv ⇒ MkRequest (Quant → r) tv where
  addToRequest r AllQu = addToRequest r { rqAll = True }
  addToRequest r ExQu  = addToRequest r { rqEx = True }

-- 'maybeGen', 'maybeInst', and 'maybeInstGen' are the external
-- interface to conditional generalization.

-- | Generalize the requested flavors, 
maybeGen ∷ MonadC tv r m ⇒
           Term Empty → Request tv → Γ tv → Type tv → m (Type tv)
maybeGen e0 φ γ σ = do
  let value = syntacticValue e0
  traceN 4 ("maybeGen", value, φ, γ, σ)
  checkEscapingEx φ
  σ ← if rqAll φ
        then generalize value (Rank.inc (rankΓ γ)) σ
        else return σ
  σ ← if rqEx φ
        then generalizeEx (rankΓ γ `min` rqRank φ) σ
        else return σ
  if rqAll φ
        then generalize value (rankΓ γ) σ
        else return σ

maybeInstGen ∷ MonadC tv r m ⇒
               Term Empty → Request tv → Γ tv → Type tv → m (Type tv)
maybeInstGen e φ γ σ = do
  σ ← case () of
    _ | isAnnotated e → return σ
      | rqAll φ       → return σ
      | rqEx φ        → instAll True =<< substDeep σ
      | otherwise     → instantiate σ
  maybeGen e φ γ σ

-- | Check for escaping existential type variables
checkEscapingEx ∷ MonadC tv r m ⇒ Request tv → m ()
checkEscapingEx φ =
  for_ (rqTVs φ) $ \(α,rank) → do
    rank' ← getTVRank α
    when (rank' <= rank) $
      fail "Type error: Existential type variable escapes its scope."

---
--- Instantiation operations
---

-- | Given a type relation, (maybe) a type, a type constructor name,
--   and its arity, return a list of (maybe) parameter types and returns
--   a list of any new type variables.  The output types are @Nothing@
--   iff the input type is @Nothign@.  If the input type is a type
--   variable, it gets unified with the requested shape over fresh type
--   variables using the given type relation.
--   PRECONDITION: σ is fully substituted.
{-
Instantiates both ∀ and ∃ to univars:
  (λx.x) : A → A          ⇒       (λ(x:A). (x:A)) : A → A
  (λx.x) : ∀α. α → α      ⇒       (λ(x:β). (x:β)) : ∀α. α → α
  (λx.x) : ∀α. C α → C α  ⇒       (λ(x:C β). (x:C β)) : ∀α. C α → C α
  (λx.x) : ∃α. α → α      ⇒       (λ(x:β). (x:β)) : ∃α. α → α
  (λx.x) : ∃α. C α → C α  ⇒       (λ(x:C β). (x:C β)) : ∃α. C α → C α
-}
splitCon ∷ MonadC tv r m ⇒
           (Type tv → Type tv → m ()) →
           Maybe (Type tv) → Name → Int →
           m ([Maybe (Type tv)])
splitCon _    Nothing  _ arity = return (replicate arity Nothing)
splitCon (<*) (Just σ) c arity = do
  traceN 4 ("splitCon", σ, c, arity)
  ρ ← instAllEx True False =<< substDeep σ
  case ρ of
    ConTy c' σs       | c == c', length σs == arity
      → return (Just <$> σs)
    ConTy _ []
      → do
          ρ <* ConTy c []
          return []
    VarTy (FreeVar α) | tvFlavorIs Universal α
      → do
          αs ← replicateM arity (newTVTy' (tvDescr α))
          ρ <* ConTy c αs
          return (Just <$> αs)
    _ → fail $ "Type error: Pattern expected a value constructed " ++
               "with ‘" ++ c ++ "’ (arity " ++ show arity ++ ") " ++
               "but got type ‘" ++ show σ ++ "’ instead."

-- | Like 'splitCon', but for rows.
--   PRECONDITION: σ is fully substituted.
splitRow ∷ MonadC tv r m ⇒
           (Type tv → Type tv → m ()) →
           Maybe (Type tv) → Name →
           m (Maybe (Type tv), Maybe (Type tv))
splitRow _    Nothing  _    = return (Nothing, Nothing)
splitRow (<*) (Just σ) name = do
  traceN 4 ("splitRow", σ, name)
  ρ ← instAllEx True False =<< substDeep σ
  loop ρ
  where
  loop ρ = case ρ of
    RowTy name' τ1 τ2 | name' == name
      → return (Just τ1, Just τ2)
                      | otherwise
      → do
        (mτ1, mτ2) ← loop τ2
        return (mτ1, RowTy name' τ1 <$> mτ2)
    VarTy (FreeVar α) | tvFlavorIs Universal α
      → do
          τ1 ← newTVTy
          τ2 ← newTVTy
          ρ <* RowTy name τ1 τ2
          return (Just τ1, Just τ2)
    _ → fail $ "Type error: Pattern expected a value constructed " ++
               "with ‘`" ++ name ++ "’ but got type ‘" ++ show σ ++
               "’ instead."

-- | Given a map from type variables names and qualifiers to variances,
--   create an initial type variable environment.
instAnnotTVs ∷ MonadC tv r m ⇒ VarMap (Name, QLit) → m (Δ tv)
instAnnotTVs vmap = foldM each Map.empty (Map.toList vmap) where
  each δ ((name, ql), variance) = do
    α ← newTV' (ql, varianceToKind variance,
                "annotation type variable " ++ qLitSigil ql : name)
    case Map.insertLookupWithKey (\_ _ → id) name α δ of
      (Nothing, δ') → return δ'
      (Just _,  _)  → fail $
        "Type error: Used both type variables `" ++ name ++
        " and '" ++ name ++ " in annotations in same expression."

-- | Given a tyvar environment (mapping some-bound names to tyvars) and
--   an annotation, create new universal type variables for any new
--   some-bound names in the annotation and update the environment
--   accordingly. Return the annotation instantiated to a type and the
--   list of universal tyvars.
instAnnot ∷ MonadTV tv r m ⇒
            Δ tv → Annot → m (Type tv)
instAnnot δ (Annot nqls σ0) = do
  let names = fst <$> nqls
  αs ← mapM eachName names
  traverse_ reportTV αs
  let σ = totalSubst names (fvTy <$> αs) =<< σ0
  traceN 4 ("instAnnot", δ, σ, αs)
  return σ
  where
    eachName ('_':_) = newTV
    eachName name    = case Map.lookup name δ of
      Just α  → return α
      Nothing → fail "BUG! (instAnnot): type variable not found"

-- | Instantiate the outermost universal and existential quantifiers
--   at the given polarities.
--   PRECONDITION: σ is fully substituted.
instAllEx ∷ MonadC tv r m ⇒ Bool → Bool → Type tv → m (Type tv)
instAllEx upos epos = substDeep >=> instEx epos >=> instAll upos

-- | Instantiate an outer universal quantifier.
--   PRECONDITION: σ is fully substituted.
instAll ∷ MonadC tv r m ⇒ Bool → Type tv → m (Type tv)
instAll pos (QuaTy AllQu αqs σ) = do
  traceN 4 ("instAll/∀", pos, αqs, σ)
  instGeneric 0 (determineFlavor AllQu pos) αqs σ
instAll pos (QuaTy ExQu αqs (QuaTy AllQu βqs σ)) = do
  traceN 4 ("instAll/∃∀", pos, αqs, βqs, σ)
  QuaTy ExQu αqs <$> instGeneric 1 (determineFlavor AllQu pos) βqs σ
instAll _ σ = return σ

-- | Instantiate an outer existential quantifier.
--   PRECONDITION: σ is fully substituted.
instEx ∷ MonadC tv r m ⇒ Bool → Type tv → m (Type tv)
instEx pos (QuaTy ExQu αqs σ) = do
  traceN 4 ("instEx", pos, αqs, σ)
  instGeneric 0 (determineFlavor ExQu pos) αqs σ
instEx _ σ = return σ

-- | What kind of type variable to create when instantiating
--   a given quantifier in a given polarity:
determineFlavor ∷ Quant → Bool → Flavor
determineFlavor AllQu  True    = Universal
determineFlavor AllQu  False   = Skolem
determineFlavor ExQu   True    = Existential
determineFlavor ExQu   False   = Universal

-- | Instantiate type variables and use them to open a type, given
--   a flavor and list of qualifier literal bounds.  Along with the
--   instantiated type, returns any new type variables.
--   PRECONDITION: σ is fully substituted.
instGeneric ∷ MonadC tv r m ⇒
              Int → Flavor → [(a, QLit)] → Type tv →
              m (Type tv)
instGeneric k flav αqs σ = do
  αs ← zipWithM (newTV' <$$> (,flav,) . snd) αqs (inferKindsTy σ)
  return (openTy k (fvTy <$> αs) σ)

-- | To instantiate a prenex quantifier with fresh type variables.
instantiate ∷ MonadC tv r m ⇒ Type tv → m (Type tv)
instantiate = instAllEx True True

-- | To instantiate a prenex quantifier with fresh type variables, in
--   a negative position
instantiateNeg ∷ MonadC tv r m ⇒ Type tv → m (Type tv)
instantiateNeg = instAllEx False False

---
--- Testing functions
---

check ∷ String → IO ()
check e = case showInfer (read e) of
  Left err    → fail err
  Right (τ,c) →
    putStrLn $ show τ ++ if null c then "" else " constraint " ++ c

showInfer ∷ Term Empty → Either String (Type String, String)
showInfer e = runU $ do
  (τ, c) ← inferTm (emptyΓ &+& Map.fromList γ0) e
  τ'     ← stringifyType τ
  return (τ', c)

stringifyType ∷ MonadTV tv r m ⇒ Type tv → m (Type String)
stringifyType = foldType (mkQuaF QuaTy) (mkBvF bvTy) (fvTy . show)
                         ConTy RowTy (mkRecF RecTy)

---
--- Testing
---

time ∷ IO a → IO (a, POSIXTime)
time m = do
  ptime1 ← getPOSIXTime
  result ← m
  ptime2 ← getPOSIXTime
  return (result, ptime2 - ptime1)

reportTime ∷ IO a → IO a
reportTime m = do
  (result, elapsed) ← time m
  hPutStrLn stderr $ "Elapsed time: " ++ show elapsed
  return result

tests, inferTests ∷ IO ()

inferTests = tests
tests | debug     = fail "Don't run tests when debug == True"
      | otherwise = reportTime $ do
  syntaxTests
  T.runTestTT inferFnTests
  return ()

inferFnTests ∷ T.Test
inferFnTests = T.test
  [ "A"         -: "A"
  , "A B C"     -: "A B C"
  , "λx.x"      -: "∀ α. α → α"
  , "λa.id id"  -: "∀ α β. α → β → β"
  , "λ_.choose id"
                -: "∀ α β γ. α → (β -γ> β) -γ> β -γ> β"
  , "λ_.choose (id : α → α)"
                -: "∀ α β γ. α → (β -γ> β) -γ> β -γ> β"
  , te "λf. P (f A) (f B)"
  , "λ_. single id" -: "∀ α β. α → List (β → β)"
  , "λf x. f (f x)" -: "∀α 'β. (α → α) → α → α"
  -- Patterns
  , "λC. B"     -: "C → B"
  , "λA. B"     -: "A → B"
  , "λ(_ : Z -A> Z : Z → Z). B" -: "(Z → Z) → B"
  , te "λ(_ : Z → Z : Z -A> Z). B"
  , "λ(f : Z -A> Z : Z → Z). f Z" -: "(Z → Z) → Z"
  , te "λ(f : Z -A> Z : Z → Z). f (f Z)"
  , "λ(B x). x"
                -: "∀α. B α → α"
  , "λ(B x) (C y z). x y z"
                -: "∀ α β γ δ. B (α -δ> β -A> γ) → C α β -δ> γ"
  , pe "λ(A x x). B"
  , "λ(B a (C b c) (D d (E e f g))). F"
                -: "∀ α β γ δ e f g. B α (C β γ) (D δ (E e f g)) → F"
  -- Let rec
  , "let rec f = λx. f x in f"
      -: "∀α β. α → β"
  , "let rec f = λx. f (f x) in f"
      -: "∀α. α → α"
  , "let rec f = λx. match Z with _ → f x | _ → x in f"
      -: "∀α. α → α"
  , "let rec f = λx. match Z with _ → f x | _ → Z in f"
      -: "∀α. α → Z"
  , "let rec f = λx. match Z with _ → f (f x) | _ → x in f"
      -: "∀α. α → α"
  , "let rec f = λx. match Z with _ → f (f x) | _ → Z in f"
      -: "Z → Z"
  , "let rec f = λ_. g G    \
    \    and g = λ_. f F in \
    \  (f, g)"
      -: "∀α β. (F → α) × (G → β)"
  , "let rec f = λ_. g G : B \
    \    and g = λ_. f F in  \
    \  (f, g)"
      -: "(F → B) × (G → B)"
  -- Occurs check
  , te "let rec x = C x in x"
  , te "λf. f f"
  , te "let rec f = λ(C x).f (C (f x)) in f"
  -- Subsumption
  , te "bot : ∀α. T α α : ∃α ∀β. T α β"
  , "bot : ∃α ∀β. T α β : ∃α. T α M"
                  -: "∃α. T α M"
  , te "bot : ∀α ∃β. T α β : ∃β ∀α. T α β"
  , "bot : ∃α. T α α : ∃α β. T α β"
                  -: "∃α β. T α β"
  , te "bot : ∃α β. T α β : ∃α. T α α"
  , "bot : ∀α β. T α β : ∀α. T α α"
                  -: "∀α. T α α"
  , te "bot : ∀α. T α α : ∀α β. T α β"
  , "bot : ∀α. T α : ∃α. T α"
                  -: "∃α. T α"
  , te "bot : ∃α. T α : ∀α. T α"
  , "bot : ∀α β. T α β : ∃α ∀β. T α β"
                  -: "∃α ∀β. T α β"
  , "bot : ∀α β. T α β : ∃β ∀α. T α β"
                  -: "∃β ∀α. T α β"
  , "bot : ∀α β. T α β : ∃α β. T α β"
                  -: "∃α β. T α β"
  , "bot : ∀α β. T α β : ∃α. T α α"
                  -: "∃α. T α α"
  -- Subtyping
  , "λf. C (f (λZ.Z))"
                  -: "∀ α. ((Z → Z) -A> α) → C α"
  , "λf. C (f (λZ.Z)) (f (λZ.Z))"
                  -: "∀ α. ((Z → Z) -U> α) → C α α"
  , "λf. C (f ((λZ.Z):Z -A> Z)) (f (λZ.Z))"
                  -: "∀ α. ((Z -A> Z) -U> α) → C α α"
  , "λf. C (f (λZ.Z)) (f ((λZ.Z):Z -A> Z))"
                  -: "∀ α. ((Z -A> Z) -U> α) → C α α"
  , "λf. C (f ((λZ.Z):Z -A> Z)) (f ((λZ.Z):Z -A> Z))"
                  -: "∀ α. ((Z -A> Z) -U> α) → C α α"
  --
  , "λf x. C (f x : Z -A> Z)"
                  -: "∀ α β. (α -β> Z -A> Z) → α -β> C (Z -A> Z)"
  , "λf x. C (f x : Z -A> Z) (f x : Z -A> Z)"
                  -: "∀ 'α. ('α → Z -A> Z) → 'α → C (Z -A> Z) (Z -A> Z)"
  , "λf x. C (f x : Z → Z) (f x : Z -A> Z)"
                  -: "∀ 'α. ('α → Z → Z) → 'α → C (Z → Z) (Z -A> Z)"
  , "λf x. C (f x : Z -A> Z) (f x : Z → Z)"
                  -: "∀ 'α. ('α → Z → Z) → 'α → C (Z -A> Z) (Z → Z)"
  , "λf x. C (f x : Z → Z) (f x : Z → Z)"
                  -: "∀ 'α. ('α → Z → Z) → 'α → C (Z → Z) (Z → Z)"
  , te "λf x. C (f x : Y → Y) (f x : Z → Z)"
  --
  , "λ(f : α -β> α) x. C (f x : B) (f x : B)"
                  -: "∀'α. (B → B) → B → C B B"
  , "λ(f : α → α) x. C (f x : Z → Z) (f x : Z → Z)"
                  -: "((Z → Z) → (Z → Z)) → (Z → Z) → C (Z → Z) (Z → Z)"
  , "λ(f : α → α) x. C (f x : Z -A> Z) (f x : Z -A> Z)"
                  -: "∀α. ((Z -α> Z) → (Z -α> Z)) → \
                     \    (Z → Z) → C (Z -A> Z) (Z -A> Z)"
  , "λ(f : α → α) x. C (f x : Z -U> Z) (f x : Z -A> Z)"
                  -: "((Z -U> Z) → (Z -U> Z)) → \
                     \(Z → Z) → C (Z -U> Z) (Z -A> Z)"
  , "λ(f : α → α) x. C (f x : Z -A> Z) (f x : Z -U> Z)"
                  -: "((Z -U> Z) → (Z -U> Z)) → \
                     \(Z → Z) → C (Z -A> Z) (Z -U> Z)"
  --
  -- qualifiers
  --
  , "λf g x. f (g x)"
      -: "∀ α β γ δ1 δ2. (β -δ2> γ) → (α -δ1> β) -δ2> α -δ1 δ2> γ"
  , "λf g x. f (f (g x))"
      -: "∀ α β δ1. (β → β) → (α -δ1> β) → α -δ1> β"
  , "λf g x. f (f (g x x))"
      -: "∀ 'α β δ1. (β → β) → ('α -δ1> 'α -A> β) → 'α -δ1> β"
  , "λf. f (f X X) X"
      -: "(X -U> X -A> X) → X"
  , "λf g x. f (f (g x) C) C"
      -: "∀ α β δ2. (β → C -A> β) → (α -δ2> β) → α -δ2> β"
  , "λf g x. f (f (g x) (g x)) (g x)"
      -: "∀ 'α β. (β → β -A> β) → ('α → β) → 'α → β"
  , "let f = bot : (B -A> B) → B in let g = bot : B -U> B in f g"
      -: "B"
  , te "let f = bot : (B -U> B) → B in let g = bot : B -A> B in f g"
  , te "let f = bot : (B -U> B) → B in let g = bot : B -A> B in f g"
  , "λ(x:α). let f = cast B : (B -A> B) → B in \
    \        let g = cast B : B -U> B in f g"
      -: "∀α. α → B"
  , "λ(x:α). let f = cast B : (B -A> B) → B in \
    \        let g = cast B : B -α> B in f g"
      -: "∀α. α → B"
  , "λ(x:Z -α> Z). let f = cast B:(B -A> B) → B in \
    \              let g = cast B:B -α> B in f g"
      -: "(Z -A> Z) → B"
  , "λ(x:α). let f = cast B : (B -α> B) → B in \
    \        let g = cast B : B -α> B in f g"
      -: "∀α. α → B"
  , "λ(x:α). let f = cast B : (B -α> B) → B in \
    \        let g = cast B : B -U> B in f g"
      -: "∀α. α → B"
  , te "λ(x:α). let f = cast B : (B -α> B) → B in \
       \        let g = cast B: B -A> B in f g"
  , "λ(x:B -α> B). let f = cast B : (B -α> B) → B in \
    \              let g = cast B : B -A> B in f g"
      -: "(B -A> B) → B"
  , "λ(x:α). let f = cast B : (B -A> B) → B in \
    \        let g = cast B : B -α> B in f g"
      -: "∀α. α → B"
  , "λ(x:α). let f = cast B : (B -U> B) → B in \
    \        let g = cast B : B -α> B in f g"
      -: "∀'α. 'α → B"
  , "λ(x:α). let f = cast B : (B -U> B) → B in \
    \        let g = cast B : B -α> B in f g"
      -: "∀'α. 'α → B"
  , te "λ(x:α). let f = cast B: (B -α> B) → B in \
    \           let g = cast B: B -A> B in f g"
  , "λ(f : (B -A> B) → B) (g : B -α> B). f g"
      -: "((B -A> B) → B) → (B -A> B) → B"
  , "λ(f : (B -α> B) → B) (g : B -A> B). f g"
      -: "((B -A> B) → B) → (B -A> B) → B"
  , "λ(f : (B -α> B) → B) (g : B -α> B). f g"
      -: "∀α. ((B -α> B) → B) → (B -α> B) → B"
  --
  , "(bot: (B -α> B) → B -α> B) (bot: B → B)"
      -: "B → B"
  , "(bot: (B -α> B) → B -α> B) (bot: B -U> B)"
      -: "B -U> B"
  , "(bot: (B -α> B) → B -α> B) (bot: B -U> B) : B -A> B"
      -: "B -A> B"
  , te "(bot: (B -α> B) → B -α> B) (bot: B -A> B) : B -U> B"
  --
  , "λ(_:α). (cast B: (B -α> B) → B) (cast B: B -α> B)"
      -: "∀α. α → B"
  , "λ(_:α) (_:β). (cast B: (B -α β> B) → B) (cast B: B -α> B)"
      -: "∀α β. α → β → B"
  , "λ(_:α) (_:β). (cast B: (B -α> B) → B) (cast B: B -α β> B)"
      -: "∀α 'β. α → 'β → B"
  , "λ(x:α) (y:β). eat (P x y) ((cast B: (B -α> B) → B) (cast B: B -α β> B))"
      -: "∀α 'β. α → 'β -α> B"
  --
  , "let rec f = λg x. let C = f ((λC.C) : C -U> C) C in g x in f"
      -: "∀α. (C -U α> C) → (C -U α> C)"
  --
  , "λ(x : Ref U α). x"
      -: "∀α. Ref U α → Ref U α"
  , "λ(x : Ref A α). x"
      -: "∀α. Ref A α → Ref A α"
  , "λ(x : Ref A α). x"
      -: "∀α. Ref A α → Ref A α"
  , "λ(r: Ref A α). r"
      -: "∀α. Ref A α → Ref A α"
  , "λ(f: Ref A α → α) (x: Ref A α). f x"
      -: "∀α. (Ref A α → α) → Ref A α → α"
  , "λ(f: Ref α β → β) (x: Ref α β). f x"
      -: "∀ α β. (Ref α β → β) → Ref α β → β"
  , "λx. match x with B _ → C"
      -: "∀ α. B α → C"
  , "choose ((λ_ _.X) : X -> X -U> X) ((λ_ _.X) : X -> X -A> X)"
      -: "X → X -A> X"
  --
  -- Generalization with non-empty Γ
  --
  , "λ(f : B -α> B). let g = λh. h f in (f, g)"
      -: "∀ β. (B → B) → (B → B) × (((B → B) -A> β) → β)"
  , "λ(f : B -α> B). let g = λh. h f in g"
      -: "∀ α β. (B -α> B) → ((B -α> B) -A> β) -α> β"
  --
  -- Row types
  --
  , "choose (`A M) (`A M)"
      -: "∀ r. [ A: M | r ]"
  , te "choose (`A M) (`A N)"
  , "choose (`A M) (`B N)"
      -: "∀ r. [ A: M | B: N | r ]"
  , "choose (`A M) (choose (`B N) (`C Q))"
      -: "∀ r. [ A: M | B: N | C: Q | r ]"
  , "choose (`A M) (#C (`B N))"
      -: "∀ α r. [ A: M | B: N | C: α | r ]"
  , "choose (#C (`A M)) (#C (`B N))"
      -: "∀ α r. [ A: M | B: N | C: α | r ]"
  , "choose (#B (`A M)) (#C (`B N))"
      -: "∀ α r. [ A: M | B: N | C: α | r ]"
  , "choose (#C (`A M)) (#A (`B N))"
      -: "∀ α r. [ A: M | B: N | C: α | r ]"
  , "choose (#A (`A M)) (#A (`B N))"
      -: "∀ α r. [ A: α | A: M | B: N | r ]"
  , "choose (#A (`A M)) (`A N)"
      -: "∀ r. [ A: N | A: M | r ]"
  , "λx. match x with `A y → y"
      -: "∀ α. [ A: α ] → α"
  , "λx. match x with `A y → y | `B y → y"
      -: "∀ α. [ A: α | B: α ] → α"
  , "λx. match x with `A y → y | `B y → M y"
      -: "∀ α. [ A: M α | B: α ] → M α"
  , "λx. match x with `A y → y | `A y → M y"
      -: "∀ α. [ A: M α | A: α ] → M α"
  , "λx. match x with `A y → y | `B y → y | _ → bot"
      -: "∀ α r. [ A: α | B: α | r ] → α"
  , "λx. match x with `A y → `B y | `B y → `A y | y → #A (#B y)"
      -: "∀ α β r. [ A: α | B: β | r ] → [ A: β | B: α | r]"
  , "λx. match x with `A y → `B y | `B y → `A y | y → #B (#A y)"
      -: "∀ α β r. [ A: α | B: β | r ] → [ A: β | B: α | r]"
  , "λf. f (`A M)"
      -: "∀ r β. ([ A: M | r ] -A> β) → β"
  , "λf. eat (f (`A M)) (f (`B N))"
      -: "∀ r β. ([ A: M | B: N | r ] -U> β) → β"
  , "λx. match x with `A _ → M | `B y → y"
      -: "∀ α. [ A: α | B: M ] → M"
  , "choose (`A ((λ_ _.X) : X -> X -U> X)) (`A ((λ_ _.X) : X -> X -A> X))"
      -: "∀ r. [ A: X → X -A> X | r ]"
  , "λx y. match x with `A T → y"
      -: "∀ α. [ A: T ] → α → α"
  , "λx y. match x with `A T → y | `B (T, T) → y"
      -: "∀ α. [ A: T | B: T × T ] → α → α"
  -- Equirecursive types
  , te "(bot : μa. M → [ A: a ]) N"
  , "(bot : μa. M → [ A: a ]) M"
      -: "μβ. [ A: M → β ]"
  , "let rec x = `A x in x"
      -: "∀γ. μα. [ A: α | γ ]"
  , "let rec x = #B (`A x) in x"
      -: "∀β γ. μα. [ A: α | B: β | γ ]"
  , "λx. choose x (`A x)"
      -: "∀'γ. (μα. [ A: α | 'γ ]) → μα. [ A: α | 'γ ]"
  , "λx. choose x (#B (`A x))"
      -: "∀'β 'γ. (μα. [ A: α | B: 'β | 'γ ]) → \
         \         μα. [ A: α | B: 'β | 'γ ]"
  , "let rec f = λz x. match x with `A x' -> f z x' | _ -> z in f"
      -: "∀ α, β. α → (μγ. [ A: γ | β]) -α> α"
  , "let rec foldr = λf z xs.                   \
    \  match xs with                            \
    \  | `Cons (x, xs') → f x (foldr f z xs')   \
    \  | `Nil T         → z                     \
    \  in foldr                                 "
      -: "∀ α β. (α → β -A> β) → β →                 \
         \       (μγ. [ Cons: α × γ | Nil: T ]) -β> β"
  , "let rec foldl = λf z xs.                   \
    \  match xs with                            \
    \  | `Cons (x, xs') → foldl f (f x z) xs'   \
    \  | `Nil T         → z                     \
    \  in foldl                                 "
      -: "∀ α β. (α → β -A> β) → β →                 \
         \       (μγ. [ Cons: α × γ | Nil: T ]) -β> β"
  , "bot : μγ. [ Cons: Q T × γ | Nil: T ]"
      -: "μγ. [ Cons: Q T × γ | Nil: T ]"
  , "bot : (μγ. [ Cons: Q A × γ | Nil: T ]) → Z"
      -: "(μγ. [ Cons: Q A × γ | Nil: T ]) → Z"
  , "(bot : (μγ. [ Cons: Q A × γ | Nil: T ]) → Z) \
    \(bot : μγ. [ Cons: Q T × γ | Nil: T ])"
      -: "Z"
  , te "(bot : (μγ. [ Cons: Q T × γ | Nil: T ]) → Z) \
       \(bot : μγ. [ Cons: Q A × γ | Nil: T ])"
  --- First class polymorphism
  , te "λf. P (f A) (f B)"
  , "λ(f : ∀ α. α → α). P (f A) (f B)"
                -: "(∀ α. α → α) → P A B"
  , "(single : (∀ α. α → α) → List (∀ α. α → α)) id"
                -: "List (∀ α. α → α)"
  , "(single : (∀ α. α → α) → β) id"
                -: "List (∀ α. α → α)"
  , "(single : β → List (∀ α. α → α)) id"
                -: "List (∀ α. α → α)"
  , "single (id : ∀ α. α → α)"
                -: "List (∀ α. α → α)"
  , te "single id : List (∀ α. α → α)"
  , te "λx. poly x"
  , te "poly (id id)"
  , "poly ((id : (∀ α. α → α) → β) id)"
                -: "Int × Bool"
  , "poly (id (id : ∀ α. α → α))"
                -: "Int × Bool"
  , "single (single (id : ∀ α. α → α))"
                -: "List (List (∀ α. α → α))"
  , "head ids"  -: "∀ α. α → α"
  , "apply head ids"
                -: "∀ α. α → α"
  , "revapp ids head"
                -: "∀ α. α → α"
  , te "apply single id : List (∀ α. α → α)"
  , te "λx. apply poly x"
  , te "apply poly (id id)"
  , "apply poly ((id : (∀ α. α → α) → β) id)"
                -: "Int × Bool"
  , "apply poly (id (id : ∀ α. α → α))"
                -: "Int × Bool"
  , "apply single (single (id : ∀ α. α → α))"
                -: "List (List (∀ α. α → α))"
  , te "revaapp id single : List (∀ α. α → α)"
  , te "λx. apply x poly"
  , te "revapp (id id) poly"
  , "revapp ((id : (∀ α. α → α) → β) id) poly"
                -: "Int × Bool"
  , "revapp (id (id : ∀ α. α → α)) poly"
                -: "Int × Bool"
  , "revapp (single (id : ∀ α. α → α)) single"
                -: "List (List (∀ α. α → α))"
  , "(cast X : (X → ∀'α. 'α → 'α) → Y) (cast X : (X → ∀α. α → α))"
                -: "Y"
  , te "(cast X : (X → ∀α. α → α) → Y) (cast X : (X → ∀'α. 'α → 'α))"
  , "bot : ∀α. α → α : ∀α. α → α"
                -: "∀α. α → α"
  , "bot : ∀α. α → α : ∀'α. 'α → 'α"
                -: "∀'α. 'α → 'α"
  , te "bot : ∀'α. 'α → 'α : ∀α. α → α"
  -- ST Monad
  , "runST (λ_. returnST X)"
                -: "X"
  , "apply runST (λ_. returnST X)"
                -: "X"
  , "revapp (λ_. returnST X) runST"
                -: "X"
  , "runST (λ_. bindST (newSTRef X) readSTRef)"
                -: "X"
  , "apply runST (λ_. bindST (newSTRef X) readSTRef)"
                -: "X"
  , "revapp (λ_. bindST (newSTRef X) readSTRef) runST"
                -: "X"
  , "runST (λ_. bindST (newSTRef X) (λr. returnST X))"
                -: "X"
  , te "runST (λ_. bindST (newSTRef X) (λr. returnST r))"
  -- Value restriction
  , "let r = ref nil in writeRef (r, cons A nil)"
                -: "T"
  , "let r = ref (`Nil T) in writeRef (r, `Cons (A, `Nil T))"
                -: "T"
  , "let r = ref nil in let t = writeRef (r, cons T nil) in r"
                -: "Ref U (List T)"
  , "let r = ref nil in let t = writeRef (r, cons T (readRef r)) in r"
                -: "Ref U (List T)"
  , "let r = ref nil in \
   \ let t = writeRef (r, cons T nil) in \
   \ let t = writeRef (r, cons T nil) in r"
                -: "Ref U (List T)"
  , te "let r = ref nil in \
      \ let t = writeRef (r, cons S nil) in \
      \ let t = writeRef (r, cons T nil) in r"
  , "let r = ref nil in \
   \ let t = writeRef (r, cons T (readRef r)) in \
   \ let t = writeRef (r, cons T (readRef r)) in r"
                -: "Ref U (List T)"
  , te "let r = ref nil in \
      \ let t = writeRef (r, cons S (readRef r)) in \
      \ let t = writeRef (r, cons T (readRef r)) in r"
  , "let r = ref (Q A) in (r, r)"
                -: "Ref U (Q A) × Ref U (Q A)"
  , "let r = ref (Q A) in (swapRef (r, Q A), r)"
                -: "Ref U (Q A) × Q A × Ref U (Q A)"
  , "let r = ref (Q A) in (swapRef (r, Q A), r)"
                -: "Ref U (Q A) × Q A × Ref U (Q A)"
  , "let r = ref (Q A) in (swapRef (r, Q U), r)"
                -: "Ref U (Q A) × Q A × Ref U (Q A)"
  , "let r = ref (Q U) in (swapRef (r, Q A), r)"
                -: "Ref U (Q A) × Q A × Ref U (Q A)"
  , "let r = ref (Q U) in (swapRef (r, Q A), r)"
                -: "Ref U (Q A) × Q A × Ref U (Q A)"
  , "let r = ref nil in \
   \ let (r', List T) = swapRef (r, cons T nil) in \
   \   swapRef (r', cons T nil) : Ref U (List T) × List T"
                -: "Ref U (List T) × List T"
  , "λT. let r = ref nil in \
   \     let (r', List T) = swapRef (r, cons T nil) in \
   \       swapRef (r', cons T nil)"
                -: "∀α. T → Ref (U α) (List T) × List T"
  -- Scoped type variables
  , "λ (x : α) (y : β). (x, y)"
                -: "∀ α β. α → β -α> α × β"
  , "λ (x : α) (y : α). (x, y)"
                -: "∀ α. α → α -α> α × α"
  , "λ (x : α) (y : β). (x, (y : α))"
                -: "∀ α. α → α -α> α × α"
  , "λ (x : α) (y : β). (x, y) : β × α"
                -: "∀ α. α → α -α> α × α"
  , "λ (x : α) (y : β). (x, y) : β × γ"
                -: "∀ α. α → α -α> α × α"
  , "λ (x : α) (y : β). (x, y) : γ × α"
                -: "∀ α. α → α -α> α × α"
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
  , "λ(x: `α). x"
                -: "∀`α. `α → `α"
  , "λ(x: 'α). x"
                -: "∀'α. 'α → 'α"
  -- Type annotation propagation
  , te "λ f . (f A, f B)"
  , "λ(f : ∀ α. α → α). (f A, f B)"
                -: "(∀ α. α → α) → A × B"
  , "(λf. (f A, f B)) : (∀ α. α → α) → A × B"
                -: "(∀ α. α → α) → A × B"
  , "(λf. (f A, f B)) : (∀ α. α → α) → β"
                -: "(∀ α. α → α) → A × B"
  , te "(λf. (f A, f B)) : ∀ β. (∀ α. α → α) → β"
  , "List (λx.x)"
                -: "∀ α. List (α → α)"
  , "List ((λx. x) : ∀ α. α → α)"
                -: "List (∀ α. α → α)"
  , "List (λx. x) : ∀ α. List (α → α)"
                -: "∀ α. List (α → α)"
  , "List (λx. x) : List (∀ α. α → α)"
                -: "List (∀ α. α → α)"
  , "λ_. (List (λx.x) : List α)"
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
  , "λ(B a (C b c) (D d (E e f g))). (F g a : F m m)"
                -: "∀ α, β γ δ e f. B α (C β γ) (D δ (E e f α)) → F α α"
  , "λ(A a (B b c)). (C a (B b c) : C α α)"
                -: "∀ α β. A (B α β) (B α β) → C (B α β) (B α β)"
  , "λ(A a (B b c)). (C a (B (b:α) c) : C α β)"
                -: "∀ α β. A α (B α β) → C α (B α β)"
  , te "λ(A a (B b c)). C a (B (b:α) c : α)"
  -- Patterns with type annotations
  , "λ(x:B). x"
                -: "B → B"
  , "λ(x: B α). x"
                -: "∀ α. B α → B α"
  , "λ(x: B (∀ α. α → α)). (λ(B f). f) x C"
                -: "B (∀ α. α → α) → C"
  , "λ(B x: α). x"
                -: "∀ α. B α → α"
  , "λ(B x: α) (B _: α). x"
                -: "∀ α. B α → B α -α> α"
  , "λ(B x: α) (B _: β). x"
                -: "∀ α, β. B α → B β -α> α"
  , "λ(B x: α) (_: α). x"
                -: "∀ α. B α → B α -α> α"
  , "λ(B x: α) (_: β). x"
                -: "∀ α, β. B α → β -α> α"
  , "λ(B x: B α) (_: α). x"
                -: "∀ α. B α → α -α> α"
  , "λ(B (x: α)) (_: α). x"
                -: "∀ α. B α → α -α> α"
  , te "λ(B x: α) (C _: α). x"
  , te "λ(f: (∀ α. α) → B) (K k). k f"
  , "λ(f: (∀ α. α) → B) (K (k : ((∀ α. α) → B) → Z)). k f"
                -: "((∀ α. α) → B) → (K (((∀ α. α) → B) → Z)) → Z"
  , "λ(f: (∀ α. α) → B) (K k : K (((∀ α. α) → B) → Z)). k f"
                -: "((∀ α. α) → B) → (K (((∀ α. α) → B) → Z)) → Z"
  , "λ(x : α) (y : β) ((z : β) : α). T"
                -: "∀ α. α → α → α → T"
  , "λ(x : α) (y : β) (z : β). (z : α)"
                -: "∀ α. α → α → α → α"
  , "λ(x : B (∀ α. α → α)). x"
                -: "B (∀ α. α → α) → B (∀ α. α → α)"
  , "λ(B x : B (∀ α. α → α)). (x M, x N)"
                -: "B (∀ α. α → α) → M × N"
  , "(λ(B x). (x M, x N)) : B (∀ α. α → α) → M × N"
                -: "B (∀ α. α → α) → M × N"
  , "(λ(A x). P (x A) (x B)) : A (∀ α. α → α) → β"
                -: "A (∀ α. α → α) → P A B"
  , te "(λ(B x). P (x A) (x B))"
  , "λ(B x : ∀ α. B (α → α)). x"
                -: "∀ α. (∀ β. B (β → β)) → α → α"
  , "λZ.(λ(B x). x) : (∀ β. B (β → β)) → z"
                -: "∀ α. Z → (∀ β. B (β → β)) → α → α"
  , "λ((B x y : B β D) : B C γ). E"
                -: "B C D → E"
  , "(λ(B x y : B β D). E) : B C γ → δ"
                -: "B C D → E"
  -- Let pattern annotations and propagation
  , te "let f = λx.(x M, x N) in f"
  , "let f : (∀α. α → α) → M × N = λg.(g M, g N) in f"
                -: "(∀α. α → α) → M × N"
  , "let f : (∀α. α → α) × β → M × N =  \
    \   λ(g, h : ∀α. α → α). (h (g M), h (g N)) in f"
                -: "(∀α. α → α) × (∀α. α → α) → M × N"
  , "let f : (∀α. α → α) × β → M × N =  \
    \   λ(g, h : ∀α. α → α). (h (g M), h (g N)) in f"
                -: "(∀α. α → α) × (∀α. α → α) → M × N"
  , "let f : β × γ → M × N =  \
    \   λ(g : ∀α. α → α, h : β). (h (g M), h (g N)) in f"
                -: "(∀α. α → α) × (∀α. α → α) → M × N"
  , "let f : β × β → M × N =  \
    \   λ(g : β, h : ∀α. α → α). (h (g M), h (g N)) in f"
                -: "(∀α. α → α) × (∀α. α → α) → M × N"
  , te "let f : γ × β → M × N =  \
       \   λ(g : ∀α. α → α, h : β). (h (g M), h (g N)) in f"
  , "λZ. let (f, g) = (λx.x, λx.x) in (f, g)"
                -: "∀α β. Z → (α → α) × (β → β)"
  , "λZ. let (f, g) : α × α = (λx.x, λx.x) in (f, g)"
                -: "∀α. Z → (α → α) × (α → α)"
  , "λZ. let (f:α, g:β) = (λx.x, λx.x) in (f, g)"
                -: "∀α β. Z → (α → α) × (β → β)"
  , "λZ. let (f:α, g:α) = (λx.x, λx.x) in (f, g)"
                -: "∀α. Z → (α → α) × (α → α)"
  , "let (f: ∀α. α → α, g: ∀α. α → α) = (λx.x, λx.x) in \
    \ (f B, f C)"
                -: "B × C"
  , "let (f: ∀α. α → α, g) = (λx.x, λx.x) in (f B, f C, g C)"
                -: "B × C × C"
  , te "let (f: ∀α. α → α, g) = (λx.x, λx.x) in (f B, f C, g B, g C)"
  , "let (f: ∀α. α → α, g) = (λx.x, (λx.x) : ∀α. α → α) in \
    \  (f B, f C, g B, g C)"
                -: "B × C × B × C"
  , "let (f: ∀α. α → α, g) = (((λx.x) : ∀α. α → α), \
    \                         ((λx.x) : ∀α. α → α)) in \
    \  (f B, f C, g B, g C)"
                -: "B × C × B × C"
  , "let (f, g) = ((λx.x) : ∀a. a → a, (λx.x) : ∀a. a → a) in \
    \ (f B, f C, g B, g C)"
                -: "B × C × B × C"
  -- Let rec
  , "let rec f = λx y z. f x z y in f"
                -: "∀α β γ. α → β -α> β -α β> γ"
  , "let rec f = λx. app x (f x) in f"
                -: "∀'α. List 'α → List 'α"
  , "let rec f = λx. app x (f x) in (f (List B), f (List C))"
                -: "List B × List C"
  , te "let rec f : ∀α. List α → List α = (λx. app x (f x)) in f"
  , "let rec f : ∀'α. List 'α → List 'α = (λx. app x (f x)) in f"
                -: "∀'α. List 'α → List 'α"
  , "let rec f : ∀'α. List 'α → List 'α = (λx. app x (f x)) \
    \ in (f (List B), f (List C))"
                -: "List B × List C"
  , te "let rec f = (λx.x) (λx y z. f x z y) in f"
  , "let rec f = λx. app x (g x) \
    \    and g = λy. app (f y) y \
    \ in (f, g)"
                -: "∀'α 'β. (List 'α → List 'α) × (List 'β → List 'β)"
  , "let rec f = λx. app x (g x) \
    \    and g = λy. app (f y) y \
    \ in (f: ∀'α. List 'α → List 'α, g: ∀'α. List 'α → List 'α)"
                -: "(∀'α. List 'α → List 'α) × (∀'β. List 'β → List 'β)"
  , "let rec y = λf. f (y f) in y"
                -: "∀α. (α -U> α) → α"
  , "let rec y = λf x. f (y f) x in y"
                -: "∀α β. ((α → β) → α -A> β) → α → β"
  , "let rec cf = C (λx. let C f = cf in f (f x)) in cf"
                -: "∀α. C (α → α)"
  -- (Let rec polymorphic recursion:)
  , te "let rec f = λx. f (B x) in f"
  , "let rec f : ∀α. B α → Z = λx. f (B x) in f"
                -: "∀α. B α → Z"
  , "let rec f : ∀α. B α → Z = λx. f (B (f (B x))) in f"
                -: "∀α. B α → Z"
  , te "let rec f = λx. choose (single x) (head (f (single x))) in f"
  , "let rec f : ∀'α. 'α → List 'α = \
    \       λx. choose (single x) (head (f (single x))) in f"
                -: "∀'α. 'α → List 'α"
  ----
  ---- Existential quantification
  ----
  -- Construction
  , "Z : ∃α. α"
                -: "∃α. α"
  , "(Y, Z) : ∃α. α"
                -: "∃α. α"
  , "(Y, Z) : ∃α. Y × α"
                -: "∃α. Y × α"
  , te "(Y, Z) : ∃α. α × α"
  , "(Y, Z) : ∃α. ε × α"
                -: "∃α. Y × α"
  , "(Z, Z) : ∃α. α × α"
                -: "∃α. α × α"
  , "(Z, Z) : ∃α. Z × α"
                -: "∃α. Z × α"
  , "(Z, Z) : ∃α. ε × α"
                -: "∃α. Z × α"
  , "Z : ∃'α. 'α"
                -: "∃'α. 'α"
  , "A : ∃α. α"
                -: "∃α. α"
  , "A : ∃α. α"
                -: "∃α. α"
  , te "A : ∃'α. 'α"
  , "let x = (Q U, Q A) in x : ∃α. α × α"
                -: "∃α. α × α"
  , te "let x = (Q U, Q A) in x : ∃'α. 'α × 'α"
  -- Impredicative instantiation to ∃
  , "(λx.x) (Z : ∃α. α)"
                -: "∃α. α"
  , "let z : ∃α. α = Z in (λx.x) z"
                -: "∃α. α"
  , "let z : ∃α. α = Z in (λ_.Y) z"
                -: "Y"
  , "let z : ∃α. α = Z in (λ(_:∃α.α).Y) z"
                -: "Y"
  , "let f : ∀ α. A α → Z = λ_. Z in \
    \let x : ∃ α. A α = A B in \
    \  f x"
                -: "Z"
  , "let f : ∀ α. A α → Z = λ_. Z in \
    \let x : ∃ 'α. A 'α = A B in \
    \  f x"
                -: "Z"
  , "let x : ∃α. B α = B A in (λ(B _). Z) x"
                -: "Z"
  -- Constructing data with ∃
  , "let x : ∃α. B α = B A in C x"
                -: "∃α. C (B α)"
  , "let x : ∃α. B α = B A in C (x : ∃α. B α)"
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
                -: "(∃α. List α) → ∃α. List α"
  , "λ(f : ∀α. α → D α) (e : ∃α. C α). f e"
                -: "(∀α. α → D α) → (∃α. C α) → D (∃α. C α)"
  , "λ(f : ∀α. C α → D α) (e : ∃α. C α). f e"
                -: "(∀α. C α → D α) → (∃α. C α) → ∃α. D α"
  , "λ(f : ∀α. C α → D α α) (e : ∃α. C α). f e"
                -: "(∀α. C α → D α α) → (∃α. C α) → ∃α. D α α"
  , te "λ(f : ∀α β. C α → C β → D α β) (e : ∃α. C α). f e e"
  , "λ(f : ∀α β. C α → C β → D α β) (e : ∃'α. C 'α). f e e"
                -: "(∀α β. C α → C β → D α β) → (∃'α. C 'α) → ∃'α 'β. D 'α 'β"
  , "λ(f : ∀α. α → D α) (C e : ∃α. C α). f e"
                -: "(∀α. α → D α) → (∃α. C α) → ∃α. D α"
  , "λ(f : ∀α. α → D α) (C e : ∃α. C α). (f e : ∃α. D α)"
                -: "(∀α. α → D α) → (∃β. C β) → ∃α. D α"
  -- with propagation
  , "(λf e. f e) : (∀α. α → D α) → (∃α. C α) → D (∃α. C α)"
                -: "(∀α. α → D α) → (∃α. C α) → D (∃α. C α)"
  , "(λf e. f e) : (∀α. C α → D α) → (∃α. C α) → ∃α. D α"
                -: "(∀α. C α → D α) → (∃α. C α) → ∃α. D α"
  , "(λf e. f e) : (∀α. C α → D α α) → (∃α. C α) → ∃α. D α α"
                -: "(∀α. C α → D α α) → (∃α. C α) → ∃α. D α α"
  , "(λf e. f e e) : (∀α β. C α → C β → D α β) → (∃'α. C 'α) → ∃'α 'β. D 'α 'β"
                -: "(∀α β. C α → C β → D α β) → (∃'α. C 'α) → ∃'α 'β. D 'α 'β"
  , "(λf e. f e) : (∀α. α → D α) → (∃β. C β) → D (∃α. C α)"
                -: "(∀α. α → D α) → (∃β. C β) → D (∃α. C α)"
  -- Destruction by pattern matching
  , "λ(T x: ∃α. T α). S x"
                -: "(∃α. T α) → ∃α. S α"
  , te "λf (T x: ∃α. T α). f x"
  , "λ(tx: ∃α. T α). let T x = tx in S x"
                -: "(∃α. T α) → ∃ α. S α"
  , te "λf (tx: ∃α. T α). let T x = tx in f x"
  , "λ(tx: ∃α. T α). match tx with T x → S x"
                -: "(∃α. T α) → ∃ α. S α"
  , te "λf (tx: ∃α. T α). match tx with T x → f x"
  , "λ(tx: S (∃α. T α)). match tx with S (T x) → T (S x)"
                -: "S (∃α. T α) → ∃α. T (S α)"
  , "λ(tx: S (∃α. T α)). match tx with S (T x) → T (S x : ∃β. S β)"
                -: "S (∃α. T α) → T (∃α. S α)"
  , te "λf (tx: S (∃α. T α)). match tx with S (T x) → f x"
  , "let x = bot : ∃ α. T α in (λ(T y). S y) x"
                -: "∃ α. S α"
  , te "λf. let x = bot : ∃ α. T α in (λ(T y). f y) x"
  , "λ_. S (bot : ∃α. T α : T b)"
                -: "∀α. α → ∃β. S (T β)"
  , te "λf. f (bot : ∃α. T α : T b)"
  , "λ_. let x = bot : ∃α. T α : T b in S x"
                -: "∀α. α → ∃β. S (T β)"
  , te "λf. let x = bot : ∃α. T α : T b in f x"
  , "λ(e : ∃α. C (D α) (D α)).          \
    \let C x y = e in           \
    \  choose x y"
                -: "(∃α. C (D α) (D α)) → ∃α. D α"
  , "λ(e : ∃α. C (D α) (D α)).          \
    \  let C x y = e in                   \
    \    (choose x y : ∃α. D α)"
                -: "(∃α. C (D α) (D α)) → ∃α. D α"
  -- Existentials don't match other stuff
  , "let x : ∃'α. C 'α = C T in        \
    \let (C x', C y') = (x, x) in      \
    \  choose x x"
                -: "∃'α. C 'α"
  , te "let x : ∃'α. C 'α = C T in        \
       \let (C x', C y') = (x, x) in      \
       \ choose x' y'"
  , te "let x : ∃'α. C 'α = C T in        \
       \ λ(f : ∀α. C α → C α → Z). f x x"
  , "let x : ∃'α. C 'α = C T in        \
    \ λ(f : ∀α β. C α → C β → Z). f x x"
                -: "(∀α β. C α → C β → Z) → Z"
  , "let x : ∃'α. C 'α = C T in        \
    \λ(f : ∀α. C α → C α → Z). let z : C δ = x in f z z"
              -: "(∀α. C α → C α → Z) → Z"
  , te "let x : ∃'α. C 'α = C T in        \
       \let y : ∃'α. C 'α = C T in        \
       \λ(f : ∀α. C α → C α → Z). f x y"
  , "let x : ∃'α. C 'α = C T in        \
    \let y : ∃'α. C 'α = C T in        \
    \λ(f : ∀α. α → α → Z). f x y"
                -: "(∀α. α → α → Z) → Z"
  , te "let e : ∃'α. 'α × ('α → Int) = (Int, λx.x) in (snd e) (fst e)"
  , "let e : ∃'α. 'α × ('α → Int) = (Int, λx.x) in  \
    \(λp. (snd p) (fst p)) e"
                -: "Int"
  , te "let e : ∃'α. 'α × ('α → C 'α) = (Int, λx.C x) in (snd e) (fst e)"
  , "let e : ∃'α. 'α × ('α → C 'α) = (Int, λx.C x) in  \
    \(λp. (snd p) (fst p)) e"
                -: "∃'α. C 'α"
  ]
  where
  a -: b = limit a $ case readsPrec 0 a of
    [(e,[])] →
      let expect = standardize (read b)
          typing = showInfer e in
      T.assertBool ("⊢ " ++ a ++ "\n  : " ++ either show show typing ++
                    "\n  ≠  " ++ show expect)
        (case typing of
           Left _       → False
           Right (τ, _) → τ == elimEmptyF expect)
    _  → T.assertBool ("Syntax error: " ++ a) False
  te a   = limit a $ T.assertBool ("¬⊢ " ++ a)
             (either (const True) (const False) (showInfer (read a)))
  pe a   = T.assertBool ("expected syntax error: " ++ a)
             (length (reads a ∷ [(Term Empty, String)]) /= 1)
  limit a m = do
    result ← timeout 1000000 m
    case result of
      Just () → return ()
      Nothing → T.assertBool ("Timeout: " ++ a) False

