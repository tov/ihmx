{-#
  LANGUAGE
    ImplicitParams,
    ParallelListComp,
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
  inferTm, infer,
  -- * Testing
  -- ** Interactive testing
  check, showInfer,
  -- ** Unit tests
  inferTests, tests,
) where

-- import qualified Data.List  as List
import qualified Data.Map   as Map
import qualified Data.Set   as Set
import qualified Test.HUnit as T
import Control.Monad.RWS    as RWS
-- import Control.Monad.State  as CMS

import Data.Time.Clock.POSIX (POSIXTime, getPOSIXTime)
import System.IO (stderr, hPutStrLn)
import System.Timeout (timeout)

import MonadU
import Constraint
import Syntax hiding (tests)
import Env
import Util
import qualified Rank

---
--- Inference
---

-- | Infer the type of a term, given a type context
inferTm ∷ (MonadU tv r m, Show tv, Tv tv) ⇒
          Γ tv → Term Empty → m (Type tv, String)
inferTm γ e = do
  δ0 ← Map.fromDistinctAscList <$> sequence
    [ do
        α ← newTVKind (varianceToKind var)
        return (name, fvTy α)
    | (name, var) ← Map.toAscList (ftvPure e) ]
  runConstraintT $ do
    τ ← infer δ0 γ e
    σ ← generalize (syntacticValue e) (rankΓ γ) τ
    c ← showConstraint
    return (σ, c)

-- | To infer a type and constraint for a term
infer ∷ MonadC tv r m ⇒ Δ tv → Γ tv → Term Empty → m (Type tv)
infer δ γ e0 = case e0 of
  AbsTm π e                     → do
    (δ', τ1, τs)     ← inferPatt δ π Nothing (countOccsPatt π e)
    γ'               ← γ &+&! π &:& τs
    τ2               ← infer δ' γ' e
    qe               ← arrowQualifier γ (AbsTm π e)
    return (arrTy τ1 qe τ2)
  LetTm π e1 e2                 → do
    τ1               ← infer δ γ e1
    (δ', _, τs)      ← inferPatt δ π (Just τ1) (countOccsPatt π e2)
    τs'              ← generalizeList (syntacticValue e1) (rankΓ γ) τs
    γ'               ← γ &+&! π &:& τs'
    infer δ' γ' e2
  MatTm e1 bs                   → do
    τ1               ← infer δ γ e1
    inferMatch δ γ τ1 bs
  RecTm bs e2                   → do
    αs               ← replicateM (length bs) newTVTy
    let ns           = map fst bs
    γ'               ← γ &+&! ns &:& αs
    sequence_
      [ do
          unless (syntacticValue ei) $
            fail $ "In let rec, binding for ‘" ++ ni ++
                   "’ not a syntactic value"
          τi ← infer δ γ' ei
          αi =: τi
          αi ⊏: U
      | (ni, ei) ← bs
      | αi       ← αs ]
    τs'              ← generalizeList True (rankΓ γ) αs
    γ'               ← γ &+&! ns &:& τs'
    infer δ γ' e2
  VarTm n                       → inst =<< γ &.& n
  ConTm n es                    → do
    τs               ← mapM (infer δ γ) es
    return (ConTy n τs)
  LabTm b n                     → do
    let (n1, n2, j1, j2) = if b then ("α","r",0,1) else ("r","α",1,0)
    inst $ QuaTy AllQu [(Here n1, L), (Here n2, L)] $
             arrTy (bvTy 0 0 (Here n1)) (qlitexp U) $
               RowTy n (bvTy 0 j1 (Here "α")) (bvTy 0 j2 (Here "r"))
  AppTm e1 e2                   → do
    τ1               ← infer δ γ e1
    τ2               ← infer δ γ e2
    α                ← newTVTy
    τ1 <: arrTy τ2 (qlitexp L) α
    return α
  AnnTm e annot                 → do
    (δ', τ', _)      ← instAnnot δ annot
    τ                ← infer δ' γ e
    τ <: τ'
    return τ'

-- | To infer a type and constraint for a match form
inferMatch ∷ MonadC tv r m ⇒
             Δ tv → Γ tv → Type tv → [(Patt Empty, Term Empty)] →
             m (Type tv)
inferMatch _ _ _ [] = newTVTy
inferMatch δ γ τ ((InjPa n πi, ei):bs) | totalPatt πi = do
  β               ← newTVTy
  mαr             ← extractLabel n <$> derefAll τ
  (α, r)          ← maybe ((,) <$> newTVTy <*> newTVTy) return mαr
  (δ', _, τs)     ← inferPatt δ πi (Just α) (countOccsPatt πi ei)
  γ'              ← γ &+&! πi &:& τs
  τi              ← infer δ' γ' ei
  τk              ← if null bs
                      then do r <: endTy; return β
                      else inferMatch δ' γ r bs
  mapM_ (τ ⊏:) (countOccsPatt πi ei)
  when (pattHasWild πi) (τ ⊏: A)
  τi <: β
  τk <: β
  τ  <: RowTy n α r
  return β
inferMatch δ γ τ ((πi, ei):bs) = do
  β               ← newTVTy
  (δ', _, τs)     ← inferPatt δ πi (Just τ) (countOccsPatt πi ei)
  γ'              ← γ &+&! πi &:& τs
  τi              ← infer δ' γ' ei
  τk              ← inferMatch δ' γ τ bs
  τi <: β
  τk <: β
  return β

-- | Extend the environment and update the ranks of the type variables
(&+&!) ∷ MonadU tv r m ⇒ Γ tv → Map.Map Name (Type tv) → m (Γ tv)
γ &+&! m = do
  lowerRank (Rank.inc (rankΓ γ)) (Map.elems m)
  return (bumpΓ γ &+& m)

infixl 2 &+&!

arrowQualifier ∷ MonadU tv r m ⇒ Γ tv → Term a → m (QExp tv)
arrowQualifier γ e =
  qualifier (ConTy "U" [ σ
                       | n ← Set.toList (termFv e)
                       , σ ← γ &.& n ])
  where ?deref = readTV

-- | Instantiate a prenex quantifier
inst ∷ MonadC tv r m ⇒ Type tv → m (Type tv)
inst σ0 = do
  σ      ← deref σ0
  τ      ← case σ of
    QuaTy AllQu nqs τ → do
      αs ← sequence
        [ do
            α ← fvTy <$> newTVKind kind
            α ⊏: q
            return α
        | (_, q) ← nqs
        | kind   ← inferKindsTy τ ]
      return (openTy 0 αs τ)
    τ → return τ
  trace ("inst", σ, τ)
  return τ

-- | Given a type variable environment, a pattern, optionally an
--   expected type, and a list of how each bound variable will be used,
--   and compute an updated type variable environment, a constraint,
--   a type for the whole pattern, and a type for each variable bound by
--   the pattern.
inferPatt ∷ MonadC tv r m ⇒
            Δ tv → Patt Empty → Maybe (Type tv) → [Occurrence] →
            m (Δ tv, Type tv, [Type tv])
inferPatt δ0 π0 mτ0 occs = do
  (σ, δ, τs) ← runRWST (loop π0 mτ0) () δ0
  zipWithM (⊏:) τs occs
  σ ⊏: bigJoin (take (length τs) occs)
  when (pattHasWild π0) (σ ⊏: A)
  return (δ, σ, τs)
  where
  bind τ      = do tell [τ]; return τ
  {-
  constrain c = tell (c, [])
  -}
  loop (VarPa _)       mτ = do
    α ← maybe newTVTy return mτ
    bind α
  loop WldPa           mτ = do
    α ← maybe newTVTy return mτ
    α ⊏: A
    return α
  loop (ConPa name πs) mτ = do
    case mτ of
      Nothing → ConTy name <$> sequence [ loop πi Nothing | πi ← πs ]
      Just τ0 → do
        τ ← deref τ0
        case τ of
          ConTy name' τs@(_:_) | length τs == length πs, name == name' →
            ConTy name <$> sequence
              [ loop πi (Just τi)
              | πi ← πs
              | τi ← τs ]
          _ → do
            τ' ← ConTy name <$> sequence [ loop πi Nothing | πi ← πs ]
            τ <: τ'
            return τ
  loop (InjPa name π)  mτ = do
    case mτ of
      Nothing → RowTy name <$> loop π Nothing <*> newTVTy
      Just τ0 → do
        τ ← deref τ0
        case τ of
          -- XXX Need to permute?
          RowTy name' τ' τr | name == name' → do
            τ' ← RowTy name <$> loop π (Just τ') <*> pure τr
            return τ'
          _ → do
            τ' ← RowTy name <$> loop π Nothing <*> newTVTy
            τ <: τ'
            return τ
  loop (AnnPa π annot) mτ = do
    δ ← get
    (δ', τ', _) ← lift (instAnnot δ annot)
    put δ'
    τ ← loop π (Just τ')
    case mτ of
      Just τ'' → do
        τ'' <: τ
        return τ''
      Nothing  → return τ

-- | Given a tyvar environment (mapping some-bound names to tyvars) and
--   an annotation, create new universal type variables for any new
--   some-bound names in the annotation and update the environment
--   accordingly. Return the annotation instantiated to a type and the
--   list of new universal tyvars.
instAnnot ∷ MonadU tv r m ⇒
            Δ tv → Annot → m (Δ tv, Type tv, [Type tv])
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
    {- Note that the newTVTy case shouldn't happen because we
       create tyvars for every term up front in 'inferTm'. -}

{-
-- | If the pattern is fully annotated, extract the annotation.
extractPattAnnot ∷ Monad m ⇒ Patt Empty → m Annot
extractPattAnnot π0 = do
  (σ, ns) ← runStateT (loop π0) []
  return (Annot ns σ)
  where
  loop (VarPa _)              = fail "Unannotated variable pattern"
  loop WldPa                  = fail "Unannotated wildcard pattern"
  loop (ConPa c πs)           = ConTy c `liftM` mapM loop πs
  loop (AnnPa _ (Annot ns σ)) = do
    modify (`List.union` ns)
    return σ
    -}

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

stringifyType ∷ MonadU tv r m ⇒ Type tv → m (Type String)
stringifyType = foldType (mkQuaF QuaTy) (mkBvF bvTy) (fvTy . show)
                         ConTy RowTy (mkRecF RecTy)
  where ?deref = readTV

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
  , "λx.x"      -: "∀ α:L. α → α"
  , "λa.id id"  -: "∀ α:A, β:L. α → β → β"
  , "λ_.choose id"
                -: "∀ α:A, β, γ:A. α → (β -γ> β) -γ> β -γ> β"
  , "λ_.choose (id : α → α)"
                -: "∀ α:A, β, γ:A. α → (β -γ> β) -γ> β -γ> β"
  , te "λf. P (f A) (f B)"
  , "λ_. single id" -: "∀ α:A, β. α → List (β → β)"
  , "λf x. f (f x)"     -: "∀α, β:R. (α -β> α) → α -β> α"
  -- Patterns
  , "λC. B"     -: "C → B"
  , "λA. B"     -: "A → B"
  , "λ(L:U). B" -: "U → B"
  , te "λ(R:A). B"
  , "λ(B x). x"
                -: "∀α. B α → α"
  , "λ(B x) (C y z). x y z"
                -: "∀ α β γ δ. B (α -δ> β -L> γ) → C α β -δ> γ"
  , pe "λ(A x x). B"
  , "λ(B a (C b c) (D d (E e f g))). F"
                -: "∀ α β γ δ e f g: A. B α (C β γ) (D δ (E e f g)) → F"
  -- Let rec
  , "let rec f = λx. f x in f"
      -: "∀α β. α → β"
  , "let rec f = λx. f (f x) in f"
      -: "∀α. α → α"
  , "let rec f = λx. match Z with _ → f x | _ → x in f"
      -: "∀α. α → α"
  , "let rec f = λx. match Z with _ → f x | _ → Z in f"
      -: "∀α:A. α → Z"
  , "let rec f = λx. match Z with _ → f (f x) | _ → x in f"
      -: "∀α. α → α"
  , "let rec f = λx. match Z with _ → f (f x) | _ → Z in f"
      -: "Z → Z"
  , "let rec f = λ_. g G    \
    \    and g = λ_. f F in \
    \  Pair f g"
      -: "∀α β. Pair (F → α) (G → β)"
  , "let rec f = λ_. g G : B \
    \    and g = λ_. f F in  \
    \  Pair f g"
      -: "Pair (F → B) (G → B)"
  -- Occurs check
  , te "λf. f f"
  , te "let rec f = λ(C x).f (C (f x)) in f"
  -- Subtyping
  , "λf. C (f L)" -: "∀ α. (L -L> α) → C α"
  , "λf. C (f L) (f L)" -: "∀ α. (L -R> α) → C α α"
  , "λf. C (f R) (f L)" -: "∀ α. (L -R> α) → C α α"
  , "λf. C (f A) (f L)" -: "∀ α. (L -R> α) → C α α"
  , "λf. C (f L) (f R)" -: "∀ α. (L -R> α) → C α α"
  , "λf. C (f L) (f A)" -: "∀ α. (L -R> α) → C α α"
  , "λf. C (f U) (f L)" -: "∀ α. (L -R> α) → C α α"
  , "λf. C (f A) (f A)" -: "∀ α. (A -R> α) → C α α"
  , "λf. C (f R) (f A)" -: "∀ α. (L -R> α) → C α α"
  , "λf. C (f U) (f A)" -: "∀ α. (A -R> α) → C α α"
  --
  , "λf x. C (f x : L)" -: "∀ α β. (α -β> L) → α -β> C L"
  , "λf x. C (f x : L) (f x : L)" -: "∀ α β:R. (α -β> L) → α -β> C L L"
  , "λf x. C (f x : R) (f x : L)" -: "∀ α β:R. (α -β> R) → α -β> C R L"
  , "λf x. C (f x : A) (f x : L)" -: "∀ α β:R. (α -β> A) → α -β> C A L"
  , "λf x. C (f x : U) (f x : L)" -: "∀ α β:R. (α -β> U) → α -β> C U L"
  , "λf x. C (f x : A) (f x : A)" -: "∀ α β:R. (α -β> A) → α -β> C A A"
  , "λf x. C (f x : R) (f x : A)" -: "∀ α β:R. (α -β> U) → α -β> C R A"
  , "λf x. C (f x : U) (f x : A)" -: "∀ α β:R. (α -β> U) → α -β> C U A"
  , te "λf x. C (f x : U) (f x : B)"
  --
  , "λ(f : α -β> α) x. C (f x : B) (f x : B)"
                                  -: "∀α:R. (B -α> B) → B -α> C B B"
  , "λ(f : α → α) x. C (f x : B) (f x : B)" -: "(B → B) → B → C B B"
  , "λ(f : α → α) x. C (f x : U) (f x : U)" -: "(U → U) → U → C U U"
  , "λ(f : α → α) x. C (f x : R) (f x : A)" -: "(U → U) → U → C R A"
  , "λ(f : α → α) x. C (f x : U) (f x : L)" -: "(U → U) → U → C U L"
  --
  , "let g = λ(f : α → α) x. C (f x : R) (f x : R) in g (λR.R) U"
      -: "C R R"
  , te "let g = λ(f : α → α) x. C (f x : L) (f x : L) in g (λL.L) U"
  , "let g = λ(f : α → α) x. C (f x : R) (f x : R) in g (λR.R) R"
      -: "C R R"
  , te "let g = λ(f : α → α) x. C (f x : R) (f x : R) in g (λU.U) R"
  , "let g = λ(f : α → α) x. C (f x : R) (f x : R) in g (λU.U) U"
      -: "C R R"
  , "let g = λ(f : α → α) x. C (f x : L) (f x : R) in g (λL.R) U"
      -: "C L R"
  , te "let g = λ(f : α → α) x. C (f x : L) (f x : R) in g (λL.L) U"
  --
  -- qualifiers
  --
  , "λf g x. f (g x)"
      -: "∀ α β γ δ1 δ2. (β -δ2> γ) → (α -δ1> β) -δ2> α -δ1 δ2> γ"
  , "λf g x. f (f (g x))"
      -: "∀ α β δ1, δ2 : R. (β -δ2> β) → (α -δ1> β) -δ2> α -δ1 δ2> β"
  , "λf g x. f (f (g x x))"
      -: "∀ α:R, β δ1, δ2:R. (β -δ2> β) → (α -δ1> α -L> β) -δ2> α -δ1 δ2> β"
  , "λf. f (f X X) X"
      -: "(X -R> X -L> X) → X"
  , "λf g x. f (f (g x) C) C"
      -: "∀ α β, δ1:R, δ2. (β -δ1> C -L> β) → (α -δ2> β) -δ1> α -δ2 δ1> β"
  , "λf g x. f (f (g x) (g x)) (g x)"
      -: "∀ α:R, β, δ1 δ2:R. (β -δ2> β -L> β) → (α -δ1> β) -δ2> α -δ1 δ2> β"
  , "let f = bot : (B -L> B) → B in let g = bot : B -U> B in f g"
      -: "B"
  , te "let f = bot : (B -U> B) → B in let g = bot : B -L> B in f g"
  , te "let f = bot : (B -R> B) → B in let g = bot : B -A> B in f g"
  , "λ(x:α). let f = cast B : (B -L> B) → B in \
    \        let g = cast B : B -R> B in f g"
      -: "∀α:A. α → B"
  , "λ(x:α). let f = cast B : (B -L> B) → B in \
    \        let g = cast B : B -α> B in f g"
      -: "∀α:A. α → B"
  , "λ(x:Z -α> Z). let f = cast B:(B -L> B) → B in \
    \              let g = cast B:B -α> B in f g"
      -: "(Z -A> Z) → B"
  , "λ(x:α). let f = cast B : (B -α> B) → B in \
    \        let g = cast B : B -α> B in f g"
      -: "∀α:A. α → B"
  , "λ(x:α). let f = cast B : (B -α> B) → B in \
    \        let g = cast B : B -U> B in f g"
      -: "∀α:A. α → B"
  , te "λ(x:α). let f = cast B : (B -α> B) → B in \
       \        let g = cast B: B -A> B in f g"
  , "λ(x:B -α> B). let f = cast B : (B -α> B) → B in \
    \              let g = cast B : B -A> B in f g"
      -: "(B -A> B) → B"
  , "λ(x:α). let f = cast B : (B -A> B) → B in \
    \        let g = cast B : B -α> B in f g"
      -: "∀α:A. α → B"
  , "λ(x:α). let f = cast B : (B -U> B) → B in \
    \        let g = cast B : B -α> B in f g"
      -: "∀α:U. α → B"
  , "λ(x:α). let f = cast B : (B -R> B) → B in \
    \        let g = cast B : B -α> B in f g"
      -: "∀α:U. α → B"
  , te "λ(x:α). let f = cast B: (B -α> B) → B in \
    \           let g = cast B: B -L> B in f g"
  , "λ(f : (B -L> B) → B) (g : B -α> B). f g"
      -: "((B -L> B) → B) → (B -L> B) → B"
  , "λ(f : (B -α> B) → B) (g : B -L> B). f g"
      -: "((B -L> B) → B) → (B -L> B) → B"
  , "λ(f : (B -α> B) → B) (g : B -α> B). f g"
      -: "∀α. ((B -α> B) → B) → (B -α> B) → B"
  --
  , "(bot: (B -α> B) → B -α> B) (bot: B → B)"
      -: "B → B"
  , "(bot: (B -α> B) → B -α> B) (bot: B -R> B)"
      -: "B -R> B"
  , "(bot: (B -α> B) → B -α> B) (bot: B -R> B) : B -L> B"
      -: "B -L> B"
  , te "(bot: (B -α> B) → B -α> B) (bot: B -L> B) : B -R> B"
  --
  , "λ(_:α). (cast B: (B -α> B) → B) (cast B: B -α> B)"
      -: "∀α:A. α → B"
  , "λ(_:α) (_:β). (cast B: (B -α β> B) → B) (cast B: B -α> B)"
      -: "∀α β:A. α → β → B"
  , "λ(_:α) (_:β). (cast B: (B -α> B) → B) (cast B: B -α β> B)"
      -: "∀α:A, β:U. α → β → B"
  , "λ(x:α) (y:β). eat (P x y) ((cast B: (B -α> B) → B) (cast B: B -α β> B))"
      -: "∀α, β:U. α → β -α> B"
  --
  , "let rec f = λg x. let _ = f ((λC.C) : C -R> C) in g x in f"
      -: "∀α. (C -R α> C) → (C -R α> C)"
  --
  , "λ(Ref A x). x"
      -: "∀α. Ref A α → α"
  , "λ(Ref L x). x"
      -: "∀α. Ref L α → α"
  , "λ(r: Ref L α). r"
      -: "∀α. Ref L α → Ref L α"
  , "λ(f: Ref L α → α) (x: Ref L α). f x"
      -: "∀α. (Ref L α → α) → Ref L α → α"
  , "λ(f: Ref A α → α) (x: Ref A α). f x"
      -: "∀α. (Ref A α → α) → Ref A α → α"
  , te "λ(f: Ref L α → α) (x: Ref A α). f x"
  , te "λ(f: Ref A α → α) (x: Ref L α). f x"
  , "λ(f: Ref α β → β) (x: Ref α β). f x"
      -: "∀ α β. (Ref α β → β) → Ref α β → β"
  , "λx. match x with B _ → C"
      -: "∀ α:A. B α → C"
  , "choose ((λ_ _.X) : X -> X -R> X) ((λ_ _.X) : X -> X -A> X)"
      -: "X → X -L> X"
  --
  -- Generalization with non-empty Γ
  --
  , "λ(f : B -α> B). let g = λh. h f in Pair f g"
      -: "∀ α:R, β. (B -α> B) → Pair (B -α> B) (((B -α> B) -L> β) -α> β)"
  , "λ(f : B -α> B). let g = λh. h f in g"
      -: "∀ α β. (B -α> B) → ((B -α> B) -L> β) -α> β"
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
  , "λx. match x with `A y → y | `B y → y | _ → botU"
      -: "∀ α r. [ A: α | B: α | r ] → α"
  , "λx. match x with `A y → `B y | `B y → `A y | y → #A (#B y)"
      -: "∀ α β r. [ A: α | B: β | r ] → [ A: β | B: α | r]"
  , "λx. match x with `A y → `B y | `B y → `A y | y → #B (#A y)"
      -: "∀ α β r. [ A: α | B: β | r ] → [ A: β | B: α | r]"
  , "λf. f (`A M)"
      -: "∀ r β. ([ A: M | r ] -L> β) → β"
  , "λf. eat (f (`A M)) (f (`B N))"
      -: "∀ r β. ([ A: M | B: N | r ] -R> β) → β"
  , "λx. match x with `A _ → M | `B y → y"
      -: "∀ α:A. [ A: α | B: M ] → M"
  , "choose (`A ((λ_ _.X) : X -> X -R> X)) (`A ((λ_ _.X) : X -> X -A> X))"
      -: "∀ r. [ A: X → X -L> X | r ]"
  , "λx y. match x with `A U → y"
      -: "∀ α. [ A: U ] → α → α"
  , "λx y. match x with `A U → y | `B (U, U) → y"
      -: "∀ α. [ A: U | B: U × U ] → α → α"
  -- Equirecursive types
  , te "(botU : μa. M → [ A: a ]) N"
  , "(botU : μa. M → [ A: a ]) M"
      -: "μβ. [ A: M → β ]"
  , "let rec x = `A x in x"
      -: "∀γ:U. μα. [ A: α | γ ]"
  , "let rec x = #B (`A x) in x"
      -: "∀β γ: U. μα. [ A: α | B: β | γ ]"
  , "λx. choose x (`A x)"
      -: "∀γ: U. (μα. [ A: α | γ ]) → μα. [ A: α | γ ]"
  , "λx. choose x (#B (`A x))"
      -: "∀β γ: U. (μα. [ A: α | B: β | γ ]) → \
         \         μα. [ A: α | B: β | γ ]"
  , "let rec foldr = λf z xs.                   \
    \  match xs with                            \
    \  | `Cons (x, xs') → f x (foldr f z xs')   \
    \  | `Nil U         → z                     \
    \  in foldr                                 "
      -: "∀ α β. (α → β -L> β) → β →                 \
         \       (μγ. [ Cons: α × γ | Nil: U ]) -β> β"
  , "let rec foldl = λf z xs.                   \
    \  match xs with                            \
    \  | `Cons (x, xs') → foldl f (f x z) xs'   \
    \  | `Nil U         → z                     \
    \  in foldl                                 "
      -: "∀ α β. (α → β -L> β) → β →                 \
         \       (μγ. [ Cons: α × γ | Nil: U ]) -β> β"
  {-
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
    result ← timeout 100000 m
    case result of
      Just () → return ()
      Nothing → T.assertBool ("Timeout: " ++ a) False
