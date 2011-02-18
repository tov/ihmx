{-# LANGUAGE
      BangPatterns,
      DeriveFunctor,
      EmptyDataDecls,
      FlexibleInstances,
      FunctionalDependencies,
      ImplicitParams,
      MultiParamTypeClasses,
      ParallelListComp,
      PatternGuards,
      TupleSections,
      UndecidableInstances,
      UnicodeSyntax
  #-}
module Syntax where

import Control.Arrow
import Control.Applicative
import Control.Monad
import Control.Monad.Identity
import qualified Control.Monad.State as CMS
import Control.Monad.ST (runST)
import qualified Data.Char as Char
import qualified Data.List as List
import qualified Data.Map  as Map
import           Data.Monoid
import qualified Data.STRef as ST
import Text.Parsec hiding ((<|>), many)
import Text.Parsec.Token
import qualified Text.PrettyPrint as Ppr

import qualified Test.HUnit as T

import Util
import Parsable
import Ppr

---
--- Type constructor variance
---

data Variance = Omnivariant | Covariant | Contravariant | Invariant
  deriving (Eq, Show)

-- | Variances are a four point lattice with Invariant on top and
--   Omnivariant on the bottom
instance Bounded Variance where
  minBound = Omnivariant
  maxBound = Invariant

-- | Variances work like abstract sign arithmetic, where:
--    Omnivariant   = { 0 }
--    Covariant     = ℤ₊ = { 0, 1, 2, ... }
--    Contravariant = ℤ₋ = { 0, -1, -2, ... }
--    Invariant     = ℤ
--- In this view, addition gives the join for the variance lattice,
--  and multiplication gives the variance of composing type constructors
--  of the given variances.
instance Num Variance where
  Omnivariant   + v2            = v2
  v1            + Omnivariant   = v1
  Covariant     + Covariant     = Covariant
  Contravariant + Contravariant = Contravariant
  _             + _             = Invariant
  --
  Contravariant * Contravariant = Covariant
  Covariant     * v2            = v2
  v1            * Covariant     = v1
  Omnivariant   * _             = Omnivariant
  _             * Omnivariant   = Omnivariant
  _             * _             = Invariant
  --
  abs Omnivariant               = Omnivariant
  abs _                         = Covariant
  --
  signum                        = id
  --
  negate Covariant              = Contravariant
  negate Contravariant          = Covariant
  negate v                      = v
  --
  fromInteger i
    | i < 0     = Contravariant
    | i > 0     = Covariant
    | otherwise = Omnivariant

-- | For now, we hard-code the variances of several type constructors
--   and consider the rest to be covariant by default.
getVariances ∷ Name → Int → [Variance]
getVariances "->"    2 = [Contravariant, Covariant]
getVariances "→"     2 = [Contravariant, Covariant]
getVariances "Ref"   1 = [Invariant]
getVariances "Const" i = replicate i Omnivariant
getVariances _       i = replicate i Covariant

---
--- Empty – an uninhabited type
---

data Empty

elimEmpty ∷ Empty → a
elimEmpty = const undefined

instance Eq Empty where
  _ == _ = True

---
--- Representation of variables
---

type Name = String

-- | We use HIDE to hide data from derived instances of Eq. In
--   particular, variables will carry a name that is suitable for
--   printing, but it shouldn't have any effect on variable comparisons.
newtype HIDE a = HIDE { unHIDE ∷ a }
instance Eq (HIDE a) where _ == _ = True
instance Show a ⇒ Show (HIDE a) where showsPrec p = showsPrec p . unHIDE

-- | We're using the locally nameless representation for binding,
--   which means that bound variables are represented as DeBruijn
--   indices but free variables have some other representation as
--   specified by the type parameter.  At different stages, we may
--   represent free variables by names or by mutable references, for
--   example.
--
--   One consequence of this reprsentation is that a variable of type
--   Var Empty must be bound, since Empty is uninhabited.
--
--   We use two indices for bound variables, a rib number DeBruijn index
--   and the position of the variable within the rib.  Type quantifiers
--   bind multiple variables in a rib.  For example, in
--
--      ∀ α β γ. α → γ
--
--   we represent α with BoundVar 0 0 and γ with BoundVar 0 2.
data Var a
  = BoundVar !Int !Int (HIDE (Maybe Name))
  | FreeVar a
  deriving (Eq, Functor)

boundVar ∷ Int → Int → Name → Var a
boundVar ix jx n = BoundVar ix jx (HIDE (Just n))

---
--- Representation of types
---

-- | The syntax of types allows nested quantifiers, though right now
--   we actually handle only prenex type.  Currently we do no kind
--   checking and don't track arity of type constructors.
--
--   The type parameter gives the representation of free type variables.
data Type a
  -- | The Int is the number of bound variables
  = QuaTy Quant Int (Type a)
  | VarTy (Var a)
  | ConTy Name [Type a]
  deriving (Eq, Functor)

-- | Quantifiers
data Quant
  = AllQu
  | ExQu
  deriving Eq

allTy, exTy ∷ Int → Type a → Type a
allTy = QuaTy AllQu
exTy  = QuaTy ExQu

bvTy ∷ Int → Int → Maybe Name → Type a
bvTy i j n = VarTy (BoundVar i j (HIDE n))

fvTy ∷ a → Type a
fvTy  = VarTy . FreeVar

t1 ↦ t2 = ConTy "→" [t1, t2]
infixr 4 ↦

-- | The type of a dereferencing function for free type variable
--   representation @v@, in some monad @m@.
type Deref m v = v → m (Maybe (Type v))

-- | Fold a type, while dereferencing type variables
foldType ∷ (Monad m, ?deref ∷ Deref m v) ⇒
           -- | For quantifiers
           (Quant → Int → r → r) →
           -- | For bound variables
           (Int → Int → Maybe Name → r) →
           -- | For free variables
           (v → r) →
           -- | For constructor applications
           (Name → [r] → r) →
           -- | Type to fold
           Type v →
           m r
foldType fquant fbvar ffvar fcon = loop where
  loop (QuaTy q n t)                   = fquant q n `liftM` loop t
  loop (VarTy (BoundVar i j (HIDE n))) = return (fbvar i j n)
  loop (VarTy (FreeVar v))             = do
    mt ← ?deref v
    case mt of
      Nothing → return (ffvar v)
      Just t  → loop t
  loop (ConTy n ts)                    = fcon n `liftM` mapM loop ts

-- | Monadic version of type folding
foldTypeM ∷ (Monad m, ?deref ∷ Deref m v) ⇒
            (Quant → Int → r → m r) →
            (Int → Int → Maybe Name → m r) →
            (v → m r) →
            (Name → [r] → m r) →
            Type v →
            m r
foldTypeM fquant fbvar ffvar fcon t =
  join (foldType fquantM fbvar ffvar fconM t) where
    fquantM q i mr = fquant q i =<< mr
    fconM c mrs    = fcon c =<< sequence mrs

-- The type monad does substitution
instance Monad Type where
  QuaTy u e t            >>= f = QuaTy u e (t >>= f)
  VarTy (FreeVar r)      >>= f = f r
  VarTy (BoundVar i j n) >>= _ = VarTy (BoundVar i j n)
  ConTy n ts             >>= f = ConTy n (map (>>= f) ts)
  return = VarTy . FreeVar

-- | Apply a total substitution to a free type variable.  Total in this
--   case simply means that the type variable must be in the domain of
--   the substitution.
totalSubst ∷ Eq a ⇒ [a] → [Type b] → a → Type b
totalSubst (α:αs) (τ:τs) β
  | α == β          = τ
  | otherwise       = totalSubst αs τs β
totalSubst _ _ _ = error "BUG! substsAll saw unexpected free tv"

-- | Use the given function to substitute for the free variables
--   of a type; allows changing the ftv representation.
typeMapM ∷ Monad m ⇒ (a → m (Type b)) → Type a → m (Type b)
typeMapM f = foldTypeM (return <$$$> QuaTy)
                       (return <$$$> bvTy)
                       f
                       (return <$$> ConTy)
             where ?deref = const $ return Nothing

-- | Is the given type ground (type-variable and quantifier free)?
isGroundType ∷ (Monad m, ?deref ∷ Deref m v) ⇒ Type v → m Bool
isGroundType = foldType (\_ _ _ → False) (\_ _ _ → False)
                        (\_ → False) (\_ → and)

-- | Is the given type closed? (ASSUMPTION: The type is locally closed)
isClosedType ∷ (Monad m, ?deref ∷ Deref m v) ⇒ Type v → m Bool
isClosedType = foldType (\_ _ → id) (\_ _ _ → True) (\_ → False) (\_ → and)

-- | Is the given type quantifier free?
isMonoType ∷ (Monad m, ?deref ∷ Deref m v) ⇒ Type v → m Bool
isMonoType = foldType (\_ _ _ → False) (\_ _ _ → True) (\_ → True) (\_ → and)

-- | Is the given type (universal) prenex?
--   (Precondition: the argument is standard)
isPrenexType ∷ (Monad m, ?deref ∷ Deref m v) ⇒ Type v → m Bool
isPrenexType (QuaTy AllQu _ τ)   = isMonoType τ
isPrenexType (VarTy (FreeVar r)) = maybe (return True) isPrenexType =<< ?deref r
isPrenexType τ                   = isMonoType τ

---
--- Patterns
---

data Patt a
  = VarPa
  | WldPa
  | ConPa Name [Patt a]
  deriving Show

-- | The number of variables bound by a pattern
pattSize ∷ Patt a → Int
pattSize VarPa        = 1
pattSize WldPa        = 0
pattSize (ConPa _ πs) = sum (map pattSize πs)

---
--- Terms
---

data Term a
  = AbsTm (Patt a) (Term a)
  -- | The first field is true for a "let rec"
  | LetTm Bool (Patt a) (Term a) (Term a)
  | VarTm (Var a)
  | ConTm Name [Term a]
  | AppTm (Term a) (Term a)

syntacticValue ∷ Term a → Bool
syntacticValue (AbsTm _ _)       = True
syntacticValue (LetTm _ _ e1 e2) = syntacticValue e1 && syntacticValue e2
syntacticValue (VarTm _)         = True
syntacticValue (ConTm _ es)      = all syntacticValue es
syntacticValue (AppTm _ _)       = False

---
--- Initial environment
---

γ0' ∷ [(Name, String)]
γ0' = [ ("id",          "∀ α. α → α")
      , ("choose",      "∀ α. α → α → α")
      , ("apply",       "∀ α β. (α → β) → α → β")
      , ("revapp",      "∀ α β. α → (α → β) → β")
      -- Lists
      , ("single",      "∀ α. α → List α")
      , ("nil",         "∀ α. List α")
      , ("cons",        "∀ α. α → List α → List α")
      , ("map",         "∀ α β. (α → β) → List α → List β")
      , ("foldr",       "∀ α β. (α → β → β) → β → List α → β")
      , ("head",        "∀ α. List α → α")
      , ("tail",        "∀ α. List α → List α")
      , ("app",         "∀ α. List α → List α → List α")
      -- Ref cells
      , ("ref",         "∀ α. α → Ref α")
      , ("readRef",     "∀ α. Ref α → α")
      , ("writeRef",    "∀ α. Ref α → α → T")
      -- Products
      , ("pair",        "∀ α β. α → β → Pair α β")
      , ("fst",         "∀ α β. Pair α β → α")
      , ("snd",         "∀ α β. Pair α β → β")
      -- Sums
      , ("inl",         "∀ α. α → all β. Either α β")
      , ("inr",         "∀ β. β → all α. Either α β")
      , ("either",      "∀ α β γ. (α → γ) → (β → γ) → Either α β → γ")
      -- Any
      , ("bot",         "∀ α. α")
      ]

γ0 ∷ [Type Empty]
γ0  = map (read . snd) γ0'

---
--- Locally nameless operations
---

-- | @openTy k τs τ@ substitutes @τs@ for the bound type variables at
--   rib level @k@.  DeBruijn indices higher than @k@ are adjusted downward,
--   since opening a type peels off a quantifier.
openTy ∷ Int → [Type a] → Type a → Type a
openTy  = openTyN 1

-- | Generalization of 'openTy': the first argument specifies how much
--   to adjust indices that exceed @k@.
openTyN ∷ Int → Int → [Type a] → Type a → Type a
openTyN n k vs (QuaTy u e t) = QuaTy u e (openTyN n (k + 1) vs t)
openTyN n k vs (VarTy (BoundVar i j name))
  | i > k      = VarTy (BoundVar (i - n) j name)
  | i == k, Just t ← listNth j vs
              = t
  | otherwise = VarTy (BoundVar i j name)
openTyN _ _ _  (VarTy (FreeVar v)) = VarTy (FreeVar v)
openTyN n k vs (ConTy name ts) = ConTy name (map (openTyN n k vs) ts)

-- | @closeTy k αs τ@ finds the free variables @αs@ and replaces them
--   with bound variables at rib level @k@.  The position of each type
--   variable in @αs@ gives the index of each bound variable into the
--   new rib.
closeTy ∷ Eq a ⇒ Int → [a] → Type a → Type a
closeTy k vs (QuaTy u e t) = QuaTy u e (closeTy (k + 1) vs t)
closeTy k _  (VarTy (BoundVar i j n))
  | i >= k    = VarTy (BoundVar (i + 1) j n)
  | otherwise = VarTy (BoundVar i j n)
closeTy k vs (VarTy (FreeVar v))
  | Just j ← List.findIndex (== v) vs
              = VarTy (BoundVar k j (HIDE Nothing))
  | otherwise = VarTy (FreeVar v)
closeTy k vs (ConTy n ts) = ConTy n (map (closeTy k vs) ts)

-- | Add the given quantifier while binding the given list of variables
closeWith ∷ Eq a ⇒ Quant → [a] → Type a → Type a
closeWith _ []  ρ = ρ
closeWith q tvs ρ = QuaTy q (length tvs) (closeTy 0 tvs ρ)

-- | @substTy τ' α 't@ substitutes @τ'@ for free variable @α@ in @τ@.
substTy ∷ Eq a ⇒ Type a → a → Type a → Type a
substTy τ' α = runIdentity . typeMapM each where
  each β | α == β    = return τ'
         | otherwise = return (fvTy β)

-- | Is the given type locally closed?  A type is locally closed
--   if none of its bound variables point to quantifiers "outside" the
--   type.
--
--   ASSUMPTION: No bound variables are lurking behind an apparent free
--   variable, because @lcTy@ doesn't attempt to dereference free
--   variables.  This should be an invariant, because it would come
--   about only as a result of a capturing substitution.
lcTy ∷ Type a → Bool
lcTy  = loop 0 where
  loop k (QuaTy _ _ t)            = loop (k + 1) t
  loop k (VarTy (BoundVar i _ _)) = k > i
  loop _ (VarTy (FreeVar _))      = True
  loop k (ConTy _ ts)             = all (loop k) ts

-- | Are there no bound vars of level k?
lcTyK ∷ Int → Type a → Bool
lcTyK  = loop where
  loop k (QuaTy _ _ t)            = loop (k + 1) t
  loop k (VarTy (BoundVar i _ _)) = k /= i
  loop _ (VarTy (FreeVar _))      = True
  loop k (ConTy _ ts)             = all (loop k) ts

---
--- Free type variables
---

{-
  We're going to construct a framework for generic functions to compute
  the free type variables of a type.  It may be a bit over-engineered.
  The idea is to write a generic function that builds an 'FtvTree',
  which contains all the free type variables in the relevant piece of
  syntax, along with variance information.
-}

-- | A tree of free type variables, with variance information
data FtvTree v
  -- | A single free type variable
  = FTSingle v
  -- | Updates the incoming variance to give the variance in
  --   the subtree
  | FTVariance (Variance → Variance) (FtvTree v)
  -- | A forest of 'FtvTree's
  | FTBranch [FtvTree v]

instance Monoid (FtvTree v) where
  mempty      = FTBranch []
  mappend a b = FTBranch [a, b]
  mconcat     = FTBranch

-- | A fold for 'FtvTree's. It's necessary to specify how to
--   add a free type variable and its variance to the result, and the
--   initial result.  Note that this fold gives no information about
--   the shape of the tree, but it uses the tree structure to determine
--   the variance of each type variable.
foldFtvTree ∷ (v → Variance → r → r) → r → FtvTree v → r
foldFtvTree each = loop Covariant where
  loop var zero (FTSingle v)       = each v var zero
  loop var zero (FTVariance vf t)  = loop (vf var) zero t
  loop var zero (FTBranch ts)      = foldr (flip (loop var)) zero ts

-- | Type class for finding the free type variables (of type @v@) in a
--   syntactic entity (of type @a@).
class Ord v ⇒ Ftv a v | a → v where
  -- | To compute the 'FtvTree' for a piece of syntax.  Because
  --   everything is parametric in the representation of ftvs, it needs
  --   to be told how to dereference an apparently free type variable.
  --   The dereferencing function should return @Nothing@ if the type
  --   variable is actually free, and @Just τ@ if a type @τ@ has been
  --   substituted for it.
  --
  --   This is the only method that doesn't have a default
  --   implementation, so it must be defined explicitly.
  ftvTree  ∷ (Monad m, ?deref ∷ Deref m v) ⇒ a → m (FtvTree v)
  -- | To fold over the free type variables in a piece of syntax.
  ftvFold  ∷ (Monad m, ?deref ∷ Deref m v) ⇒
             (v → Variance → r → r) → r → a → m r
  -- | To find all the type variables and their variances. Will repeat
  --   type variables that occur more than once.
  ftvList  ∷ (Monad m, ?deref ∷ Deref m v) ⇒ a → m [(v, Variance)]
  -- | To get a map from free type variables to their variances.
  ftvV     ∷ (Monad m, ?deref ∷ Deref m v) ⇒ a → m (Map.Map v Variance)
  -- | To get a map from free type variables to a list of all their
  --   occurrences' variances.
  ftvVs    ∷ (Monad m, ?deref ∷ Deref m v) ⇒ a → m (Map.Map v [Variance])
  -- | To get a list of the free type variables in a type (with no repeats).
  ftvM     ∷ (Monad m, ?deref ∷ Deref m v) ⇒ a → m [v]
  -- | To get a list of the APPARENTLY free type variables in a type
  --   (with no repeats).  Makes no attempt to dereference type
  --   variables.
  ftvS     ∷ a → [v]
  --
  ftvFold each zero a
                 = foldFtvTree each zero `liftM` ftvTree a
  ftvList        = ftvFold (curry (:)) []
  ftvV           = ftvFold (Map.insertWith (+)) Map.empty
  ftvVs          = ftvFold (\v a → Map.insertWith (++) v [a]) Map.empty
  ftvM a         = liftM (ordNub . map fst) (ftvList a)
  ftvS           = runIdentity . ftvM where ?deref = const (return Nothing)

instance Ord v ⇒ Ftv (Type v) v where
  ftvTree = foldType
             (\_ _ tree → tree)
             (\_ _ _ → mempty)
             FTSingle
             (\c trees → FTBranch
                 [ FTVariance (* var) tree
                 | tree ← trees
                 | var  ← getVariances c (length trees) ])

instance Ftv a v ⇒ Ftv [a] v where
  ftvTree a = FTBranch `liftM` mapM ftvTree a

instance (Ftv a v, Ftv b v) ⇒ Ftv (a,b) v where
  ftvTree (a,b) = liftM2 mappend (ftvTree a) (ftvTree b)

instance (Ftv a v, Ftv b v, Ftv c v) ⇒ Ftv (a,b,c) v where
  ftvTree (a,b,c) = ftvTree (a,(b,c))

instance Ftv a v ⇒ Ftv (Maybe a) v where
  ftvTree = maybe (return mempty) ftvTree

instance (Ftv a v, Ftv b v) ⇒ Ftv (Either a b) v where
  ftvTree = either ftvTree ftvTree

---
--- Unfolds for syntax
---

-- To strip off as many of the specified quantifier as possible,
-- counting how many layers are stripped.
unfoldQua ∷ Quant → Type a → (Int, Type a)
unfoldQua u (QuaTy u' _ t)
  | u == u' || lcTyK 0 t     = first (+ 1) (unfoldQua u t)
unfoldQua _ t                = (0, t)

-- To find the operator and operands of a curried application.
unfoldApp ∷ Term a → (Term a, [Term a])
unfoldApp (AppTm e1 e2) = second (++[e2]) (unfoldApp e1)
unfoldApp e             = (e, [])

-- To find the parameters and body of a curried function.
unfoldAbs ∷ Term a → ([Patt a], Term a)
unfoldAbs (AbsTm π e) = first (π:) (unfoldAbs e)
unfoldAbs e           = ([], e)

---
--- Parsing
---

-- | @standardizeType@ puts a type in standard form.
--   A type is in standard form if three conditions are met:
--
--   * All bound type variables actually appear in their scope.  That
--     is, ‘∀ α β γ. α → γ’ is not standard, but ‘∀ α γ. α → γ’ is.
--
--   * The same quantifier never nests directly inside itself.  That is,
--     ‘∀ α β. ∀ γ. C α β γ’ is not standard, but ‘∀ α β γ. C α β γ’ is.
--
--   * The bound type variables of each quantifier are listed in the
--     order that they appear in its scope.  That is,
--     ‘∀ α β γ. C α γ β’ is not standard, but ‘∀ α β γ. C α β γ’ is.
--
--  Type standardization is necessary as a post-pass after parsing,
--  because it's difficult to parse into standard form directly.
standardizeType ∷ Type a → Type a
standardizeType t00 = runST (loop 0 [] t00) where
  loop depth g t0 = case t0 of
    QuaTy u _ _ → do
      let (i, t) = unfoldQua u t0
      rn ← ST.newSTRef []
      t' ← loop (depth + i)
                (foldr (++) g $
                   replicate i [(depth + i, rn)]) t
      nl ← ST.readSTRef rn
      return $ case length nl of
        0 → openTyN i (-1) [] t'
        n → QuaTy u n (openTyN (i - 1) (i - 1) [] t')
    ConTy con ts          → ConTy con <$> mapM (loop depth g) ts
    VarTy (BoundVar i j n)
      | (olddepth, r):_ ← drop i g
                          → do
          s  ← ST.readSTRef r
          j' ← case List.findIndex (== (depth - i,j)) s of
            Just j' → return j'
            Nothing → do
              ST.writeSTRef r (s ++ [(depth - i,j)])
              return (length s)
          return (VarTy (BoundVar (depth - olddepth) j' n))
    VarTy v               → return (VarTy v)

-- | A Parsec tokenizer
tok ∷ TokenParser st
tok  = makeTokenParser LanguageDef {
  commentStart = "{-",
  commentEnd   = "-}",
  commentLine  = "--",
  nestedComments = True,
  identStart   = noλ $ upper <|> lower <|> oneOf "_",
  identLetter  = noλ $ alphaNum <|> oneOf "_'′₀₁₂₃₄₅₆₇₈₉⁰¹²³⁴⁵⁶⁷⁸⁹",
  opStart      = empty,
  opLetter     = empty,
  reservedNames   = ["all", "ex", "let", "in", "rec"],
  reservedOpNames = ["->", "→", ".", "\\", "λ", "=", ":", "∀", "∃"],
  caseSensitive   = True
}
  -- 'λ' is not an identifier character, so that we can use it as
  -- a reserved operator. Otherwise, we'd need a space after it.
  where noλ p = notFollowedBy (char 'λ') *> p

-- | Run a parser in the context of a different parsing state.
withState ∷ st → Parsec String st a → Parsec String st a
withState st p = do
  old ← getState
  setState st
  a   ← p
  setState old
  return a

-- | @identifierSat descr pred@ parses an identifer that satisfies
--   @pred@, or fails with message @descr@.
identifierSat ∷ String → (Name → Bool) → P Name
identifierSat descr pred = try $ do
  s ← identifier tok
  if pred s
    then return s
    else empty <?> descr

upperIdentifier, lowerIdentifier ∷ P Name
upperIdentifier = identifierSat "uppercase identifier" (Char.isUpper . head)
lowerIdentifier = identifierSat "lowercase identifier" (Char.isLower . head)

-- | Attempts to parse the uninhabited type 'Empty' always fail.
instance Parsable Empty where
  genParser = empty

-- | Given the name of a variable and an environment comprising
--   a list of ribs of names, attempts to find the index of the name
--   in the environment and construct a bound variable. If the name
--   doesn't appear in the environment, it also looks in the parser
--   state, which is considered to be the next rib after the given
--   environment.
findVar ∷ Name → [[Name]] → P (Var a)
findVar name = loop 0 where
  loop !ix [] = do
    somes ← getState
    case List.findIndex (== name) somes of
      Just jx → return (boundVar ix jx name)
      Nothing → do
        setState (somes ++ [name])
        return (boundVar ix (length somes) name)
  loop !ix (rib:ribs) = case findLastIndex (== name) rib of
    Just jx → return (boundVar ix jx name)
    Nothing → loop (ix + 1) ribs

-- | To parse a closed type.
instance Parsable (Type a) where
  genParser  = withState [] $ do
    t ← parseType
    somes ← getState
    case somes of
      [] → return t
      _  → fail ("Open type: " ++ show somes)

-- | To parse a (potentially open) type.  Adds the names of any free
--   variables encountered to the parse state in the order that their
--   seen, and binds them to an outermost rib.
parseType ∷ P (Type a)
parseType  = level0 []
  where
  level0 g = do
               (quants, tvss) ← unzip <$> parseQuantifiers
               body   ← level0 (reverse tvss ++ g)
               return (foldr2 QuaTy body quants (map length tvss))
         <|> level1 g
  level1 g = do
               t1 ← level2 g
               option t1 $ do
                 reservedOp tok "→" <|> reservedOp tok "->"
                 t2 ← level0 g
                 return (t1 ↦ t2)
  level2 g = ConTy <$> upperIdentifier <*> many (level3 g)
         <|> level3 g
  level3 g = do
               tv ← lowerIdentifier
               VarTy <$> findVar tv g
         <|> do
               con ← upperIdentifier
               return (ConTy con [])
         <|> parens tok (level0 g)

-- To parse a sequence of quantifiers along with their bound variables.
parseQuantifiers ∷ P [(Quant, [Name])]
parseQuantifiers = many1 ((,) <$> quant <*> tvs) <* dot tok where
  quant   = AllQu <$ (reserved tok "all" <|> reservedOp tok "∀")
        <|> ExQu  <$ (reserved tok "ex"  <|> reservedOp tok "∃")
  tvs     = do
    ids ← many1 lowerIdentifier
    when (List.nub ids /= ids) $
      fail "repeated tyvar in quantifier group"
    return ids

-- To parse a pattern. Produces the pattern (which is nameless) and
-- the list of names bound by the patern.
parsePatt ∷ Int → P (Patt a, [Name])
parsePatt p = withState [] $ (,) <$> level p <*> getState where
  level 0 = level 1
  level 1 = ConPa <$> upperIdentifier <*> many (level 2)
        <|> level 2
  level _ = ConPa <$> upperIdentifier <*> pure []
        <|> WldPa <$  reserved tok "_"
        <|> VarPa <$  variable
        <|> parens tok (level 0)
  variable = do
    name  ← lowerIdentifier
    names ← getState
    if name `elem` names
      then unexpected ("repeated variable in pattern: " ++ name)
      else putState (names++[name])

-- | To parse a closed term.
instance Parsable (Term a) where
  genParser  = withState [] $ do
    (e, free) ← parseTerm (map fst γ0')
    case free of
      [] → return e
      _  → fail ("Open term: " ++ show free)

-- | To parse a (potentially open) term. Free variables are handled as
--   in 'parseType'.
parseTerm ∷ [Name] → P (Term a, [Name])
parseTerm γ0 = liftM2 (,) (level0 [γ0]) getState where
  level0 γ = do
               reserved tok "let"
               rec ← option False (True <$ reserved tok "rec")
               (π, names) ← parsePatt 0
               reservedOp tok "="
               e1 ← level0 (if rec then names:γ else γ)
               reserved tok "in"
               e2 ← level0 (names : γ)
               return (LetTm rec π e1 e2)
         <|> do
               reservedOp tok "\\" <|> reservedOp tok "λ"
               (πs, names) ← unzip <$> many1 (parsePatt 3)
               dot tok
               e ← level0 (reverse names ++ γ)
               return (foldr AbsTm e πs)
         <|> level1 γ
  level1 γ = level2 γ
  level2 γ = ConTm <$> upperIdentifier <*> many (level3 γ)
         <|> chainl1 (level3 γ) (return AppTm)
  level3 γ = do
               v ← lowerIdentifier
               VarTm <$> findVar v γ
         <|> do
               con ← upperIdentifier
               return (ConTm con [])
         <|> parens tok (level0 γ)

instance Parsable a ⇒ Read (Type a) where
  readsPrec _ = readsPrecFromParser

instance Parsable a ⇒ Read (Term a) where
  readsPrec _ = readsPrecFromParser

---
--- Pretty-printing
---

-- | Given a base name, produces the list of names starting with the
--   base name, then with a prime added, and then with numeric
--   subscripts increasing from 1.
namesFrom ∷ String → [Name]
namesFrom s = [ c:n | n ← "" : "′" : map numberSubscript [1 ..], c ← s ]

-- | Given a natural number, represent it as a string of number
--   subscripts.
numberSubscript ∷ Int → String
numberSubscript 0  = "₀"
numberSubscript n0
  | n0 < 0         = error "numberSubscript requires non-negative Int"
  | otherwise      = reverse $ List.unfoldr each n0 where
  each 0 = Nothing
  each n = Just (digits !! ones, rest) where (rest, ones) = n `divMod` 10
  digits = "₀₁₂₃₄₅₆₇₈₉"

-- | Lists of name candidates for type variables, exotic type variables
--   (during unification), and variables.
tvNames, exNames, varNames ∷ [Name]
tvNames = namesFrom "αβγδ"
exNames = namesFrom "efgh"
varNames = namesFrom ['i' .. 'z']

instance Ppr Empty where
  ppr = elimEmpty

instance Ppr a ⇒ Ppr (Type a) where
  ppr = pprType []

-- | To pretty-print a type
pprType ∷ Ppr a ⇒ [[Name]] → Type a → Ppr.Doc
pprType  = loop 0 where
  loop p g t0 = case t0 of
    QuaTy u e t           →
      let quant = case u of AllQu → "∀"; ExQu → "∃"
          tvs   = take e (filter (`notElem` concat g) tvNames)
       in parensIf (p > 0) $
            Ppr.hang
              (Ppr.text quant Ppr.<+>
               Ppr.fsep (map Ppr.text tvs) Ppr.<>
               Ppr.char '.')
              2
              (loop 0 (tvs : g) t)
    VarTy (BoundVar ix jx (HIDE n)) →
      Ppr.text $ maybe "?" id $ (listNth jx <=< listNth ix $ g) `mplus` n
    VarTy (FreeVar a)        → ppr a
    ConTy c [t1, t2] | c `elem` ["->", "→"] →
      parensIf (p > 1) $
        Ppr.sep [loop 2 g t1, Ppr.text "→", loop 0 g t2]
    ConTy c []          → Ppr.text c
    ConTy c ts          →
      parensIf (p > 2) $
        Ppr.fsep (Ppr.text c : map (loop 3 g) ts)

-- | To pretty-print a pattern using the given list of names
--   for its bound variables.
pprPatt ∷ Ppr a ⇒ Int → [Name] → Patt a → Ppr.Doc
pprPatt p0 names0 π0 = CMS.evalState (loop p0 π0) names0 where
  loop _ VarPa = Ppr.text <$> next
  loop _ WldPa = return (Ppr.char '_')
  loop _ (ConPa c []) = return (Ppr.text c)
  loop p (ConPa c πs) = do
    docs ← mapM (loop 2) πs
    return $
      parensIf (p > 1) $
        Ppr.sep (Ppr.text c : docs)
  next = do
    name:names ← CMS.get
    CMS.put names
    return name

-- | Too pretty-print a closed term.
instance Ppr a ⇒ Ppr (Term a) where
  ppr = pprTerm []

-- | To pretty-print a term, given a name environment.
pprTerm ∷ Ppr a ⇒ [[Name]] → Term a → Ppr.Doc
pprTerm  = loop 0 where
  loop p g e0 = case e0 of
    AbsTm _ _           →
      let (πs, e) = unfoldAbs e0
          freshNames = filter (`notElem` concat g) varNames
          alloc (vs', fresh) π = (vs' ++ [used], fresh')
            where (used, fresh') = splitAt (pattSize π) fresh
          names = fst (foldl alloc ([], freshNames) πs)
       in parensIf (p > 0) $
            Ppr.hang
              (Ppr.char 'λ'
                 Ppr.<> Ppr.fsep (zipWith (pprPatt 3) names πs)
                 Ppr.<> Ppr.char '.')
              2
              (loop 0 (reverse names ++ g) e)
    LetTm rec π e1 e2   →
      let fresh  = filter (`notElem` concat g) varNames
          names  = take (pattSize π) fresh
       in parensIf (p > 0) $
            Ppr.hang
              (Ppr.text (if rec then "let rec" else "let")
                Ppr.<+> pprPatt 0 names π
                Ppr.<+> Ppr.char '='
                Ppr.<+> loop 0 (if rec then names : g else g) e1
                Ppr.<+> Ppr.text "in")
              2
              (loop 0 (names : g) e2)
    VarTm (BoundVar ix jx (HIDE n)) →
      Ppr.text $ maybe "?" id $ (listNth jx <=< listNth ix $ g) `mplus` n
    VarTm (FreeVar name)   → ppr name
    ConTm name es       → parensIf (p > 2) $
      Ppr.sep (Ppr.text name : map (loop 3 g) es)
    AppTm e1 e2         → parensIf (p > 2) $
      Ppr.sep [loop 2 g e1, loop 3 g e2]

instance Ppr a ⇒ Show (Type a) where
  show = Ppr.render . ppr

instance Ppr a ⇒ Show (Term a) where
  show = Ppr.render . ppr

tests, syntaxTests ∷ IO ()

syntaxTests = tests
tests       = do
  T.runTestTT parseTypeTests
  T.runTestTT standardizeTypeTests
  return ()

(==>) ∷ String → Type Empty → T.Assertion
str ==> t = T.assertBool str (reads str == [(t, [])])

(<==>) ∷ String → String → T.Assertion
str1 <==> str2 = T.assertBool (str1 ++ " <==> " ++ str2) (t1 == t2) where
  t1, t2 ∷ [(Type Empty, String)]
  t1 = reads str1
  t2 = reads str2

parseTypeTests ∷ T.Test
parseTypeTests = T.test
  [ "A"                         ==> a
  , "A → B"                     ==> (a ↦ b)
  , "∀ α. α"                    ==> allTy 1 (bv 0 0)
  , "∀ α β. α"                  ==> allTy 2 (bv 0 0)
  , "∀ α β. β"                  ==> allTy 2 (bv 0 1)
  , "∃ α. α"                    ==> exTy 1 (bv 0 0)
  , "∃ α β. α"                  ==> exTy 2 (bv 0 0)
  , "∃ α β. β"                  ==> exTy 2 (bv 0 1)
  , "∀ α β. C α → C β"
      ==> allTy 2 (c (bv 0 0) ↦ c (bv 0 1))
  , "∀ α. ∀ β. C α → C β → A"
      ==> allTy 1 (allTy 1 (c (bv 1 0) ↦ c (bv 0 0) ↦ a))
  , "∀ α. α → ∀ β. β → α"
      ==> allTy 1 (bv 0 0 ↦ allTy 1 (bv 0 0 ↦ bv 1 0))
  , "∃ α β. C α → C β"
      ==> exTy 2 (c (bv 0 0) ↦ c (bv 0 1))
  , "∃ α. ∃ β. C α → C β → A"
      ==> exTy 1 (exTy 1 (c (bv 1 0) ↦ c (bv 0 0) ↦ a))
  , "∃ α. α → ∃ β. β → α"
      ==> exTy 1 (bv 0 0 ↦ exTy 1 (bv 0 0 ↦ bv 1 0))
  , "∃ α ∀ β. C α → C β → A"
      ==> exTy 1 (allTy 1 (c (bv 1 0) ↦ c (bv 0 0) ↦ a))
  , "∃ α. α → ∀ β. β → α"
      ==> exTy 1 (bv 0 0 ↦ allTy 1 (bv 0 0 ↦ bv 1 0))
  , "∀ α β. α → β"              <==> "∀ β α. β → α"
  , "∀ α. C α → ∀ α. C α"       <==> "∀ δ. C δ → ∀ e. C e"
  , "∃ α β. α → β"              <==> "∃ β α. β → α"
  , "∃ α. C α → ∃ α. C α"       <==> "∃ δ. C δ → ∃ e. C e"
  ]
  where
    a = ConTy "A" []
    b = ConTy "B" []
    c t = ConTy "C" [t]
    bv m n = VarTy (BoundVar m n (HIDE Nothing))

(<==>*) ∷ String → String → T.Assertion
str1 <==>* str2 = T.assertBool (str1 ++ " <==> " ++ str2) (t1 == t2) where
  t1, t2 ∷ [(Type Empty, String)]
  t1 = map (first standardizeType) (reads str1)
  t2 = map (first standardizeType) (reads str2)

standardizeTypeTests ∷ T.Test
standardizeTypeTests = T.test
  [ "A"                         <==>* "A"
  , "A → B"                     <==>* "A → B"
  , "∀ α. α"                    <==>* "∀ α. α"
  , "∀ α β. α"                  <==>* "∀ α. α"
  , "∀ α β. β"                  <==>* "∀ α. α"
  , "∀ α β. C α → C β"
      <==>* "∀ α β. C β → C α"
  , "∀ α. ∀ β. C α → C β → A"
      <==>* "∀ α β. C β → C α → A"
  , "∀ α. α → ∀ β. β → α"
      <==>* "∀ α. α → ∀ β. β → α"
  , "∀ α. α → ∀ β. α"
      <==>* "∀ α. α → α"
  , "∀ α. α → ∀ β. ∀ γ. α"
      <==>* "∀ α. α → α"
  , "∀ α. α → ∀ β. ∀ γ. A α β γ"
      <==>* "∀ α. α → ∀ β γ. A α β γ"
  , "∀ α β. α → β"              <==>* "∀ β α. β → α"
  , "∀ α. C α → ∀ α. C α"       <==>* "∀ δ. C δ → ∀ e. C e"
  , "∀ α β γ δ. A"              <==>* "A"
  , "∀ α β γ δ. δ"              <==>* "∀ α. α"
  , "∀ α. ∀ β. ∀ γ. ∀ δ. (α → β) → α → δ"
      <==>* "∀ α β γ. (γ → β) → γ → α"
  , "∀ α β γ. A β"              <==>* "∀ α. A α"
  , "∀ α' β'. β' → ∀ α β γ. A β → α'"
                                <==>* "∀ α β. α → ∀ γ. A γ → β"
  , "∃ α' ∀ β'. β' → ∀ α β γ. A β → α'"
                                <==>* "∃ β. ∀ α. α → ∀ γ. A γ → β"
  , "∃ α' ∀ β'. β' → ∀ α β γ. A β' → α'"
                                <==>* "∃ β. ∀ α. α → A α → β"
  , let str = "∀ α. α → ∀ β. β → α" in
    T.assertBool str
      ((standardizeType (read str) ∷ Type Empty) ==
       allTy 1 (VarTy (boundVar 0 0 "α") ↦
                allTy 1 (VarTy (boundVar 0 0 "β") ↦
                         VarTy (boundVar 1 0 "α"))))
  ]

{-
tryParsePprPatt ∷ String → IO ()
tryParsePprPatt s =
  case runParser (parsePatt 0 <* eof) [] "" s of
    Left e              → print e
    Right (patt, names) → print (pprPatt 0 names (patt ∷ Patt Empty))

-}
