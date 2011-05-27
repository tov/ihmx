{-# LANGUAGE
      BangPatterns,
      DeriveFunctor,
      EmptyDataDecls,
      ExistentialQuantification,
      FlexibleInstances,
      FunctionalDependencies,
      ImplicitParams,
      MultiParamTypeClasses,
      ParallelListComp,
      PatternGuards,
      StandaloneDeriving,
      TupleSections,
      TypeSynonymInstances,
      UndecidableInstances,
      UnicodeSyntax,
      ViewPatterns
  #-}
module Syntax where

import Control.Arrow
import Control.Applicative
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Reader     as CMR
import Control.Monad.Writer     as CMW
import Control.Monad.RWS        as RWS
import Control.Monad.ST (runST)
import qualified Data.Char      as Char
import qualified Data.List      as List
import qualified Data.Map       as Map
import qualified Data.Set       as Set
import qualified Data.STRef     as ST
import Text.Parsec hiding ((<|>), many, optional)
import Text.Parsec.Token
import qualified Text.PrettyPrint as Ppr
import qualified Unsafe.Coerce

import qualified Test.HUnit as T

import Util
import Parsable
import Ppr
import qualified Stream

---
--- Some algebra / order theory
---

class Eq a ⇒ Lattice a where
  (⊔), (⊓) ∷ a → a → a
  (⊑), (⊒) ∷ a → a → Bool
  a ⊑ b = a ⊔ b == b
  a ⊒ b = b ⊑ a

class (Bounded a, Lattice a) ⇒ BoundedLattice a where
  bigJoin, bigMeet ∷ [a] → a

instance (Bounded a, Lattice a) ⇒ BoundedLattice a where
  bigJoin = foldr (⊔) minBound
  bigMeet = foldr (⊓) maxBound

newtype DUAL a = DUAL { dual ∷ a } deriving (Eq, Show)

instance Lattice a ⇒ Lattice (DUAL a) where
  DUAL a ⊔ DUAL b = DUAL (a ⊓ b)
  DUAL a ⊓ DUAL b = DUAL (a ⊔ b)

instance Lattice a ⇒ Lattice (Stream.Stream a) where
  (⊔) = liftM2 (⊔)
  (⊓) = liftM2 (⊓)

instance Bounded a ⇒ Bounded (DUAL a) where
  minBound = DUAL maxBound
  maxBound = DUAL minBound

instance Ord a ⇒  Ord (DUAL a) where
  DUAL a `compare` DUAL b = b `compare` a

---
--- Usage qualifiers
---

infixl 6 ⊔
infixl 7 ⊓
infix 4 ⊑, ⊒

data QLit = U | R | A | L
  deriving (Eq, Show)

readQLit ∷ String → Maybe QLit
readQLit "U" = Just U
readQLit "R" = Just R
readQLit "A" = Just A
readQLit "L" = Just L
readQLit _   = Nothing

instance Bounded QLit where
  minBound = U
  maxBound = L

instance Lattice QLit where
  U ⊔ q = q; q ⊔ U = q
  R ⊔ A = L; R ⊔ R = R
  A ⊔ A = A; A ⊔ R = L
  L ⊔ _ = L; _ ⊔ L = L
  --
  U ⊓ _ = U; _ ⊓ U = U
  R ⊓ A = U; R ⊓ R = R
  A ⊓ A = A; A ⊓ R = U
  L ⊓ q = q; q ⊓ L = q

-- | @a \-\ b@ is the least @c@ such that
--   @a ⊑ b ⊔ c@.  (This is sort of dual to a pseudocomplement.)
(\-\) ∷ QLit → QLit → QLit
L \-\ R = A
L \-\ A = R
a \-\ b = if a ⊑ b then U else a

-- | The intent is that only well-formed qualifiers should be wrapped
--   in 'QExp'.
data QExp v = QExp QLit [Var v]
  deriving (Show, Functor)

unQExp ∷ QExp tv → Type tv
unQExp (QExp ql vs) = ConTy (show ql) (map VarTy vs)

qlitexp   ∷ QLit → QExp tv
qlitexp q = QExp q []

qvarexp   ∷ Var v → QExp v
qvarexp v = QExp U [v]

instance Monoid (QExp v) where
  mempty = qlitexp U
  QExp L  _  `mappend` _            = qlitexp L
  _          `mappend` QExp L   _   = qlitexp L
  QExp R  _  `mappend` QExp A   _   = qlitexp L
  QExp A  _  `mappend` QExp R   _   = qlitexp L
  QExp ql vs `mappend` QExp ql' vs' = QExp (ql ⊔ ql') (vs ++ vs')

-- | For now, we hard-code the qualifiers of several type constructors
--   and consider the rest to be like tuples by default.
--   PRECONDITION: The arguments are well-formed qualifiers.
--   POSTCONDITION: The result is a well-formed qualifiers.
getQualifier ∷ Name → [QExp v] → QExp v
getQualifier "->"    [_,qe,_] = qe
getQualifier "U"     qes      = mconcat (qlitexp U : qes)
getQualifier "R"     qes      = mconcat (qlitexp R : qes)
getQualifier "A"     qes      = mconcat (qlitexp A : qes)
getQualifier "L"     qes      = mconcat (qlitexp L : qes)
getQualifier "Ref"   [_]      = qlitexp U
getQualifier "Ref"   [qe,_]   = qe
getQualifier "File"  [qe]     = qe
getQualifier "Const" _        = qlitexp U
getQualifier _       [qe]     = qe
getQualifier _       qes      = mconcat (qlitexp U : qes)

class Qualifier q r | q → r where
  toQualifierType ∷ q → Type r

instance Qualifier (Type r) r where
  toQualifierType = id

instance Qualifier (QExp r) r where
  toQualifierType = toQualifierType . unQExp

instance Qualifier QLit r where
  toQualifierType = unQExp . qlitexp

instance Qualifier Occurrence r where
  toQualifierType = toQualifierType . occToQLit

instance Ord r ⇒ Qualifier (QLit, Set.Set r) r where
  toQualifierType (q, rset) =
    toQualifierType (QExp q (FreeVar <$> Set.toList rset))

---
--- Type constructor variance
---

{-
Type constructor variance forms a seven point lattice, which keeps track
of both polarity and parameters that should be treated as qualifiers.
In particular, given a unary type constructor T with variance +, T S <:
T U when S <: U; but if T has variance Q+, then T S <: T U when
|S| ≤ |U|, where |⋅| gives the qualifier of a type.

       =
      /|\
     / | \
    /  |  \
   +  Q=   -
   | /  \  |
   |/    \ |
  Q+      Q-
    \     /
     \   /
      \ /
       0
-}

data Variance
  -- | 0
  = Omnivariant
  -- | Q+
  | QCovariant
  -- | Q-
  | QContravariant
  -- | Q=
  | QInvariant
  -- | +
  | Covariant
  -- | -
  | Contravariant
  -- | =
  | Invariant
  deriving (Eq, Show)

isQVariance ∷ Variance → Bool
isQVariance QInvariant     = True
isQVariance QCovariant     = True
isQVariance QContravariant = True
isQVariance _              = False

-- | Variances are a four point lattice with Invariant on top and
--   Omnivariant on the bottom
instance Bounded Variance where
  minBound = Omnivariant
  maxBound = Invariant

instance Lattice Variance where
  Omnivariant    ⊔ v2             = v2
  v1             ⊔ Omnivariant    = v1
  QCovariant     ⊔ Covariant      = Covariant
  Covariant      ⊔ QCovariant     = Covariant
  QContravariant ⊔ Contravariant  = Contravariant
  Contravariant  ⊔ QContravariant = Contravariant
  v1             ⊔ v2
    | v1 == v2                    = v1
    | isQVariance v1 && isQVariance v2
                                  = QInvariant
    | otherwise                   = Invariant
  --
  Invariant      ⊓ v2             = v2
  v1             ⊓ Invariant      = v1
  QCovariant     ⊓ Covariant      = QCovariant
  Covariant      ⊓ QCovariant     = QCovariant
  QInvariant     ⊓ Covariant      = QCovariant
  Covariant      ⊓ QInvariant     = QCovariant
  QContravariant ⊓ Contravariant  = QContravariant
  Contravariant  ⊓ QContravariant = QContravariant
  QInvariant     ⊓ Contravariant  = QContravariant
  Contravariant  ⊓ QInvariant     = QContravariant
  QInvariant     ⊓ QCovariant     = QCovariant
  QCovariant     ⊓ QInvariant     = QCovariant
  QInvariant     ⊓ QContravariant = QContravariant
  QContravariant ⊓ QInvariant     = QContravariant
  v1             ⊓ v2
    | v1 == v2                    = v1
    | otherwise                   = Omnivariant
  --
  Omnivariant    ⊑ _              = True
  QCovariant     ⊑ Covariant      = True
  QContravariant ⊑ Contravariant  = True
  QCovariant     ⊑ QInvariant     = True
  QContravariant ⊑ QInvariant     = True
  _              ⊑ Invariant      = True
  v1             ⊑ v2             = v1 == v2

-- | Variances work like abstract sign arithmetic, where:
--    Omnivariant    = { 0 }
--    Covariant      = ℤ₊  = { 0, 1, 2, ... }
--    Contravariant  = ℤ₋  = { ..., -2, -1, 0 }
--    Invariant      = ℤ
--    QCovariant     = 2ℤ₊ = { 0, 2, 4, ... }
--    QContravariant = 2ℤ₋ = { ..., -4, -2, 0 }
--    QInvariant     = 2ℤ  = { ..., -4, -2, 0, 2, 4, ... }
--- In this view, addition gives the join for the variance lattice,
--  and multiplication gives the variance of composing type constructors
--  of the given variances (more or less).
instance Num Variance where
  (+) = (⊔)
  --
  Omnivariant    * _              = Omnivariant
  Covariant      * v2             = v2
  v1             * Covariant      = v1
  Contravariant  * v2             = negate v2
  v1             * Contravariant  = negate v1
  QCovariant     * v2             = v2 ⊓ QInvariant
  v1             * QCovariant     = v1 ⊓ QInvariant
  QContravariant * v2             = negate v2 ⊓ QInvariant
  v1             * QContravariant = negate v1 ⊓ QInvariant
  QInvariant     * _              = QInvariant
  _              * QInvariant     = QInvariant
  _              * _              = Invariant
  --
  abs Omnivariant               = Omnivariant
  abs v | isQVariance v         = QCovariant
        | otherwise             = Covariant
  --
  signum QCovariant             = Covariant
  signum QContravariant         = Contravariant
  signum QInvariant             = Invariant
  signum v                      = v
  --
  negate Covariant              = Contravariant
  negate Contravariant          = Covariant
  negate QCovariant             = QContravariant
  negate QContravariant         = QCovariant
  negate v                      = v
  --
  fromInteger i
    | i > 0     = if even i then QCovariant else Covariant
    | i < 0     = if even i then QContravariant else Contravariant
    | otherwise = Omnivariant

-- | For now, we hard-code the variances of several type constructors
--   and consider the rest to be covariant by default.
getVariances ∷ Name → Int → [Variance]
getVariances "->"    3 = [Contravariant, QCovariant, Covariant]
getVariances "Ref"   1 = [Invariant]
getVariances "Ref"   2 = [QInvariant, Invariant]
getVariances "File"  1 = [QContravariant]
getVariances "Const" i = replicate i Omnivariant
getVariances "Anti"  i = replicate i Contravariant
getVariances _       i = replicate i Covariant

---
--- Empty – an uninhabited type
---

data Empty

elimEmpty  ∷ Empty → a
elimEmpty  = const undefined

elimEmptyF ∷ Functor f ⇒ f Empty → f a
elimEmptyF = Unsafe.Coerce.unsafeCoerce

instance Eq Empty where
  _ == _ = True

instance Ord Empty where
  _ `compare` _ = EQ

instance Show Empty where
  show = elimEmpty

---
--- Representation of variables
---

type Name = String

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
  = BoundVar !Int !Int (Perhaps Name)
  | FreeVar a
  deriving (Eq, Ord, Functor, Show)

boundVar ∷ Int → Int → Name → Var a
boundVar ix jx n = BoundVar ix jx (Here n)

bumpVar ∷ Int → Var a → Var a
bumpVar k (BoundVar i j n) = BoundVar (i + k) j n
bumpVar _ v                = v

---
--- Representation of types and type annotations
---

-- | The syntax of types allows nested quantifiers, though right now
--   we actually handle only prenex type.  Currently we do no kind
--   checking and don't track arity of type constructors.
--
--   The type parameter gives the representation of free type variables.
data Type a
  -- | The list of names are the suggested printing names for the bound
  --   type variables
  = QuaTy Quant [(Perhaps Name, QLit)] (Type a)
  | VarTy (Var a)
  | ConTy Name [Type a]
  | RowTy Name (Type a) (Type a)
  deriving (Eq, Functor)

-- | Quantifiers
data Quant
  = AllQu
  | ExQu
  deriving (Eq, Ord, Show)

allTy, exTy ∷ [QLit] → Type a → Type a
allTy j = QuaTy AllQu (zip (map Here tvNames) j)
exTy  j = QuaTy ExQu  (zip (map Here tvNames) j)

bvTy ∷ Optional f => Int → Int → f Name → Type a
bvTy i j n = VarTy (BoundVar i j (coerceOptional n))

fvTy ∷ a → Type a
fvTy  = VarTy . FreeVar

arrTy ∷ Type a → QExp a → Type a → Type a
arrTy t1 qe t2 = ConTy "->" [t1, unQExp qe, t2]

pairTy ∷ Type a → Type a → Type a
pairTy t1 t2 = ConTy "Pair" [t1, t2]

endTy  ∷ Type a
endTy  = ConTy "end" []

t1 ↦ t2 = arrTy t1 (qlitexp U) t2
infixr 6 ↦

-- | A type annotation. The list of 'Name's records the free
--   type variables in the 'Type'.
data Annot = Annot [Name] (Type Name)
  deriving Eq

-- | The empty annotation
annot0 :: Annot
annot0  = Annot ["_"] (fvTy "_")

-- | The type of a dereferencing function for free type variable
--   representation @v@, in some monad @m@.
type Deref m v = v → m (Either v (Type v))

-- | Fold a type, while dereferencing type variables
foldType ∷ (Monad m, ?deref ∷ Deref m v) ⇒
           -- | For quantifiers
           (Quant → [(Perhaps Name, QLit)] → r → r) →
           -- | For bound variables
           (Maybe QLit → Int → Int → Perhaps Name → r) →
           -- | For free variables
           (v → r) →
           -- | For constructor applications
           (Name → [r] → r) →
           -- | For row type labels
           (Name → r → r → r) →
           -- | Type to fold
           Type v →
           m r
foldType fquant fbvar ffvar fcon frow t0 =
  let ?deref = lift . ?deref in CMR.runReaderT (loop t0) []
  where
  loop (QuaTy q αs t)           =
    fquant q αs `liftM` CMR.local (map snd αs:) (loop t)
  loop (VarTy (BoundVar i j n)) = do
    env ← CMR.ask
    return (fbvar (look i j env) i j n)
  loop (VarTy (FreeVar v))      = do
    mt ← ?deref v
    case mt of
      Left v' → return (ffvar v')
      Right t → loop t
  loop (ConTy n ts)             =
    fcon n `liftM` sequence
      [ if isQVariance v
          then loop . unQExp =<< qualifier t
          else loop t
      | t ← ts
      | v ← getVariances n (length ts) ]
  loop (RowTy n t1 t2)          =
    frow n `liftM` loop t1 `ap` loop t2
  --
  look i j env
    | rib:_ ← drop i env
    , elt:_ ← drop j rib = Just elt
  look _ _ _             = Nothing

-- | Get the qualifier of a type
qualifier ∷ (Monad m, ?deref ∷ Deref m v) ⇒
            Type v → m (QExp v)
qualifier = foldType fquant fbvar ffvar fcon frow
  where
  fquant _ _ (QExp q vs) = QExp q (bumpVar (-1) <$> vs)
  fbvar (Just ql) _ _ _  = qlitexp ql
  fbvar Nothing   i j n  = qvarexp (BoundVar i j n)
  ffvar                  = qvarexp . FreeVar
  fcon n qes             = getQualifier n qes
  frow _ qe1 qe2         = getQualifier "*" [qe1, qe2]

-- | Get something in the *form* of a qualifier without dereferencing
pureQualifier ∷ Type v → QExp v
pureQualifier t = runIdentity (qualifier t) where ?deref = return . Left

-- | Monadic version of type folding
foldTypeM ∷ (Monad m, ?deref ∷ Deref m v) ⇒
            (Quant → [(Perhaps Name, QLit)] → r → m r) →
            (Maybe QLit → Int → Int → Perhaps Name → m r) →
            (v → m r) →
            (Name → [r] → m r) →
            (Name → r → r → m r) →
            Type v →
            m r
foldTypeM fquant fbvar ffvar fcon frow t =
  join (foldType fquantM fbvar ffvar fconM frowM t) where
    fquantM q αs mr  = fquant q αs =<< mr
    fconM c mrs      = fcon c =<< sequence mrs
    frowM c t1 t2    = join (frow c `liftM` t1 `ap` t2)

-- The type monad does substitution
instance Monad Type where
  QuaTy u e t            >>= f = QuaTy u e (t >>= f)
  VarTy (FreeVar r)      >>= f = f r
  VarTy (BoundVar i j n) >>= _ = VarTy (BoundVar i j n)
  ConTy n ts             >>= f = ConTy n (map (>>= f) ts)
  RowTy n t1 t2          >>= f = RowTy n (t1 >>= f) (t2 >>= f)
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
                       (const (return <$$$> bvTy))
                       f
                       (return <$$> ConTy)
                       (return <$$$> RowTy)
             where ?deref = return . Left

-- | Is the given type ground (type-variable and quantifier free)?
isGroundType ∷ (Monad m, ?deref ∷ Deref m v) ⇒ Type v → m Bool
isGroundType = foldType (\_ _ _ → False) (\_ _ _ _ → False)
                        (\_ → False) (\_ → and) (\_ → (&&))

-- | Is the given type closed? (ASSUMPTION: The type is locally closed)
isClosedType ∷ (Monad m, ?deref ∷ Deref m v) ⇒ Type v → m Bool
isClosedType = foldType (\_ _ → id) (\_ _ _ _ → True) (\_ → False)
                        (\_ → and) (\_ → (&&))

-- | Is the given type quantifier free?
isMonoType ∷ (Monad m, ?deref ∷ Deref m v) ⇒ Type v → m Bool
isMonoType = foldType (\_ _ _ → False) (\_ _ _ _ → True) (\_ → True)
                      (\_ → and) (\_ → (&&))

-- | Is the given type (universal) prenex?
--   (Precondition: the argument is standard)
isPrenexType ∷ (Monad m, ?deref ∷ Deref m v) ⇒ Type v → m Bool
isPrenexType (QuaTy AllQu _ τ)   = isMonoType τ
isPrenexType (VarTy (FreeVar r)) =
  either (\_ → return True) isPrenexType =<< ?deref r
isPrenexType τ                   = isMonoType τ

---
--- Patterns
---

data Patt a
  = VarPa (Perhaps Name)
  | WldPa
  | ConPa Name [Patt a]
  | InjPa Name (Patt a)
  | AnnPa (Patt a) Annot
  deriving Functor

-- | The number of variables bound by a pattern
pattSize ∷ Patt a → Int
pattSize (VarPa _)    = 1
pattSize WldPa        = 0
pattSize (ConPa _ πs) = sum (map pattSize πs)
pattSize (InjPa _ π)  = pattSize π
pattSize (AnnPa π _)  = pattSize π

totalPatt ∷ Patt a → Bool
totalPatt (VarPa _)   = True
totalPatt WldPa       = True
totalPatt (ConPa _ _) = False
totalPatt (InjPa _ _) = False
totalPatt (AnnPa π _) = totalPatt π

pattHasWild ∷ Patt a → Bool
pattHasWild (VarPa _)    = False
pattHasWild WldPa        = True
pattHasWild (ConPa _ πs) = any pattHasWild πs
pattHasWild (InjPa _ π)  = pattHasWild π
pattHasWild (AnnPa π _)  = pattHasWild π

---
--- Terms
---

data Term a
  = AbsTm (Patt a) (Term a)
  | LetTm (Patt a) (Term a) (Term a)
  | MatTm (Term a) [(Patt a, Term a)]
  | RecTm [(Perhaps Name, Term a)] (Term a)
  | VarTm (Var a)
  | ConTm Name [Term a]
  | LabTm Bool Name
  | AppTm (Term a) (Term a)
  | AnnTm (Term a) Annot
  deriving Functor

bvTm ∷ Optional f => Int → Int → f Name → Term a
bvTm i j n = VarTm (BoundVar i j (coerceOptional n))

fvTm ∷ a → Term a
fvTm  = VarTm . FreeVar

syntacticValue ∷ Term a → Bool
syntacticValue (AbsTm _ _)       = True
syntacticValue (MatTm _ _)       = False
syntacticValue (LetTm _ e1 e2)   = syntacticValue e1 && syntacticValue e2
-- Assumes all bindings are values, which is required by statics:
syntacticValue (RecTm _ e2)      = syntacticValue e2
syntacticValue (VarTm _)         = True
syntacticValue (ConTm _ es)      = all syntacticValue es
syntacticValue (LabTm _ _)       = True
syntacticValue (AppTm (LabTm _ _) e)
                                 = syntacticValue e
syntacticValue (AppTm _ _)       = False
syntacticValue (AnnTm e _)       = syntacticValue e

isAnnotated :: Term a → Bool
isAnnotated (AbsTm _ _)      = False
isAnnotated (MatTm _ bs)     = all (isAnnotated . snd) bs
isAnnotated (LetTm _ _ e2)   = isAnnotated e2
isAnnotated (RecTm _ e2)     = isAnnotated e2
isAnnotated (VarTm _)        = False
isAnnotated (ConTm _ _)      = False
isAnnotated (LabTm _ _)      = False
isAnnotated (AppTm _ _)      = False
isAnnotated (AnnTm _ _)      = True

---
--- Initial environment
---

γ0' ∷ [(Name, String)]
γ0' = [ ("id",          "∀ α. α → α")
      , ("choose",      "∀ α : A. α → α -α> α")
      , ("apply",       "∀ α β γ. (α -γ> β) → α -γ> β")
      , ("revapp",      "∀ α β γ. α → (α -γ> β) -α γ> β")
      -- Lists
      , ("single",      "∀ α. α → List α")
      , ("nil",         "∀ α. List α")
      , ("cons",        "∀ α. α → List α -α> List α")
      , ("map",         "∀ α β. (α → β) → List α → List β")
      , ("foldr",       "∀ α β. (α → β -L> β) → β → List α -β> β")
      , ("head",        "∀ α : A. List α → α")
      , ("tail",        "∀ α : A. List α → List α")
      , ("app",         "∀ α. List α → List α → List α")
      -- Ref cells
      , ("ref",         "∀ α: A, β. α → Ref β α")
      , ("ref'",        "∀ α β. α → Ref (R β) α")
      , ("uref",        "∀ α:A. α → Ref U α")
      , ("rref",        "∀ α. α → Ref R α")
      , ("aref",        "∀ α:A. α → Ref A α")
      , ("lref",        "∀ α. α → Ref L α")
      , ("swapRef",     "∀ α β. Pair (Ref β α) α → Pair (Ref β α) α")
      , ("swapRef'",    "∀ α β γ. Pair (Ref (A β γ) α) β → \
                        \         Pair (Ref (A β γ) β) α")
      , ("readRef",     "∀ α:R, β. Ref β α → α")
      , ("readRef'"  ,  "∀ α:R, β. Ref β α → Pair (Ref β α) α")
      , ("freeRef'",    "∀ α β. Ref (A β) α → α")
      , ("writeRef",    "∀ α β:A. Pair (Ref β α) α → T")
      , ("writeRef'",   "∀ α:A, β γ. Pair (Ref (A β γ) α) β → Ref (A β γ) β")
      -- Products
      , ("pair",        "∀ α β. α → β -α> Pair α β")
      , ("fst",         "∀ α : L, β : A. Pair α β → α")
      , ("snd",         "∀ α : A, β : L. Pair α β → β")
      -- Sums
      , ("inl",         "∀ α β. α → Either α β")
      , ("inr",         "∀ α β. β → Either α β")
      , ("either",      "∀ α β γ. (α -A> γ) → (β -A> γ) -A> Either α β -A> γ")
      -- Uniqueness types?
      , ("openFile",    "String → File A")
      , ("readFile",    "∀ α. File α → File α")
      , ("writeFile",   "File A → File A")
      , ("closeFile",   "File A → T")
      -- Any
      , ("eat",         "∀ α β. α → β → β")
      , ("eatU",        "∀ α:U, β. α → β → β")
      , ("eatA",        "∀ α:A, β. α → β → β")
      , ("eatR",        "∀ α:R, β. α → β → β")
      , ("bot",         "∀ α. α")
      , ("botU",        "∀ α:U. α")
      , ("botR",        "∀ α:R. α")
      , ("botA",        "∀ α:A. α")
      , ("botL",        "∀ α:L. α")
      , ("cast",        "∀ α β. α → β")
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
openTyN n k vs t0 = case t0 of
  QuaTy u e t      → QuaTy u e (next t)
  VarTy v          → openTV_N n k vs v
  ConTy name ts    → ConTy name (map this ts)
  RowTy name t1 t2 → RowTy name (this t1) (this t2)
  where
    this = openTyN n k vs
    next = openTyN n (k + 1) vs

openTV_N ∷ Int → Int → [Type a] → Var a → Type a
openTV_N n k vs (BoundVar i j name)
  | i > k      = VarTy (BoundVar (i - n) j name)
  | i == k, Just t ← listNth j vs
              = t
  | otherwise = VarTy (BoundVar i j name)
openTV_N _ _ _  (FreeVar v) = VarTy (FreeVar v)

-- | @closeTy k αs τ@ finds the free variables @αs@ and replaces them
--   with bound variables at rib level @k@.  The position of each type
--   variable in @αs@ gives the index of each bound variable into the
--   new rib.
closeTy ∷ Eq a ⇒ Int → [a] → Type a → Type a
closeTy k vs t0 = case t0 of
  QuaTy u e t   → QuaTy u e (next t)
  VarTy (BoundVar i j n)
    | i >= k    → VarTy (BoundVar (i + 1) j n)
    | otherwise → VarTy (BoundVar i j n)
  VarTy (FreeVar v)
    | Just j ← List.findIndex (== v) vs
                → VarTy (BoundVar k j Nope)
    | otherwise → VarTy (FreeVar v)
  ConTy n ts    → ConTy n (map this ts)
  RowTy n t1 t2 → RowTy n (this t1) (this t2)
  where
    this = closeTy k vs
    next = closeTy (k + 1) vs

-- | Add the given quantifier while binding the given list of variables
closeWith ∷ Ord a ⇒ Quant → [a] → Type a → Type a
closeWith = closeWithNames []

-- | Add the given quantifier while binding the given list of variables
closeWithQuals ∷ Ord a ⇒ [QLit] → Quant → [a] → Type a → Type a
closeWithQuals qls = closeWithNames (map (Nope,) qls)

-- | Add the given quantifier while binding the given list of variables
closeWithNames ∷ Ord a ⇒
                 [(Perhaps Name, QLit)] → Quant → [a] → Type a → Type a
closeWithNames _   _ []  ρ = ρ
closeWithNames pns q tvs ρ = standardize (QuaTy q pns' (closeTy 0 tvs ρ))
  where pns' = take (length tvs) (pns ++ repeat (Nope, L))

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
  loop k (RowTy _ t1 t2)          = loop k t1 && loop k t2

-- | Are there no bound vars of level k?
lcTyK ∷ Int → Type a → Bool
lcTyK  = loop where
  loop k (QuaTy _ _ t)            = loop (k + 1) t
  loop k (VarTy (BoundVar i _ _)) = k /= i
  loop _ (VarTy (FreeVar _))      = True
  loop k (ConTy _ ts)             = all (loop k) ts
  loop k (RowTy _ t1 t2)          = loop k t1 && loop k t2

-- | Rename the variables at rib level k, where we adjust the rib levels
--   in the new names as we traverse under binders.
renameTm ∷ Int → [Var a] → Term a → Term a
renameTm k vs e0 = case e0 of
  AbsTm π e     → AbsTm π (next e)
  LetTm π e1 e2 → LetTm π (loop e1) (next e2)
  MatTm e1 bs   → MatTm (loop e1) [ (π, next e) | (π,e) ← bs ]
  RecTm bs e2   → RecTm [ (pn, next e) | (pn,e) ← bs ] (next e2)
  VarTm var     → VarTm $ case var of
    BoundVar i j name
      | i > k         → BoundVar i j name
      | i == k, Just v ← listNth j vs
                      → bumpVar k v
    _                 → var
  ConTm n vs    → ConTm n (map loop vs)
  LabTm b n     → LabTm b n
  AppTm e1 e2   → AppTm (loop e1) (loop e2)
  AnnTm e annot → AnnTm (loop e) annot
  where next = renameTm (k + 1) vs
        loop = renameTm k vs

-- | Like 'openTyN', but for terms.
openTm ∷ Int → [Term a] → Term a → Term a
openTm k es e0 = case e0 of
  AbsTm π e     → AbsTm π (next e)
  LetTm π e1 e2 → LetTm π (loop e1) (next e2)
  MatTm e1 bs   → MatTm (loop e1) [ (π, next e) | (π,e) ← bs ]
  RecTm bs e2   → RecTm [ (pn, next e) | (pn,e) ← bs ] (next e2)
  VarTm var     → case var of
    BoundVar i j name
      | i > k         → VarTm (BoundVar i j name)
      | i == k, Just e ← listNth j es
                      → e
    _                 → VarTm var
  ConTm n es    → ConTm n (map loop es)
  LabTm b n     → LabTm b n
  AppTm e1 e2   → AppTm (loop e1) (loop e2)
  AnnTm e annot → AnnTm (loop e) annot
  where next = openTm (k + 1) es
        loop = openTm k es

-- | Find the "locally-free" variables in a term -- that is, the bound
--   variables that point beyond the term.
lfvTm ∷ Term a → [(Int, Int)]
lfvTm = Set.toList . lfvTmK 0 where
  lfvTmK k e0 = case e0 of
    AbsTm _ e     → next e
    LetTm _ e1 e2 → loop e1 `Set.union` next e2
    MatTm e1 bs   → loop e1 `Set.union` Set.unions (map (next . snd) bs)
    RecTm bs e2   → Set.unions (map (next . snd) bs) `Set.union` next e2
    VarTm var     → case var of
      BoundVar i j _
        | i >= k  → Set.singleton (i - k, j)
      _           → Set.empty
    ConTm _ es    → Set.unions (map loop es)
    LabTm _ _     → Set.empty
    AppTm e1 e2   → loop e1 `Set.union` loop e2
    AnnTm e _     → loop e
    where next = lfvTmK (k + 1)
          loop = lfvTmK k

---
--- Occurrence analysis
---

{- | The number of occurrences of a variable in a term.  These
     are an abstraction of the natural numbers as zero, one, many, or
     combinations thereof.
     (Note: no { 0, 2+ })

      U
     / \
    /   \
   A     R
   |\   /|
   | \ / |
   Z  L  /
    \ | /
     \|/
      E

-}
data Occurrence
  -- | Any number of times { 0, 1, 2+ }
  = UO
  -- | One or more times { 1, 2+ }
  | RO
  -- | Zero or one times { 0, 1 }
  | AO
  -- | Exactly one time { 1 }
  | LO
  -- | Zero times { 0 }
  | ZO
  -- | Dead code / error { }
  | EO
  deriving (Eq, Show)

-- | Convert an occurrence to a representative list of numbers
occToInts ∷ Occurrence → [Int]
occToInts UO = [0, 1, 2]
occToInts RO = [1, 2]
occToInts AO = [0, 1]
occToInts LO = [1]
occToInts ZO = [0]
occToInts EO = []

-- | Convert an occurrence to the best qualifier literal
occToQLit ∷ Occurrence → QLit
occToQLit UO = U
occToQLit RO = R
occToQLit AO = A
occToQLit LO = L
occToQLit ZO = A
occToQLit EO = L

instance Bounded Occurrence where
  minBound = EO
  maxBound = UO

instance Lattice Occurrence where
  EO ⊔ o  = o;  o  ⊔ EO = o
  ZO ⊔ LO = AO; LO ⊔ ZO = AO
  ZO ⊔ AO = AO; AO ⊔ ZO = AO
  LO ⊔ RO = RO; RO ⊔ LO = RO
  LO ⊔ AO = AO; AO ⊔ LO = AO
  o  ⊔ o' | o == o'   = o
          | otherwise = UO
  --
  UO ⊓ o  = o;  o  ⊓ UO = o
  RO ⊓ AO = LO; AO ⊓ RO = LO
  RO ⊓ LO = LO; LO ⊓ RO = LO
  AO ⊓ LO = LO; LO ⊓ AO = LO
  AO ⊓ ZO = ZO; ZO ⊓ AO = ZO
  o  ⊓ o' | o == o'   = o
          | otherwise = EO

-- Abstract arithmetic
instance Num Occurrence where
  fromInteger 0             = ZO
  fromInteger 1             = LO
  fromInteger z | z > 1     = RO
                | otherwise = EO
  abs = id
  negate = const EO
  signum o = bigJoin (map (fromInteger . toInteger . signum) (occToInts o))
  EO + _  = EO; _  + EO = EO
  ZO + o  = o;  o  + ZO = o
  LO + LO = RO;
  LO + AO = RO; AO + LO = RO
  LO + RO = RO; RO + LO = RO
  LO + UO = RO; UO + LO = RO
  AO + RO = RO; RO + AO = RO
  RO + RO = RO;
  RO + UO = RO; UO + RO = RO
  _  + _  = UO
  --
  o  * o' = bigJoin $ do
    z  ← occToInts o
    z' ← occToInts o'
    return (fromInteger (toInteger (z * z')))

{-
countOccs ∷ Eq a ⇒ a → Term a → Occurrence
countOccs x = loop where
  loop (AbsTm _ e)     = loop e
  loop (LetTm _ e1 e2) = loop e1 + loop e2
  loop (MatTm e1 bs)   = loop e1 + bigJoin (map (loop . snd) bs)
  loop (RecTm bs e2)   = loop e2 + sum (map (loop . snd) bs)
  loop (VarTm (FreeVar x'))
    | x == x'          = 1
  loop (VarTm _)       = 0
  loop (ConTm _ es)    = sum (map loop es)
  loop (AppTm e1 e2)   = loop e1 + loop e2
  loop (AnnTm e _)     = loop e
-}

-- | Count the occurrences of the variables of rib 0
countOccs ∷ Term Empty → [Occurrence]
countOccs = Stream.toList . loop . openTm 0 (map fvTm [0..]) . elimEmptyF
  where
  loop (AbsTm _ e)         = loop e
  loop (LetTm _ e1 e2)     = loop e1 + loop e2
  loop (MatTm e1 bs)       = loop e1 + bigJoin (map (loop . snd) bs)
  loop (RecTm bs e2)       = loop e2 + sum (map (loop . snd) bs)
  loop (VarTm (FreeVar j)) = δ j
  loop (VarTm _)           = 0
  loop (ConTm _ es)        = sum (map loop es)
  loop (LabTm _ _)         = 0
  loop (AppTm e1 e2)       = loop e1 + loop e2
  loop (AnnTm e _)         = loop e
  --
  δ j = fmap (\j' → if j == j' then 1 else 0) (Stream.iterate succ 0)

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

-- | Map from variables to variances
type VarMap v = Map.Map v Variance

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
  ftvV     ∷ (Monad m, ?deref ∷ Deref m v) ⇒ a → m (VarMap v)
  -- | To get a map from free type variables to a list of all their
  --   occurrences' variances.
  ftvSet   ∷ (Monad m, ?deref ∷ Deref m v) ⇒ a → m (Set.Set v)
  -- | To get a map from free type variables to a list of all their
  --   occurrences' variances.
  ftvVs    ∷ (Monad m, ?deref ∷ Deref m v) ⇒ a → m (Map.Map v [Variance])
  -- | To get a list of the free type variables in a type (with no repeats).
  ftvM     ∷ (Monad m, ?deref ∷ Deref m v) ⇒ a → m [v]
  -- | To get the set of (apparent) free variables without trying to
  --   dereference anything
  ftvPure  ∷ a → VarMap v
  -- 
  --
  ftvFold each zero a
                 = foldFtvTree each zero `liftM` ftvTree a
  ftvList        = ftvFold (curry (:)) []
  ftvV           = ftvFold (Map.insertWith (+)) Map.empty
  ftvSet         = ftvFold (const . Set.insert) Set.empty
  ftvVs          = ftvFold (\v a → Map.insertWith (++) v [a]) Map.empty
  ftvM a         = liftM (ordNub . map fst) (ftvList a)
  ftvPure a      = runIdentity (ftvV a) where ?deref = return . Left

instance Ord v ⇒ Ftv (Type v) v where
  ftvTree = foldType
             (\_ _ tree → tree)
             (\_ _ _ → mempty)
             FTSingle
             (\c trees → FTBranch
                 [ FTVariance (* var) tree
                 | tree ← trees
                 | var  ← getVariances c (length trees) ])
             (\_ t1 t2 → FTBranch [t1, t2])

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

-- | A class for type variables (which are free in themselves).
class    (Ftv v v, Show v, Ppr v) ⇒ Tv v where
  tvUniqueID ∷ v → Int

---
--- Unfolds for syntax
---

-- To strip off as many of the specified quantifier as possible,
-- building a qualifier bound environment for the layers.
unfoldQua ∷ Quant → Type a → ([[QLit]], Type a)
unfoldQua u0 = first reverse . loop where
  loop (QuaTy u tvs t)
    | u0 == u || lcTyK 0 t = first (map snd tvs:) (loop t)
  loop t                   = ([], t)

-- To find the labels and fields of a row type, and the extension,
-- in standard order
unfoldRow ∷ Type a → ([(Name, Type a)], Type a)
unfoldRow = first (List.sortBy (compare <$> fst <$.> fst)) . loop where
  loop (RowTy n t1 t2) = first ((n, t1):) (loop t2)
  loop t               = ([], t)

-- To find the operator and operands of a curried application.
unfoldApp ∷ Term a → (Term a, [Term a])
unfoldApp (AppTm e1 e2) = second (++[e2]) (unfoldApp e1)
unfoldApp e             = (e, [])

-- To find the parameters and body of a curried function.
unfoldAbs ∷ Term a → ([Patt a], Term a)
unfoldAbs (AbsTm π e) = first (π:) (unfoldAbs e)
unfoldAbs e           = ([], e)

---
--- Row operations
---

foldRow ∷ [(Name, Type a)] → Type a → Type a
foldRow = flip (foldr (uncurry RowTy))

sortRow ∷ Type a → Type a
sortRow = uncurry foldRow . unfoldRow

extractLabel ∷ Name → Type v → Maybe (Type v, Type v)
extractLabel n (RowTy n' t1 t2)
  | n == n'      = Just (t1, t2)
  | otherwise    = second (RowTy n' t1) <$> extractLabel n t2
extractLabel _ _ = Nothing

matchLabels
  ∷ Type v → Type v →
    ([((Name, Type v), (Name, Type v))],
     ([(Name, Type v)], Type v), ([(Name, Type v)], Type v))
matchLabels t10 t20 = (pairs, (extra1, ext1), (extra2, ext2))
  where
    (pairs, extra1, extra2) = CMW.execWriter (loop row1 row2)
    (row1, ext1) = unfoldRow t10
    (row2, ext2) = unfoldRow t20
    loop []    rest2 = tell ([], [], rest2)
    loop rest1 []    = tell ([], rest1, [])
    loop (p1@(n1,_):rest1) (p2@(n2,_):rest2)
      | n1 < n2      = tell ([], [p1], [])      >> loop rest1 (p2:rest2)
      | n1 > n2      = tell ([], [], [p2])      >> loop (p1:rest1) rest2
      | otherwise    = tell ([(p1,p2)], [], []) >> loop rest1 rest2
    tell = CMW.tell

---
--- Parsing
---

-- | @standardize@ puts a type in standard form.
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
class Ord v ⇒ Standardizable a v | a → v where
  standardize      ∷ a → a
  standardize      = standardizeQuals Map.empty
  standardizeQuals ∷ Map.Map v QLit → a → a

instance Standardizable a v ⇒ Standardizable [a] v where
  standardizeQuals = map . standardizeQuals

instance Ord v ⇒ Standardizable (Type v) v where
  standardizeQuals qm t00 = runST (loop 0 [] t00) where
    loop depth g t0 = case t0 of
      QuaTy u _ _ → do
        rn ← ST.newSTRef []
        let (qls, t) = unfoldQua u t0
            i        = length qls
            g'       = (depth + i, rn,) <$$> qls
        t' ← loop (depth + i) (g' ++ g) t
        nl ← ST.readSTRef rn
        return $ case nl of
          [] → openTyN i (-1) [] t'
          _  → QuaTy u [ n | (_,n) ← nl ] (openTyN (i - 1) (i - 1) [] t')
      ConTy con ts          → ConTy con <$> sequence
        [ if isQVariance v
            then doQual depth g t
            else loop depth g t
        | t ← ts
        | v ← getVariances con (length ts) ]
      VarTy v               → VarTy . fst <$> doVar depth g (const True) v
      RowTy _ _ _           → do
        let (row, ext) = unfoldRow t0
        row' ← sequence
          [ (ni,) <$> loop depth g ti
          | (ni, ti) ← row ]
        ext' ← loop depth g ext
        return (foldRow row' ext')
    --
    doVar depth g keep v0 = case v0 of
      BoundVar i j n
        | rib:_               ← drop i g
        , (olddepth, r, ql):_ ← drop j rib
                            → do
            s  ← ST.readSTRef r
            j' ← case List.findIndex ((== (depth - i,j)) . fst) s of
              Just j' → return j'
              Nothing → do
                when (keep ql) $
                  ST.writeSTRef r (s ++ [((depth - i,j),(n,ql))])
                return (length s)
            return (BoundVar (depth - olddepth) j' n, keep ql)
        | otherwise   → return (v0, True)
      FreeVar r       → return (FreeVar r, keep (Map.findWithDefault L r qm))
    --
    doQual depth g t = do
      let QExp q vs = pureQualifier t
      vqs' ← mapM (doVar depth g (not . (⊑ q))) (ordNub vs)
      let vs' = List.sort (map fst (filter snd vqs'))
      return (toQualifierType (QExp q vs'))

-- | To put a type annotation in standard form.
instance Standardizable Annot Name where
  standardizeQuals qm (Annot ns t) = Annot ns (standardizeQuals qm t)

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
  reservedNames   = ["all", "ex", "let", "in", "rec", "and", "match", "with"],
  reservedOpNames = ["->", "→", "⊸", "∀", "∃", ".", "*", "×",
                     "\\", "λ", "=", ":", "|"],
  caseSensitive   = True
}
  -- 'λ' is not an identifier character, so that we can use it as
  -- a reserved operator. Otherwise, we'd need a space after it.
  where noλ p = notFollowedBy (char 'λ') *> p

parseArrow ∷ P ()
parseArrow = reservedOp tok "→" <|> reservedOp tok "->"

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

-- | To parse an annotation
instance Parsable Annot where
  genParser  = withState [] $ do
    τ0    ← parseType
    somes ← getState
    let τ = openTy 0 (map fvTy somes) τ0
    return (standardize (Annot somes τ))

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
               body   ← level0 (reverse (fst <$$> tvss) ++ g)
               return (foldr2 QuaTy body quants (first Here <$$> tvss))
         <|> level1 g
  level1 g = do
               t1 ← level2 g
               option t1 $ do
                 mkArr ← parseTypeArrow (tyvarp g) (level0 g)
                 t2    ← level0 g
                 return (t1 `mkArr` t2)
  level2 g = chainl1
               (level3 g)
               (pairTy <$ (reservedOp tok "*" <|> reservedOp tok "×"))
  level3 g = ConTy <$> upperIdentifier <*> many (level4 g)
         <|> level4 g
  level4 g = VarTy <$> tyvarp g
         <|> do
               con ← upperIdentifier
               return (ConTy con [])
         <|> brackets tok (rowty g)
         <|> parens tok (level0 g)
  rowty g  =
    let entry = RowTy <$> upperIdentifier <* colon tok <*> level0 g
        loop  = option endTy $ do
          reservedOp tok "|"
          (VarTy <$> tyvarp g) <|> (entry <*> loop)
     in option endTy (entry <*> loop)
  tyvarp g = join (findVar <$> lowerIdentifier <*> pure g)

-- To parse a sequence of quantifiers along with their bound variables.
parseQuantifiers ∷ P [(Quant, [(Name, QLit)])]
parseQuantifiers = many1 ((,) <$> quant <*> tvs) <* dot tok where
  quant   = AllQu <$ (reserved tok "all" <|> reservedOp tok "∀")
        <|> ExQu  <$ (reserved tok "ex"  <|> reservedOp tok "∃")
  tvs     = do
    idss ← sepBy1 tvGroup (comma tok)
    let ids = concatMap (map fst) idss
    when (List.nub ids /= ids) $
      fail "repeated tyvar in quantifier group"
    return (concat idss)
  tvGroup = do
    ids ← many1 lowerIdentifier
    ql  ← option L (colon tok >> parseQLit)
    return (map (,ql) ids)

-- | To parse a qualifier literal
parseQLit ∷ P QLit
parseQLit = choice
              [ symbol tok "U" >> return U
              , symbol tok "R" >> return R
              , symbol tok "A" >> return A
              , symbol tok "L" >> return L ]

parseTypeArrow ∷ P (Var a) → P (Type a) → P (Type a → Type a → Type a)
parseTypeArrow tyvarp typep = flip arrTy <$> choice
  [ qlitexp U <$ reservedOp tok "→"
  , qlitexp U <$ reservedOp tok "->"
  , qlitexp L <$ reservedOp tok "⊸"
  , qlitexp L <$ try (symbol tok "-o")
  , between (try (symbol tok "-{")) (try (symbol tok "}>")) $
      pureQualifier <$> typep
  , between (symbol tok "-") (symbol tok ">") $ do
      QExp <$> option U parseQLit <*> many tyvarp
  ]

-- To parse a pattern. Produces the pattern (which is nameless) and
-- the list of names bound by the patern.
parsePatt ∷ Int → P (Patt a, [Name])
parsePatt p = withState [] $ (,) <$> level p <*> getState where
  level 0 = do
              π ← level 1
              option π $ do
                reservedOp tok ":"
                AnnPa π <$> genParser
  level 1 = ConPa <$> upperIdentifier <*> many (level 2)
        <|> InjPa <$  char '`' <*> upperIdentifier <*> level 1
        <|> level 2
  level _ = ConPa <$> upperIdentifier <*> pure []
        <|> WldPa <$  reserved tok "_"
        <|> VarPa <$> variable
        <|> parens tok tuple
  tuple    = chainl1 (level 0)
                     ((\e1 e2 → ConPa "Pair" [e1, e2]) <$ comma tok)
  variable = do
    name  ← lowerIdentifier
    names ← getState
    if name `elem` names
      then unexpected ("repeated variable in pattern: " ++ name)
      else putState (names++[name])
    return (Here name)

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
               reserved tok "match"
               e1 ← level0 γ
               reserved tok "with"
               optional (reservedOp tok "|")
               bs ← flip sepBy1 (reservedOp tok "|") $ do
                 (π, names) ← parsePatt 0
                 parseArrow
                 e ← level0 (names : γ)
                 return (π, e)
               return (MatTm e1 bs)
         <|> do
               reserved tok "let"
               choice
                [ do
                    reserved tok "rec"
                    parseLetRec level0 γ
                , do
                    (π, names) ← parsePatt 0
                    reservedOp tok "="
                    e1 ← level0 γ
                    reserved tok "in"
                    e2 ← level0 (names : γ)
                    return (LetTm π e1 e2)
                ]
         <|> do
               reservedOp tok "\\" <|> reservedOp tok "λ"
               (πs, names) ← unzip <$> many1 (parsePatt 3)
               dot tok
               e ← level0 (reverse names ++ γ)
               return (foldr AbsTm e πs)
         <|> level1 γ
  level1 γ = do
               e ← level2 γ
               option e $ do
                 reservedOp tok ":"
                 AnnTm e <$> genParser
  level2 γ = ConTm <$> upperIdentifier <*> many (level3 γ)
         <|> chainl1 (level3 γ) (return AppTm)
  level3 γ = do
               v ← lowerIdentifier
               VarTm <$> findVar v γ
         <|> do
               con ← upperIdentifier
               return (ConTm con [])
         <|> LabTm <$> rowInjMark <*> upperIdentifier
         <|> parens tok (tuple γ)
  tuple γ  = chainl1 (level0 γ)
                     ((\e1 e2 → ConTm "Pair" [e1, e2]) <$ comma tok)

rowInjMark ∷ P Bool
rowInjMark = (True  <$ char '`')
         <|> (False <$ char '#')

parseLetRec ∷ ([[Name]] → P (Term a)) → [[Name]] → P (Term a)
parseLetRec term γ = do
  freeVars ← getState
  putState []
  bs ← flip sepBy1 (reserved tok "and") $ do
    x ← lowerIdentifier
    reservedOp tok "="
    e ← term []
    return (x, e)
  reserved tok "in"
  e2       ← term []
  recVars  ← getState
  putState freeVars
  let names = map fst bs
  unless (ordNub names == names) $
    fail "Repeated bound variable name in let rec"
  let γ'     = names : γ
  vars' ← mapM (flip findVar γ') recVars
  let adjust = renameTm 0 vars'
  return (RecTm (map (Here *** adjust) bs) (adjust e2))

instance Read Annot where
  readsPrec _ = readsPrecFromParser

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
namesFrom s = [ c:n | n ← "" : "'" : map numberSubscript [0 ..], c ← s ]

-- | Given a natural number, represent it as a string of number
--   subscripts.
numberSubscript ∷ Int → String
numberSubscript 0  = "₀"
numberSubscript n0
  | n0 < 0         = error "numberSubscript requires non-negative Int"
  | otherwise      = reverse $ List.unfoldr each n0 where
  each 0 = Nothing
  each n = Just (subscriptDigits !! ones, rest)
             where (rest, ones) = n `divMod` 10

-- | Clear the primes and subscripts from the end of a name
clearScripts ∷ String → String
clearScripts n = case reverse (dropWhile (`elem` scripts) (reverse n)) of
  [] → n
  n' → n'
  where scripts = "'′" ++ subscriptDigits ++ ['0' .. '9']

-- | The subscript digits
subscriptDigits ∷ [Char]
subscriptDigits = "₀₁₂₃₄₅₆₇₈₉"

-- | Lists of name candidates for type variables, exotic type variables
--   (during unification), and variables.
tvNames, exNames, varNames ∷ [Name]
tvNames = namesFrom "αβγδ"
exNames = namesFrom "efgh"
varNames = namesFrom ['i' .. 'z']

-- | @freshName sugg avoid cands@ attempts to generate a fresh name
--   as follows:
--
--   * if @sugg@ is @Here n@, then it returns @n@ if @n@ is not in
--     @avoid@, and otherwise subscripts @n@ until if finds a fresh
--     name.
--   * Otherwise, return the first name from @cands@ that isn't in
--     @avoid@.
--
--   Returns the list of unused/undiscarded candidates along with the
--   fresh name
freshName ∷ Perhaps Name → [Name] → [Name] → Name
freshName pn avoid cands = case pn of
  Here n
    | n `notElem` avoid → n
    | otherwise         → takeFrom (namesFrom (clearScripts n))
  Nope                  → takeFrom cands
  where takeFrom = head . filter (`notElem` avoid)

-- | Like 'freshName', but produces a list of fresh names
freshNames ∷ [Perhaps Name] → [Name] → [Name] → [Name]
freshNames []       _     _     = []
freshNames (pn:pns) avoid cands = 
  let n'  = freshName pn avoid cands
   in n' : freshNames pns (n':avoid) cands

instance Ppr Empty where
  ppr = elimEmpty

instance Ppr Annot where
  pprPrec p (Annot _ t) = pprType p [] t

instance Ppr a ⇒ Ppr (Type a) where
  pprPrec p = pprType p []

-- | To pretty-print a type
pprType ∷ Ppr a ⇒ Int → [[Name]] → Type a → Ppr.Doc
pprType  = loop where
  loop p g t0 = case t0 of
    QuaTy u e t           →
      let quant = case u of AllQu → "∀"; ExQu → "∃"
          (tvs0, qls) = unzip e
          tvs         = freshNames tvs0 (concat g) tvNames
          btvs        = groupByQLits tvs qls
       in parensIf (p > 0) $
            Ppr.hang
              (Ppr.text quant Ppr.<+>
               (Ppr.fsep $ Ppr.punctuate Ppr.comma
                [ Ppr.fsep $
                    map Ppr.text names ++
                    if ql == L
                      then []
                      else [Ppr.char ':' Ppr.<+> Ppr.text (show ql)]
                | (ql,names) ← btvs ])
               Ppr.<> Ppr.char '.')
              2
              (loop 0 (tvs : g) t)
    VarTy (BoundVar ix jx (coerceOptional → n)) →
      Ppr.text $ maybe "?" id $ (listNth jx <=< listNth ix $ g) `mplus` n
    VarTy (FreeVar a)      → pprPrec p a
    ConTy "->" [t1, tq, t2] →
      parensIf (p > 1) $
        Ppr.sep [loop 2 g t1, pprQExp True 0 g tq, loop 0 g t2]
    ConTy "Pair" [t1, t2]   →
      parensIf (p > 2) $
        loop 2 g t1 Ppr.<+> Ppr.char '×' Ppr.<+> loop 3 g t2
    ConTy "end" []      → Ppr.text "[ ]"
    ConTy c []          → Ppr.text c
    ConTy c ts          →
      parensIf (p > 3) $
        Ppr.fsep (Ppr.text c : [ printer 4 g t
                               | t ← ts
                               | v ← getVariances c (length ts)
                               , let printer = if isQVariance v
                                                 then pprQExp False
                                                 else pprType ])
    t@(RowTy _ _ _)     →
      let (row, ext) = unfoldRow t
          fext       = case ext of
            ConTy "end" [] → id
            _              → (++[loop 0 g ext])
       in Ppr.sep .
          mapHead (Ppr.char '[' Ppr.<+>) .
          mapTail (Ppr.char '|' Ppr.<+>) .
          mapLast (Ppr.<+> Ppr.char ']') .
          fext $
            [ Ppr.text ni Ppr.<> Ppr.char ':' Ppr.<+> loop 0 g ti
            | (ni, ti) ← row ]
  groupByQLits = foldr2 each [] where
    each tv ql ((ql',tvs):rest)
      | ql == ql'   = ((ql',tv:tvs):rest)
    each tv ql rest = (ql,[tv]):rest

pprQExp ∷ Ppr a ⇒ Bool → Int → [[Name]] → Type a → Ppr.Doc
pprQExp arrowStyle p g t =
  case pureQualifier t of
    QExp U [] | arrowStyle → Ppr.char '→'
    QExp U [v]             → addArrow $ pprType 0 g (VarTy v)
    QExp U vs | arrowStyle → addArrow $ Ppr.fsep (pprType 0 g . VarTy <$> vs)
    QExp L _  → addArrow $ Ppr.char 'L'
    QExp q vs → addArrow $ pprType p g (ConTy (show q) (VarTy <$> vs))
  where addArrow doc
          | arrowStyle = Ppr.char '-' Ppr.<> doc Ppr.<> Ppr.char '>'
          | otherwise  = doc

  {-
pprQExp True       _ _ (ConTy "U" []) = Ppr.char '→'
pprQExp True       _ _ (ConTy "L" _)  = Ppr.text "-L>"
pprQExp arrowStyle _ _ (ConTy "L" _)  = Ppr.char 'L'
pprQExp arrowStyle p g (ConTy q   vs) = case pureQualifier (ConTy q vs)
  -}

-- | To pretty-print a pattern and return the list of names of
--   the bound variables.  (Avoiding the given list of names.)
pprPatt ∷ Ppr a ⇒ Int → [Name] → Patt a → (Ppr.Doc, [Name])
pprPatt p0 avoid0 π0 = evalRWS (loop p0 π0) () avoid0 where
  loop _ (VarPa pn)   = Ppr.text <$> getName pn
  loop _ WldPa        = return (Ppr.char '_')
  loop _ (ConPa c []) = return (Ppr.text c)
  loop p (ConPa c πs) = do
    docs ← mapM (loop 2) πs
    return $
      parensIf (p > 1) $
        Ppr.sep (Ppr.text c : docs)
  loop p (InjPa c π)  = do
    doc ← loop 1 π
    return $
      parensIf (p > 1) $
        Ppr.char '`' Ppr.<> Ppr.text c Ppr.<+> doc
  loop p (AnnPa π annot) = do
    πdoc ← loop 1 π
    return $
      parensIf (p > 0) $
        Ppr.hang πdoc 2 (Ppr.char ':' Ppr.<+> ppr annot)
  getName pn = do
    avoid ← get
    let name = freshName pn avoid varNames
    put (name:avoid)
    tell [name]
    return name

-- | Given a pretty-printing precedence, a list of names to avoid, and
--   a list of patterns, pretty-print the patterns and return a list
--   of lists of their bound names.
pprPatts ∷ Ppr a ⇒ Int → [Name] → [Patt a] → ([Ppr.Doc], [[Name]])
pprPatts _ _     []     = ([], [])
pprPatts p avoid (π:πs) =
  let (doc, names)   = pprPatt p avoid π
      (docs, names') = pprPatts p (names++avoid) πs
   in (doc:docs, names:names')

-- | To pretty-print a closed term.
instance Ppr a ⇒ Ppr (Term a) where
  ppr = pprTerm []

-- | To pretty-print a term, given a name environment.
pprTerm ∷ Ppr a ⇒ [[Name]] → Term a → Ppr.Doc
pprTerm  = loop 0 where
  loop p g e0 = case e0 of
    AnnTm e annot       → parensIf (p > 1) $
      Ppr.fsep [ loop 1 g e, Ppr.text ":", ppr annot ]
    AbsTm _ _           →
      let (πs, e)        = unfoldAbs e0
          (πdocs, names) = pprPatts 3 (concat g) πs
       in parensIf (p > 0) $
            Ppr.hang
              (Ppr.char 'λ'
                 Ppr.<> Ppr.fsep πdocs
                 Ppr.<> Ppr.char '.')
              2
              (loop 0 (reverse names ++ g) e)
    LetTm π e1 e2       →
      let (πdoc, names) = pprPatt 0 (concat g) π
       in parensIf (p > 0) $
            Ppr.hang
              (Ppr.text "let" Ppr.<+> πdoc Ppr.<+> Ppr.char '=' Ppr.<+>
               loop 0 g e1)
              1
              (Ppr.text "in" Ppr.<+> loop 0 (names : g) e2)
    MatTm e1 bs         →
      parensIf (p > 0) . Ppr.vcat $
        Ppr.text "match" Ppr.<+> loop 0 g e1 Ppr.<+> Ppr.text "with" :
        [ let (πdoc, names) = pprPatt 0 (concat g) πi
           in Ppr.hang
                (Ppr.char '|' Ppr.<+> πdoc Ppr.<+> Ppr.char '→')
                4
                (loop 0 (names : g) ei)
        | (πi, ei) ← bs ]
    RecTm bs e2         →
      parensIf (p > 0) $
        let names           = foldr each [] bs
            each (pn,_) ns' = freshName pn (ns' ++ concat g) varNames : ns'
         in Ppr.text "let" Ppr.<+>
            Ppr.vcat
              [ Ppr.text kw Ppr.<+>
                Ppr.hang
                  (Ppr.text ni Ppr.<+> Ppr.char '=')
                  2
                  (loop 0 (names : g) ei)
              | ni      ← names
              | (_,ei)  ← bs
              | kw      ← "rec" : repeat "and" ]
            Ppr.$$ Ppr.text " in" Ppr.<+> loop 0 (names : g) e2
    VarTm (BoundVar ix jx (coerceOptional → n)) →
      Ppr.text $ maybe "?" id $ (listNth jx <=< listNth ix $ g) `mplus` n
    VarTm (FreeVar name)   → ppr name
    ConTm name es       → parensIf (p > 2 && not (null es)) $
      Ppr.sep (Ppr.text name : map (loop 3 g) es)
    LabTm inj name     →
      Ppr.char (if inj then '`' else '#') Ppr.<> Ppr.text name
    AppTm e1 e2         → parensIf (p > 2) $
      Ppr.sep [loop 2 g e1, loop 3 g e2]

instance Show Annot where
  show = Ppr.render . ppr

-- deriving instance Show a ⇒ Show (Type a)
instance Ppr a ⇒ Show (Type a) where
  showsPrec p t = showString (Ppr.render (pprPrec p t))

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
  , "∀ α. α"                    ==> allTy [L] (bv 0 0)
  , "∀ α : U. α"                ==> allTy [U] (bv 0 0)
  , "∀ α : R. α"                ==> allTy [R] (bv 0 0)
  , "∀ α : A. α"                ==> allTy [A] (bv 0 0)
  , "∀ α : L. α"                ==> allTy [L] (bv 0 0)
  , "∀ α β. α"                  ==> allTy [L,L] (bv 0 0)
  , "∀ α β. β"                  ==> allTy [L,L] (bv 0 1)
  , "∀ α, β. α"                 ==> allTy [L,L] (bv 0 0)
  , "∀ α, β : U. β"             ==> allTy [L,U] (bv 0 1)
  , "∃ α. α"                    ==> exTy [L] (bv 0 0)
  , "∃ α β. α"                  ==> exTy [L,L] (bv 0 0)
  , "∃ α β. β"                  ==> exTy [L,L] (bv 0 1)
  , "∀ α β. C α → C β"
      ==> allTy [L,L] (c (bv 0 0) ↦ c (bv 0 1))
  , "∀ α. ∀ β. C α → C β → A"
      ==> allTy [L] (allTy [L] (c (bv 1 0) ↦ c (bv 0 0) ↦ a))
  , "∀ α. α → ∀ β. β → α"
      ==> allTy [L] (bv 0 0 ↦ allTy [L] (bv 0 0 ↦ bv 1 0))
  , "∃ α β. C α → C β"
      ==> exTy [L,L] (c (bv 0 0) ↦ c (bv 0 1))
  , "∃ α. ∃ β. C α → C β → A"
      ==> exTy [L] (exTy [L] (c (bv 1 0) ↦ c (bv 0 0) ↦ a))
  , "∃ α. α → ∃ β. β → α"
      ==> exTy [L] (bv 0 0 ↦ exTy [L] (bv 0 0 ↦ bv 1 0))
  , "∃ α ∀ β. C α → C β → A"
      ==> exTy [L] (allTy [L] (c (bv 1 0) ↦ c (bv 0 0) ↦ a))
  , "∃ α. α → ∀ β. β → α"
      ==> exTy [L] (bv 0 0 ↦ allTy [L] (bv 0 0 ↦ bv 1 0))
  , "∀ α β. α → β"              <==> "∀ β α. β → α"
  , "∀ α. C α → ∀ α. C α"       <==> "∀ δ. C δ → ∀ e. C e"
  , "∃ α β. α → β"              <==> "∃ β α. β → α"
  , "∃ α. C α → ∃ α. C α"       <==> "∃ δ. C δ → ∃ e. C e"
  ]
  where
    a = ConTy "A" []
    b = ConTy "B" []
    c t = ConTy "C" [t]
    bv m n = VarTy (BoundVar m n Nope)

(<==>*) ∷ String → String → T.Assertion
str1 <==>* str2 = T.assertBool (str1 ++ " <==> " ++ str2) (t1 == t2) where
  t1, t2 ∷ [(Type Empty, String)]
  t1 = map (first standardize) (reads str1)
  t2 = map (first standardize) (reads str2)

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
      ((standardize (read str) ∷ Type Empty) ==
       allTy [L] (VarTy (boundVar 0 0 "α") ↦
                  allTy [L] (VarTy (boundVar 0 0 "β") ↦
                             VarTy (boundVar 1 0 "α"))))
  ]

{-
tryParsePprPatt ∷ String → IO ()
tryParsePprPatt s =
  case runParser (parsePatt 0 <* eof) [] "" s of
    Left e              → print e
    Right (patt, names) → print (pprPatt 0 names (patt ∷ Patt Empty))

-}

