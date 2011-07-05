{-# LANGUAGE
      BangPatterns,
      DeriveFunctor,
      EmptyDataDecls,
      FlexibleInstances,
      FunctionalDependencies,
      GeneralizedNewtypeDeriving,
      MultiParamTypeClasses,
      NoImplicitPrelude,
      ParallelListComp,
      PatternGuards,
      RankNTypes,
      ScopedTypeVariables,
      StandaloneDeriving,
      TupleSections,
      TypeSynonymInstances,
      UndecidableInstances,
      UnicodeSyntax,
      ViewPatterns
  #-}
module Syntax where

import Control.Monad.ST (runST)
import qualified Data.Char      as Char
import qualified Data.List      as List
import qualified Data.Map       as Map
import qualified Data.Set       as Set
import Text.Parsec hiding ((<|>), many, optional)
import Text.Parsec.Token
import qualified Text.PrettyPrint as Ppr
import qualified Unsafe.Coerce

import qualified Test.HUnit as T

import Util
import Ppr
import MonadRef

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

instance Lattice a ⇒ Lattice (Maybe a) where
  Just a  ⊔ Just b  = Just (a ⊔ b)
  Nothing ⊔ b       = b
  a       ⊔ Nothing = a
  Just a  ⊓ Just b  = Just (a ⊓ b)
  Nothing ⊓ _       = Nothing
  _       ⊓ Nothing = Nothing

newtype DUAL a = DUAL { dual ∷ a } deriving (Eq, Show)

instance Lattice a ⇒ Lattice (DUAL a) where
  DUAL a ⊔ DUAL b = DUAL (a ⊓ b)
  DUAL a ⊓ DUAL b = DUAL (a ⊔ b)

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

data QLit = U | A
  deriving (Eq, Ord, Show)

instance Ppr QLit where ppr = Ppr.text . show

readQLit ∷ String → Maybe QLit
readQLit "U" = Just U
readQLit "A" = Just A
readQLit _   = Nothing

qLitSigil ∷ QLit → Char
qLitSigil U = '\''
qLitSigil A = '`'

instance Bounded QLit where
  minBound = U
  maxBound = A

instance Lattice QLit where
  A ⊔ _ = A
  U ⊔ q = q
  --
  A ⊓ q = q
  U ⊓ _ = U
  --
  A ⊑ U = False
  _ ⊑ _ = True

-- | @a \-\ b@ is the least @c@ such that
--   @a ⊑ b ⊔ c@.  (This is sort of dual to a pseudocomplement.)
(\-\) ∷ QLit → QLit → QLit
A \-\ U = A
_ \-\ _ = U

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
  QExp A  _  `mappend` _            = qlitexp A
  _          `mappend` QExp A   _   = qlitexp A
  QExp U  vs `mappend` QExp U   vs' = QExp U (vs ++ vs')

-- | For now, we hard-code the qualifiers of several type constructors
--   and consider the rest to be like tuples by default.
--   PRECONDITION: The arguments are well-formed qualifiers.
--   POSTCONDITION: The result is a well-formed qualifiers.
getQualifier ∷ Name → [QExp v] → QExp v
getQualifier "->"    [_,qe,_] = qe
getQualifier "U"     qes      = mconcat (qlitexp U : qes)
getQualifier "A"     qes      = mconcat (qlitexp A : qes)
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

instance Ppr Variance where ppr = Ppr.text . show

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
getVariances "Q"     i = replicate i QCovariant
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
--- Kinds
---

-- | Kinds are used internally to track which type variables carry
--   actual type information and which merely represent qualifiers.
data Kind
  = QualKd
  | TypeKd
  deriving (Eq, Ord, Enum, Bounded, Show)

varianceToKind ∷ Variance → Kind
varianceToKind var = if isQVariance var then QualKd else TypeKd

instance Ppr Kind where ppr = Ppr.text . show

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
  | RecTy (Perhaps Name) (Type a)
  deriving (Eq, Ord, Functor)
  -- NB: Ord instance is not the subsumption order, but merely an order
  -- used for binary search trees.

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

tupleTy ∷ [Type a] → Type a
tupleTy []     = ConTy "U" []
tupleTy (τ:τs) = foldl pairTy τ τs

endTy  ∷ Type a
endTy  = ConTy "end" []

t1 ↦ t2 = arrTy t1 (qlitexp U) t2
infixr 6 ↦

-- | A type annotation. The list of 'Name's records the free
--   type variables in the 'Type'.
data Annot = Annot [(Name, QLit)] (Type Name)
  deriving Eq

---
--- GENERIC DEREFERENCING
---

type ReadTV v m = v → m (Either v (Type v))

-- | Class for a dereferencing operation for free type variable
--   representation @v@ in some monad @m@.
class Monad m ⇒ MonadReadTV v m where readTV ∷ ReadTV v m

-- | A monad transformer that allows specifying the dereference
--   operation.
newtype ReadTV_T v m a
  = ReadTV_T {
      unReadTV_T ∷ ReaderT (ReadTV v m) m a
    }
  deriving (Functor, Applicative, Monad)

-- | Run the 'ReadTV_T' monad transformer with a given dereference
--   operation
runReadTV_T ∷ ReadTV_T v m a → ReadTV v m → m a
runReadTV_T = runReaderT . unReadTV_T

instance MonadTrans (ReadTV_T v) where lift = ReadTV_T . lift

instance Monad m ⇒ MonadReadTV v (ReadTV_T v m) where
  readTV v = do
    derefer ← ReadTV_T ask
    lift (derefer v)

-- | The type of a pure 'MonadReadTV' computation where the dereferencing
--   operation always returns the type variable without attempting to
--   actually dereference.
type PureDeref v = ReadTV_T v Identity

-- | Run a dereferencing computation purely.
runPureDeref   ∷ PureDeref v a → a
runPureDeref m = runIdentity (runReadTV_T m (return . Left))

---
--- TYPE FOLDS
---

-- | Fold a type, while dereferencing type variables
foldType ∷ ∀ m v r s. MonadReadTV v m ⇒
           -- | For quantifiers
           (∀a. Quant → [(Perhaps Name, QLit)] → ([s] → (r → r) → a) → a) →
           -- | For bound variables
           ((Int, Int) → Perhaps Name → Maybe s → r) →
           -- | For free variables
           (v → r) →
           -- | For constructor applications
           (Name → [r] → r) →
           -- | For row type labels
           (Name → r → r → r) →
           -- | For recursive types
           (∀a. Perhaps Name → (s → (r → r) → a) → a) →
           -- | Type to fold
           Type v →
           m r
foldType fquant fbvar ffvar fcon frow frec t0 =
  runReaderT (loop t0) []
  where
  loop (QuaTy q αs t)           =
    fquant q αs $ \ss f → f `liftM` local (ss:) (loop t)
  loop (VarTy (BoundVar i j n)) = do
    env ← ask
    return (fbvar (i, j) n (look i j env))
  loop (VarTy (FreeVar v))      = do
    mt ← lift (readTV v)
    case mt of
      Left v' → return (ffvar v')
      Right t → loop t
  loop (ConTy n ts)             =
    fcon n `liftM` sequence
      [ if isQVariance v
          then loop . unQExp =<< lift (qualifier t)
          else loop t
      | t ← ts
      | v ← getVariances n (length ts) ]
  loop (RowTy n t1 t2)          =
    frow n `liftM` loop t1 `ap` loop t2
  loop (RecTy n t)              =
    frec n (\s f → f `liftM` local ([s]:) (loop t))
  --
  look i j env
    | rib:_ ← drop i env
    , elt:_ ← drop j rib = Just elt
  look _ _ _             = Nothing

mkBvF   ∷ (Int → Int → Perhaps Name → r) →
          (Int, Int) → Perhaps Name → a → r
mkBvF f (i, j) pn _ = f i j pn

mkQuaF
  ∷ (Quant → [(Perhaps Name, QLit)] → r → s) →
    (∀a. Quant → [(Perhaps Name, QLit)] → ([(Int, Int)] → (r → s) → a) → a)
mkQuaF f q αs k = k [ (0, j) | j ← [0 .. length αs - 1] ] (f q αs)

mkRecF ∷ (Perhaps Name → r → s) →
         (∀a. Perhaps Name → ((Int, Int) → (r → s) → a) → a)
mkRecF f pn k = k (0, 0) (f pn)

-- | Get the qualifier of a type
qualifier ∷ MonadReadTV v m ⇒ Type v → m (QExp v)
qualifier = foldType fquant fbvar ffvar fcon frow frec
  where
  fquant AllQu αs k      = k (U <$ αs) bumpQExp
  fquant ExQu  αs k      = k (snd <$> αs) bumpQExp
  fbvar _ _    (Just ql) = qlitexp ql
  fbvar (i,j) n Nothing  = qvarexp (BoundVar i j n)
  ffvar                  = qvarexp . FreeVar
  fcon n qes             = getQualifier n qes
  frow _ qe1 qe2         = getQualifier "*" [qe1, qe2]
  frec _ k               = k U bumpQExp
  bumpQExp (QExp q vs)   = QExp q (bumpVar (-1) <$> vs)

-- | Get something in the *form* of a qualifier without dereferencing
pureQualifier ∷ ∀ v. Type v → QExp v
pureQualifier t = runPureDeref (qualifier t ∷ PureDeref v (QExp v))

-- | Monadic version of type folding
foldTypeM
  ∷ ∀m v r s. MonadReadTV v m ⇒
    (∀a. Quant → [(Perhaps Name, QLit)] → ([s] → (r → m r) → a) → a) →
    ((Int, Int) → Perhaps Name → Maybe s → m r) →
    (v → m r) →
    (Name → [r] → m r) →
    (Name → r → r → m r) →
    (∀a. Perhaps Name → (s → (r → m r) → a) → a) →
    Type v →
    m r
foldTypeM fquant fbvar ffvar fcon frow frec t =
  join (foldType fquantM fbvar ffvar fconM frowM frecM t) where
    fquantM q αs k = fquant q αs $ k <$.> (=<<)
    fconM c mrs    = fcon c =<< sequence mrs
    frowM c t1 t2  = join (frow c `liftM` t1 `ap` t2)
    frecM n k      = frec n $ k <$.> (=<<)

-- The type monad does substitution
instance Monad Type where
  QuaTy u e t            >>= f = QuaTy u e (t >>= f)
  VarTy (FreeVar r)      >>= f = f r
  VarTy (BoundVar i j n) >>= _ = VarTy (BoundVar i j n)
  ConTy n ts             >>= f = ConTy n (map (>>= f) ts)
  RowTy n t1 t2          >>= f = RowTy n (t1 >>= f) (t2 >>= f)
  RecTy n t              >>= f = RecTy n (t >>= f)
  return = VarTy . FreeVar

-- | Apply a total substitution to a free type variable.  Total in this
--   case simply means that the type variable must be in the domain of
--   the substitution.
totalSubst ∷ Eq a ⇒ [a] → [Type b] → a → Type b
totalSubst (α:αs) (τ:τs) β
  | α == β          = τ
  | otherwise       = totalSubst αs τs β
totalSubst _ _ _ = error "BUG! substsAll saw unexpected free tv"

-- | Is the given type ground (type-variable and quantifier free)?
isGroundType ∷ MonadReadTV v m ⇒ Type v → m Bool
isGroundType = foldType (\_ _ k → k (repeat False) (const False))
                        (\_ _ → maybe False id)
                        (\_ → False) (\_ → and) (\_ → (&&))
                        (\_ k → k True id)

-- | Is the given type closed? (ASSUMPTION: The type is locally closed)
isClosedType ∷ MonadReadTV v m ⇒ Type v → m Bool
isClosedType = foldType (\_ _ k → k (repeat True) id)
                        (\_ _ → maybe False id)
                        (\_ → False) (\_ → and) (\_ → (&&))
                        (\_ k → k True id)

-- | Is the given type quantifier free?
isMonoType ∷ MonadReadTV v m ⇒ Type v → m Bool
isMonoType = foldType (mkQuaF (\_ _ _ → False))
                      (mkBvF (\_ _ _ → True))
                      (\_ → True) (\_ → and) (\_ → (&&))
                      (mkRecF (\_ _ → True))

-- | Is the given type (universal) prenex?
--   (Precondition: the argument is standard)
isPrenexType ∷ MonadReadTV v m ⇒ Type v → m Bool
isPrenexType (QuaTy AllQu _ τ)   = isMonoType τ
isPrenexType (VarTy (FreeVar r)) =
  either (\_ → return True) isPrenexType =<< readTV r
isPrenexType τ                   = isMonoType τ

---
--- Equality and normalization of equirecursive types.
---

newtype REC_TYPE a = REC_TYPE { unREC_TYPE ∷ Type a }

instance Ppr a ⇒ Show (REC_TYPE a) where
  showsPrec = showsPrec <$.> unREC_TYPE

instance Ppr a ⇒ Ppr (REC_TYPE a) where
  pprPrec = pprPrec <$.> unREC_TYPE

instance Ord a ⇒ Eq (REC_TYPE a) where
  a == b   = compare a b == EQ

instance Ord a ⇒ Ord (REC_TYPE a) where
  compare (REC_TYPE τ10) (REC_TYPE τ20) =
    evalState (loop τ10 τ20) Set.empty where
      thenCompareM m1 m2 = do
        ord ← m1
        case ord of
          EQ → m2
          _  → return ord
      compareM a b = return (compare a b)
      loop τ1 τ2 = do
        seen ← get
        if (Set.member (τ1, τ2) seen || Set.member (τ2, τ1) seen)
          then return EQ
          else do
            put (Set.insert (τ1, τ2) seen)
            case (τ1, τ2) of
              (RecTy _ τ1', _)
                → loop (openTy 0 [τ1] τ1') τ2
              (_, RecTy _ τ2')
                → loop τ1 (openTy 0 [τ2] τ2')
              (QuaTy q1 qls1 τ1', QuaTy q2 qls2 τ2')
                → compareM q1 q2 `thenCompareM`
                  compareM qls1 qls2 `thenCompareM`
                  loop τ1' τ2'
              (QuaTy _ _ _, _)
                → return LT
              (VarTy _, QuaTy _ _ _)
                → return GT
              (VarTy v1, VarTy v2)
                → return (v1 `compare` v2)
              (VarTy _, _)
                → return LT
              (ConTy _ _, QuaTy _ _ _)
                → return GT
              (ConTy _ _, VarTy _)
                → return GT
              (ConTy n1 τs1, ConTy n2 τs2)
                → compareM n1 n2 `thenCompareM`
                  compareM (length τs1) (length τs2) `thenCompareM`
                  foldl' thenCompareM (return EQ) (zipWith loop τs1 τs2)
              (ConTy _ _, _)
                → return LT
              (RowTy _ _ _, QuaTy _ _ _)
                → return GT
              (RowTy _ _ _, VarTy _)
                → return GT
              (RowTy _ _ _, ConTy _ _)
                → return GT
              (RowTy n1 τ1f τ1r, RowTy n2 τ2f τ2r)
                → compareM n1 n2 `thenCompareM`
                  loop τ1f τ2f `thenCompareM`
                  loop τ1r τ2r

-- | Put all recursion in standard form.
--   PRECONDITION: The type is in 'standardize' standard form
standardizeMus ∷ ∀ a r m. (Ord a, MonadRef r m) ⇒ Type a → m (Type a)
standardizeMus t00 = do
  counter ← newRef 0
  let loop g0 t0 = do
        case Map.lookup (REC_TYPE t0) g0 of
          Just (i, used') → do
            writeRef used' True
            return (fvTy i)
          Nothing → do
            i    ← gensym
            used ← newRef False
            let g = Map.insert (REC_TYPE t0) (i, used) g0
            t0'  ← case t0 of
              QuaTy u qls t → do
                is ← mapM (const gensym) qls
                t' ← loop g (openTy 0 (map fvTy is) t)
                return (QuaTy u qls (closeTy 0 is t'))
              ConTy n ts    → ConTy n `liftM` mapM (loop g) ts
              VarTy _       → return t0
              RowTy n t1 t2 → RowTy n `liftM` loop g t1 `ap` loop g t2
              RecTy _ t1    → loop g0 (openTy 0 [t0] t1)
            wasUsed ← readRef used
            return $ if wasUsed
              then RecTy Nope (closeTy 0 [i] t0')
              else t0'
      gensym  = do
        i ← readRef counter
        writeRef counter (i + 1)
        return (Right i)
      clean = fmap (either id (error "BUG! (standardizeMus)"))
  gensym
  t00' ← loop Map.empty (fmap Left t00)
  return (clean t00')

---
--- Patterns
---

data Patt a
  = VarPa Name
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
totalPatt (VarPa _)         = True
totalPatt WldPa             = True
totalPatt (ConPa "Pair" πs) = all totalPatt πs
totalPatt (ConPa "U" [])    = True
totalPatt (ConPa "T" [])    = True
totalPatt (ConPa _ _)       = False
totalPatt (InjPa _ _)       = False
totalPatt (AnnPa π _)       = totalPatt π

pattHasWild ∷ Patt a → Bool
pattHasWild (VarPa _)    = False
pattHasWild WldPa        = True
pattHasWild (ConPa _ πs) = any pattHasWild πs
pattHasWild (InjPa _ π)  = pattHasWild π
pattHasWild (AnnPa π _)  = pattHasWild π

pattHasAnnot ∷ Patt a → Bool
pattHasAnnot (VarPa _)    = False
pattHasAnnot WldPa        = False
pattHasAnnot (ConPa _ πs) = any pattHasAnnot πs
pattHasAnnot (InjPa _ π)  = pattHasAnnot π
pattHasAnnot (AnnPa _ _)  = True

pattBv ∷ Patt a → [Name]
pattBv (VarPa n)    = [n]
pattBv WldPa        = []
pattBv (ConPa _ πs) = concatMap pattBv πs
pattBv (InjPa _ π)  = pattBv π
pattBv (AnnPa π _)  = pattBv π

---
--- Terms
---

data Term a
  = AbsTm (Patt a) (Term a)
  | LetTm (Patt a) (Term a) (Term a)
  | MatTm (Term a) [(Patt a, Term a)]
  | RecTm [(Name, Maybe Annot, Term a)] (Term a)
  | VarTm Name
  | ConTm Name [Term a]
  | LabTm Bool Name
  | AppTm (Term a) (Term a)
  | AnnTm (Term a) Annot
  deriving Functor

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

termFv ∷ Term a → Set.Set Name
termFv e0 = case e0 of
  AbsTm π e      → mask π e
  MatTm e bs     → Set.unions (termFv e : map (uncurry mask) bs)
  LetTm π e1 e2  → termFv e1 `Set.union` mask π e2
  RecTm bs e2    → Set.unions (termFv e2 : map (termFv . sel3) bs)
                     Set.\\ Set.fromList (map sel1 bs)
  VarTm n        → Set.singleton n
  ConTm _ es     → Set.unions (map termFv es)
  LabTm _ _      → Set.empty
  AppTm e1 e2    → termFv e1 `Set.union` termFv e2
  AnnTm e _      → termFv e
  where
  mask π e = termFv e Set.\\ Set.fromList (pattBv π)

---
--- Initial environment
---

γ0' ∷ [(Name, String)]
γ0' = [ ("id",          "∀ α. α → α")
      , ("ids",         "List (∀ α. α → α)")
      , ("choose",      "∀ α. α → α -α> α")
      , ("discard",     "∀ α. α → α")
      , ("apply",       "∀ α β γ. (α -γ> β) → α -γ> β")
      , ("revapp",      "∀ α β γ. α → (α -γ> β) -α γ> β")
      -- FCP
      , ("ids",         "List (∀ α. α → α)")
      , ("poly",        "(∀ α. α -> α) → Int × Bool")
      -- Lists
      , ("single",      "∀ α. α → List α")
      , ("nil",         "∀ α. List α")
      , ("cons",        "∀ α. α → List α -α> List α")
      , ("map",         "∀ α β. (α → β) → List α → List β")
      , ("foldr",       "∀ α β. (α → β -A> β) → β → List α -β> β")
      , ("head",        "∀ α. List α → α")
      , ("tail",        "∀ α. List α → List α")
      , ("app",         "∀ α. List α → List α → List α")
      -- Ref cells
      , ("ref",         "∀ α β. α → Ref β α")
      , ("uref",        "∀ α. α → Ref U α")
      , ("aref",        "∀ α. α → Ref A α")
      , ("swapRef",     "∀ α β. Ref β α × α → Ref β α × α")
      , ("swapRef'",    "∀ α β. Ref A α × β → \
                        \       Ref A β × α")
      , ("readRef",     "∀ 'α β. Ref β 'α → 'α")
      , ("readRef'"  ,  "∀ 'α β. Ref β 'α → Ref β 'α × 'α")
      , ("freeRef'",    "∀ α. Ref A α → α")
      , ("writeRef",    "∀ α β. Ref β α × α → T")
      , ("writeRef'",   "∀ α β. Ref A α × β → Ref A β")
      -- Products
      , ("pair",        "∀ α β. α → β -α> α × β")
      , ("fst",         "∀ α β. α × β → α")
      , ("snd",         "∀ α β. α × β → β")
      -- Sums
      , ("inl",         "∀ α β. α → Either α β")
      , ("inr",         "∀ α β. β → Either α β")
      , ("either",      "∀ α β γ. (α -A> γ) → (β -A> γ) -A> Either α β -A> γ")
      -- Uniqueness types?
      , ("openFile",    "String → File A")
      , ("readFile",    "∀ α. File α → File α")
      , ("writeFile",   "File A → File A")
      , ("closeFile",   "File A → T")
      -- Simple ST-like thing
      , ("runST'",      "∀ β. (all s. ST s β) → β")
      , ("returnST'",   "∀ α s. α → ST s Z")
      -- ST Monad
      , ("runST",       "∀ α β. (all s. α → ST s β) → β")
      , ("bindST",      "∀ α β s. ST s α → (α → ST s β) → ST s β")
      , ("returnST",    "∀ α s. α → ST s α")
      , ("newSTRef",    "∀ α s. α → ST s (STRef s α)")
      , ("readSTRef",   "∀ 'α s. STRef s 'α → ST s 'α")
      -- Any
      , ("eat",         "∀ α β. α → β → β")
      , ("eatU",        "∀ 'α β. 'α → β → β")
      , ("eatA",        "∀ α β. α → β → β")
      , ("bot",         "∀ α. α")
      , ("botU",        "∀ 'α. 'α")
      , ("botA",        "∀ α. α")
      , ("cast",        "∀ α β. α → β")
      ]

γ0 ∷ [(Name, Type a)]
γ0 = second (elimEmptyF . read) <$> γ0'

unγ0 ∷ Map.Map Name a → Map.Map Name a
unγ0 = (Map.\\ γmap) where γmap = Map.fromList γ0'

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
  RecTy name t     → RecTy name (next t)
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
  RecTy n t     → RecTy n (next t)
  where
    this = closeTy k vs
    next = closeTy (k + 1) vs

-- | Add the given quantifier while binding the given list of variables
closeWith ∷ Ord a ⇒ Quant → [a] → Type a → Type a
closeWith = closeWithNames []

-- | Build a recursive type by closing and binding the given variable
closeRec ∷ Ord a ⇒ a → Type a → Type a
closeRec a t = RecTy Nope (closeTy 0 [a] t)

-- | Add the given quantifier while binding the given list of variables
closeWithQuals ∷ Ord a ⇒ [QLit] → Quant → [a] → Type a → Type a
closeWithQuals qls = closeWithNames (map (Nope,) qls)

-- | Add the given quantifier while binding the given list of variables
closeWithNames ∷ Ord a ⇒
                 [(Perhaps Name, QLit)] → Quant → [a] → Type a → Type a
closeWithNames _   _ []  ρ = ρ
closeWithNames pns q tvs ρ = standardize (QuaTy q pns' (closeTy 0 tvs ρ))
  where pns' = take (length tvs) (pns ++ repeat (Nope, maxBound))

{-
-- | @substTy τ' α 't@ substitutes @τ'@ for free variable @α@ in @τ@.
substTy ∷ Eq a ⇒ Type a → a → Type a → Type a
substTy τ' α = runIdentity . typeMapM each where
  each β | α == β    = return τ'
         | otherwise = return (fvTy β)
-}

-- | Is the given type locally closed to level k?  A type is locally closed
--   if none of its bound variables point to quantifiers "outside" the
--   type.
--
--   ASSUMPTION: No bound variables are lurking behind an apparent free
--   variable, because @lcTy@ doesn't attempt to dereference free
--   variables.  This should be an invariant, because it would come
--   about only as a result of a capturing substitution.
lcTy ∷ Int → Type a → Bool
lcTy  = loop where
  loop k (QuaTy _ _ t)            = loop (k + 1) t
  loop k (VarTy (BoundVar i _ _)) = k > i
  loop _ (VarTy (FreeVar _))      = True
  loop k (ConTy _ ts)             = all (loop k) ts
  loop k (RowTy _ t1 t2)          = loop k t1 && loop k t2
  loop k (RecTy _ t)              = loop (k + 1) t

-- | Are there no bound vars of level k?
lcTyK ∷ Int → Type a → Bool
lcTyK  = loop where
  loop k (QuaTy _ _ t)            = loop (k + 1) t
  loop k (VarTy (BoundVar i _ _)) = k /= i
  loop _ (VarTy (FreeVar _))      = True
  loop k (ConTy _ ts)             = all (loop k) ts
  loop k (RowTy _ t1 t2)          = loop k t1 && loop k t2
  loop k (RecTy _ t)              = loop (k + 1) t

-- | Is the given type contractive at the given level? (A type is
--   contractive if all occurrences of level k type variables appear
--   under the field position of a row type.)
contractiveTy ∷ Type a → Bool
contractiveTy = loop 0 where
  loop k (QuaTy _ _ t)            = loop (k + 1) t
  loop k (VarTy (BoundVar i _ _)) = k /= i
  loop _ (VarTy (FreeVar _))      = True
  loop k (ConTy _ ts)             = all (loop k) ts
  loop k (RowTy _ _ t2)           = loop k t2 -- don't check field
  loop k (RecTy _ t)              = loop (k + 1) t

-- | Find the kinds of the rib 0 type variables in an opened type, where
--   the given 'Int' is the width of the rib.
inferKindsTy ∷ Type a → [Kind]
inferKindsTy = varianceToKind <$$> loop 0 where
  loop k (QuaTy _ _ t)            = loop (k + 1) t
  loop k (VarTy (BoundVar i j _))
    | i == k                      = replicate j 0 ++ 1 : repeat 0
    | otherwise                   = repeat 0
  loop _ (VarTy (FreeVar _))      = repeat 0
  loop k (ConTy c ts)             =
    foldr (zipWith (+)) (repeat 0)
      [ let t' = if isQVariance var
                   then toQualifierType (pureQualifier t)
                   else t
         in map (* var) (loop k t')
      | var ← getVariances c (length ts)
      | t   ← ts ]
  loop k (RowTy _ t1 t2)          = zipWith (+) (loop k t1) (loop k t2)
  loop k (RecTy _ t)              = loop (k + 1) t

---
--- Occurrence analysis
---

{- | The number of occurrences of a variable in a term.  These
     are an abstraction of the natural numbers as zero, one, many, or
     some combinations thereof.
     (Note: no { 0, 2+ })

   U
   |
   |
   A
   |
   |
   Z
   |
   |
   E

-}
data Occurrence
  -- | Any number of times { 0, 1, 2+ }
  = UO
  -- | Zero or one times { 0, 1 }
  | AO
  -- | Zero times { 0 }
  | ZO
  -- | Dead code / error { }
  | EO
  deriving (Eq, Show)

instance Ppr Occurrence where ppr = Ppr.text . show

-- | Convert an occurrence to a representative list of numbers
occToInts ∷ Occurrence → [Int]
occToInts UO = [0, 1, 2]
occToInts AO = [0, 1]
occToInts ZO = [0]
occToInts EO = []

-- | Convert an occurrence to the best qualifier literal
occToQLit ∷ Occurrence → QLit
occToQLit UO = U
occToQLit AO = A
occToQLit ZO = A
occToQLit EO = A

instance Bounded Occurrence where
  minBound = EO
  maxBound = UO

instance Lattice Occurrence where
  EO ⊔ o  = o;  o  ⊔ EO = o
  ZO ⊔ o  = o;  o  ⊔ ZO = o
  AO ⊔ o  = o;  o  ⊔ AO = o
  _  ⊔ _  = UO
  --
  UO ⊓ o  = o;  o  ⊓ UO = o
  AO ⊓ o  = o;  o  ⊓ AO = o
  ZO ⊓ o  = o;  o  ⊓ ZO = o
  _  ⊓ _  = EO

-- Abstract arithmetic
instance Num Occurrence where
  fromInteger 0             = ZO
  fromInteger 1             = AO
  fromInteger z | z > 1     = UO
                | otherwise = EO
  abs = id
  negate = const EO
  signum o = bigJoin (map (fromInteger . toInteger . signum) (occToInts o))
  EO + _  = EO; _  + EO = EO
  ZO + o  = o;  o  + ZO = o
  _  + _  = UO
  --
  o  * o' = bigJoin $ do
    z  ← occToInts o
    z' ← occToInts o'
    return (fromInteger (toInteger (z * z')))

countOccsPatt ∷ Patt a → Term a → [Occurrence]
countOccsPatt π e = map (flip countOccs e) (pattBv π)

countOccs ∷ Name → Term a → Occurrence
countOccs x = loop where
  loop (AbsTm π e)
    | x `elem` pattBv π   = 0
    | otherwise           = loop e
  loop (LetTm π e1 e2)
    | x `elem` pattBv π   = loop e1
    | otherwise           = loop e1 + loop e2
  loop (MatTm e1 bs)      = loop e1 + bigJoin [ loop ei
                                              | (πi, ei) ← bs
                                              , x `notElem` pattBv πi ]
  loop (RecTm bs e2)
    | x `elem` map sel1 bs= 0
    | otherwise           = loop e2 + sum (map (loop . sel3) bs)
  loop (VarTm x')
    | x == x'             = 1
    | otherwise           = 0
  loop (ConTm _ es)       = sum (map loop es)
  loop (LabTm _ _)        = 0
  loop (AppTm e1 e2)      = loop e1 + loop e2
  loop (AnnTm e _)        = loop e

---
--- Free type variables
---

{-
  We're going to construct a framework for generic functions to compute
  the free type variables of a type.  It may be a bit over-engineered.
  The idea is to write a generic function that builds an 'FtvTree',
  which contains all the free type variables in the relevant piece of
  syntax, along with variance and recursive guard information.
-}

-- | A tree of free type variables, with variance and recursive guard
--   information
data FtvTree v
  -- | A single free type variable
  = FTSingle v
  -- | Updates the incoming variance to give the variance in
  --   the subtree
  | FTVariance (Variance → Variance) (FtvTree v)
  -- | Indicates that the subtree is guarded by a type constructor
  --   that allows recursion
  | FTGuard (FtvTree v)
  -- | A forest of 'FtvTree's
  | FTBranch [FtvTree v]
  deriving Functor

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
foldFtvTree ∷ (v → Variance → r → r) → (r → r) → r → FtvTree v → r
foldFtvTree fsingle fguard = loop Covariant where
  loop var acc (FTSingle v)       = fsingle v var acc
  loop var acc (FTVariance vf t)  = loop (vf var) acc t
  loop var acc (FTGuard t)        = fguard (loop var acc t)
  loop var acc (FTBranch ts)      = foldr (flip (loop var)) acc ts

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
  ftvTree  ∷ MonadReadTV v m ⇒ a → m (FtvTree v)
  -- | To fold over the free type variables in a piece of syntax.
  ftvFold  ∷ MonadReadTV v m ⇒
             (v → Variance → r → r) → (r → r) → r → a → m r
  -- | To get a map from free type variables to their variances.
  ftvV     ∷ MonadReadTV v m ⇒ a → m (VarMap v)
  -- | To get a map from free type variables to their guardedness
  ftvG     ∷ MonadReadTV v m ⇒ a → m (Map.Map v Bool)
  -- | To get a map from free type variables to a list of all their
  --   occurrences' variances.
  ftvSet   ∷ MonadReadTV v m ⇒ a → m (Set.Set v)
  -- | To get a list of the free type variables in a type (with no repeats).
  ftvList  ∷ MonadReadTV v m ⇒ a → m [v]
  -- | To get the tree of (apparent) free variables without trying to
  --   dereference anything
  ftvTreePure ∷ a → FtvTree v
  -- | To get the set of (apparent) free variables without trying to
  --   dereference anything
  ftvPure     ∷ a → VarMap v
  -- 
  --
  ftvFold fsingle fguard zero a
                 = foldFtvTree fsingle fguard zero `liftM` ftvTree a
  ftvV           = ftvFold (Map.insertWith (+)) id Map.empty
  ftvG           = ftvFold (\v _ → Map.insert v False) (True <$) Map.empty
  ftvSet         = ftvFold (const . Set.insert) id Set.empty
  ftvList        = liftM Set.toAscList . ftvSet
  ftvTreePure a  = runPureDeref (ftvTree a ∷ PureDeref v (FtvTree v))
  ftvPure a      = runPureDeref (ftvV a ∷ PureDeref v (VarMap v))

instance Ord v ⇒ Ftv (Type v) v where
  ftvTree = foldType
             (mkQuaF (\_ _ → id))
             (mkBvF (\_ _ _ → mempty))
             FTSingle
             (\c trees → FTBranch
                 [ FTVariance (* var) tree
                 | tree ← trees
                 | var  ← getVariances c (length trees) ])
             (\_ t1 t2 → FTBranch [FTGuard t1, t2])
             (mkRecF (\_ → id))

instance Ftv a v ⇒ Ftv [a] v where
  ftvTree a = FTBranch `liftM` mapM ftvTree a

instance Ftv a v ⇒ Ftv (Map.Map k a) v where
  ftvTree = ftvTree . Map.elems

instance (Ftv a v, Ftv b v) ⇒ Ftv (a,b) v where
  ftvTree (a,b) = liftM2 mappend (ftvTree a) (ftvTree b)

instance (Ftv a v, Ftv b v, Ftv c v) ⇒ Ftv (a,b,c) v where
  ftvTree (a,b,c) = ftvTree (a,(b,c))

instance Ftv a v ⇒ Ftv (Maybe a) v where
  ftvTree = maybe (return mempty) ftvTree

instance (Ftv a v, Ftv b v) ⇒ Ftv (Either a b) v where
  ftvTree = either ftvTree ftvTree

-- The free type variables in annotations, patterns, and terms give
-- the free names that are shared between annotations.
instance Ftv Annot (Name, QLit) where
  ftvTree (Annot nqls τ)   = return (addQLit <$> ftvTreePure τ)
    where
      addQLit name = (name, fromMaybe maxBound (lookup name nqls))

instance Ftv (Patt Empty) (Name, QLit) where
  ftvTree (VarPa _)        = return mempty
  ftvTree WldPa            = return mempty
  ftvTree (ConPa _ πs)     = ftvTree πs
  ftvTree (InjPa _ π)      = ftvTree π
  ftvTree (AnnPa π annot)  = ftvTree (π, annot)

instance Ftv (Term Empty) (Name, QLit) where
  ftvTree e0 = case e0 of
    AbsTm π e      → ftvTree (π, e)
    MatTm e bs     → ftvTree (e, bs)
    LetTm π e1 e2  → ftvTree (π, e1, e2)
    RecTm bs e2    → ftvTree (map sel2 bs, map sel3 bs, e2)
    VarTm _        → return mempty
    ConTm _ es     → ftvTree es
    LabTm _ _      → return mempty
    AppTm e1 e2    → ftvTree (e1, e2)
    AnnTm e annot  → ftvTree (e, annot)

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

unfoldRec ∷ Type a → ([Perhaps Name], Type a)
unfoldRec (RecTy pn t) = first (pn:) (unfoldRec t)
unfoldRec t            = ([], t)

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
    (pairs, extra1, extra2) = execWriter (loop row1 row2)
    (row1, ext1) = unfoldRow t10
    (row2, ext2) = unfoldRow t20
    loop []    rest2 = tell ([], [], rest2)
    loop rest1 []    = tell ([], rest1, [])
    loop (p1@(n1,_):rest1) (p2@(n2,_):rest2)
      | n1 < n2      = tell ([], [p1], [])      >> loop rest1 (p2:rest2)
      | n1 > n2      = tell ([], [], [p2])      >> loop (p1:rest1) rest2
      | otherwise    = tell ([(p1,p2)], [], []) >> loop rest1 rest2

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
--   * Type variables bound by μ appear in their scope, and there are
--     never multiple, immediately nested μs.
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
        rn ← newRef []
        let (qls, t) = unfoldQua u t0
            i        = length qls
            g'       = (depth + i, rn, False,) <$$> qls
        t' ← loop (depth + i) (g' ++ g) t
        nl ← readRef rn
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
      RecTy pn _            → do
        rn ← newRef []
        let (pns, t) = unfoldRec t0
            i        = length pns
            g'       = (depth + i, rn, True,) <$$> replicate i [A]
        t' ← loop (depth + i) (g' ++ g) t
        nl ← readRef rn
        return $
          if null nl
            then openTyN i (-1) [] t'
            else RecTy pn (openTyN (i - 1) (i - 1) [] t')
    --
    doVar depth g keep v0 = case v0 of
      BoundVar i j n
        | rib:_                    ← drop i g
        , (olddepth, r, rec, ql):_ ← drop j rib
                            → do
          s  ← readRef r
          if rec
            then do
              case List.findIndex ((== (depth - i)) . fst . fst) s of
                Just _  → return ()
                Nothing → writeRef r (s ++ [((depth - i, 0), (n, ql))])
              return (BoundVar (depth - olddepth) 0 n, True)
            else do
              j' ← case List.findIndex ((== (depth - i, j)) . fst) s of
                Just j' → return j'
                Nothing → do
                  when (keep ql) $
                    writeRef r (s ++ [((depth - i, j), (n, ql))])
                  return (length s)
              return (BoundVar (depth - olddepth) j' n, keep ql)
        | otherwise   → return (v0, True)
      FreeVar r       → return (FreeVar r,
                                keep (Map.findWithDefault maxBound r qm))
    --
    doQual depth g t = do
      let QExp q vs = pureQualifier t
      vqs' ← mapM (doVar depth g (not . (⊑ q))) (ordNub vs)
      let vs' = List.sort (map fst (filter snd vqs'))
      return (toQualifierType (QExp q vs'))

-- | To put a type annotation in standard form.
instance Standardizable Annot Name where
  standardizeQuals qm (Annot ns t) = Annot ns (standardizeQuals qm t)

-- | Parser monad with the type variables in state.
type P a = Parsec String [(String, QLit)] a

-- | A type class for generic parsing. It's especially useful for
--   building Read instances from Parsec parsers.
class Parsable a where
  genParser :: P a
  readsPrecFromParser :: ReadS a
  readsPrecFromParser =
    either (fail . show) return .
      runParser ((,) <$> genParser <*> getInput) [] ""

-- | A Parsec tokenizer
tok ∷ TokenParser st
tok  = makeTokenParser LanguageDef {
  commentStart = "{-",
  commentEnd   = "-}",
  commentLine  = "--",
  nestedComments = True,
  identStart   = noλμ $ upper <|> lower <|> oneOf "_",
  identLetter  = alphaNum <|> oneOf "_'′₀₁₂₃₄₅₆₇₈₉⁰¹²³⁴⁵⁶⁷⁸⁹",
  opStart      = empty,
  opLetter     = empty,
  reservedNames   = ["all", "ex", "let", "in", "rec", "and", "match", "with"],
  reservedOpNames = ["->", "→", "⊸", "∀", "∃", "μ", ".", "*", "×",
                     "\\", "λ", "=", ":", "|"],
  caseSensitive   = True
}
  -- 'λ' is not an identifier character, so that we can use it as
  -- a reserved operator. Otherwise, we'd need a space after it.
  where noλμ p = notFollowedBy (char 'λ' <|> char 'μ') *> p

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
findVar ∷ (Name, QLit) → [[(Name, QLit)]] → P (Var a)
findVar (name, ql) = loop 0 where
  loop !ix [] = do
    somes ← getState
    case lookupWithIndex name somes of
      Just (ql', jx) → finish ix jx ql'
      Nothing → do
        setState (somes ++ [(name, ql)])
        return (boundVar ix (length somes) name)
  loop !ix (rib:ribs) = case lookupWithIndex name rib of
    Just (ql', jx) → finish ix jx ql'
    Nothing        → loop (ix + 1) ribs
  finish ix jx ql' =
    if ql == ql'
      then return (boundVar ix jx name)
      else fail $ "Syntax error: Used both type variables '" ++
                  name ++ " and `" ++ name ++ " in the same expression"

-- | To parse an annotation
instance Parsable Annot where
  genParser  = withState [] $ do
    τ0    ← parseType
    somes ← getState
    let τ = openTy 0 (map (fvTy . fst) somes) τ0
    return (standardize (Annot somes τ))

-- | To parse a closed type.
instance Parsable (Type a) where
  genParser  = withState [] $ do
    t ← parseType
    somes ← getState
    case somes of
      [] → return t
      _  → fail ("Syntax error: Unbound type variables: " ++ show somes)

-- | To parse a (potentially open) type.  Adds the names of any free
--   variables encountered to the parse state in the order that their
--   seen, and binds them to an outermost rib.
parseType ∷ P (Type a)
parseType  = level0 []
  where
  level0 g = do
               (quants, tvss) ← unzip <$> parseQuantifiers
               body   ← level0 (reverse tvss ++ g)
               return (foldr2 QuaTy body quants (first Here <$$> tvss))
         <|> do
               reservedOp tok "μ" <|> reserved tok "rec"
               (tv, ql) ← parseTV
               dot tok
               body ← level0 ([(tv, ql)]:g)
               if contractiveTy body
                 then return (RecTy (Here tv) body)
                 else fail "Parser error: Recursive type not contractive"
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
  tyvarp g = join (findVar <$> parseTV <*> pure g)

-- To parse a sequence of quantifiers along with their bound variables.
parseQuantifiers ∷ P [(Quant, [(Name, QLit)])]
parseQuantifiers = many1 ((,) <$> quant <*> tvs) <* dot tok where
  quant   = AllQu <$ (reserved tok "all" <|> reservedOp tok "∀")
        <|> ExQu  <$ (reserved tok "ex"  <|> reservedOp tok "∃")
  tvs     = do
    idss ← sepBy1 tvGroup (comma tok)
    let ids = concatMap (map fst) idss
    when (ordNub ids /= ids) $
      fail "Syntax error: Repeated tyvar in quantifier group"
    return (concat idss)
  tvGroup = many1 parseTV

parseTV ∷ P (Name, QLit)
parseTV = flip (,) <$> option A (choice (parseQLitSigil <$> [U, A]))
                   <*> lowerIdentifier

parseQLitSigil ∷ QLit → P QLit
parseQLitSigil ql = ql <$ char (qLitSigil ql)

-- | To parse a qualifier literal
parseQLit ∷ P QLit
parseQLit = U <$ symbol tok "U"
        <|> A <$ symbol tok "A"

parseTypeArrow ∷ P (Var a) → P (Type a) → P (Type a → Type a → Type a)
parseTypeArrow tyvarp typep = flip arrTy <$> choice
  [ qlitexp U <$ reservedOp tok "→"
  , qlitexp U <$ reservedOp tok "->"
  , qlitexp A <$ reservedOp tok "⊸"
  , qlitexp A <$ try (symbol tok "-o")
  , between (try (symbol tok "-{")) (try (symbol tok "}>")) $
      pureQualifier <$> typep
  , between (symbol tok "-") (symbol tok ">") $ do
      QExp <$> option U parseQLit <*> many tyvarp
  ]

-- To parse a pattern. Produces the pattern and
-- the list of names bound by the patern.
parsePatt ∷ Int → P (Patt a)
parsePatt p = withState [] (level p) where
  level 0 = foldl' AnnPa <$> level 1
                         <*> many (reservedOp tok ":" *> genParser)
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
    -- On the next three lines A is arbitrary, but needs to match. Ugh!
    if (name, A) `elem` names
      then unexpected ("repeated variable in pattern: " ++ name)
      else putState (names++[(name, A)])
    return name

-- | To parse a closed term.
instance Parsable (Term a) where
  genParser  = parseTerm

-- | To parse a (potentially open) term. Free variables are handled as
--   in 'parseType'.
parseTerm ∷ P (Term a)
parseTerm = level0 where
  level0   = do
               reserved tok "match"
               e1 ← level0
               reserved tok "with"
               optional (reservedOp tok "|")
               bs ← flip sepBy1 (reservedOp tok "|") $ do
                 π ← parsePatt 0
                 parseArrow
                 e ← level0
                 return (π, e)
               return (MatTm e1 bs)
         <|> do
               reserved tok "let"
               choice
                [ reserved tok "rec" *>
                  (RecTm
                    <$> sepBy1
                          ((,,) <$> lowerIdentifier
                                <*> optional (colon tok *> genParser)
                                <*  reservedOp tok "="
                                <*> level0)
                          (reserved tok "and")
                    <*  reserved tok "in"
                    <*> level0)
                , LetTm
                    <$> parsePatt 0
                    <*  reservedOp tok "="
                    <*> level0
                    <*  reserved tok "in"
                    <*> level0
                ]
         <|> do
               reservedOp tok "\\" <|> reservedOp tok "λ"
               πs ← many1 (parsePatt 3)
               dot tok
               e ← level0
               return (foldr AbsTm e πs)
         <|> level1
  level1   = foldl' AnnTm <$> level2
                          <*> many (reservedOp tok ":" *> genParser)
  level2   = ConTm <$> upperIdentifier <*> many level3
         <|> chainl1 level3 (return AppTm)
  level3   = VarTm <$> lowerIdentifier
         <|> do
               con ← upperIdentifier
               return (ConTm con [])
         <|> LabTm <$> rowInjMark <*> upperIdentifier
         <|> parens tok tuple
  tuple    = chainl1 level0
                     ((\e1 e2 → ConTm "Pair" [e1, e2]) <$ comma tok)

rowInjMark ∷ P Bool
rowInjMark = (True  <$ char '`')
         <|> (False <$ char '#')

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
  | n0 < 0         = error "BUG! numberSubscript requires non-negative Int"
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
pprType ∷ Ppr a ⇒ Int → [[(Name, QLit)]] → Type a → Ppr.Doc
pprType  = loop where
  loop p g t0 = case t0 of
    QuaTy u e t           →
      let quant = case u of AllQu → "∀"; ExQu → "∃"
          (tvs0, qls) = unzip e
          tvs1        = freshNames tvs0 (fst <$> concat g) tvNames
          tvs         = zip tvs1 qls
       in parensIf (p > 0) $
            Ppr.hang
              (Ppr.text quant Ppr.<+>
                 Ppr.fsep (pprTV <$> tvs)
               Ppr.<> Ppr.char '.')
              2
              (loop 0 (tvs : g) t)
    VarTy (BoundVar ix jx (coerceOptional → n)) →
      case listNth jx <=< listNth ix $ g of
        Just tvql → pprTV tvql
        Nothing   → Ppr.text $ fromMaybe "?" n
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
    RecTy pn t          →
      let tv = freshName pn (fst <$> concat g) tvNames in
      parensIf (p > 0) $
        Ppr.hang
          (Ppr.text "μ `" Ppr.<> ppr tv Ppr.<> Ppr.char '.')
          2
          (loop 0 ([(tv, A)]:g) t)
  pprTV (name, ql) = Ppr.text (qLitSigil ql : name)

pprQExp ∷ Ppr a ⇒ Bool → Int → [[(Name, QLit)]] → Type a → Ppr.Doc
pprQExp arrowStyle p g t =
  case pureQualifier t of
    QExp U [] | arrowStyle → Ppr.char '→'
    QExp U [v]             → addArrow $ pprType 0 g (VarTy v)
    QExp U vs | arrowStyle → addArrow $ Ppr.fsep (pprType 0 g . VarTy <$> vs)
    QExp A _  → addArrow $ Ppr.char 'A'
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

instance Ppr (Patt a) where
  pprPrec = loop where
    loop _ (VarPa n)    = Ppr.text n
    loop _ WldPa        = Ppr.char '_'
    loop _ (ConPa c []) = Ppr.text c
    loop p (ConPa c πs) =
      parensIf (p > 1) $
        Ppr.sep (Ppr.text c : map (loop 2) πs)
    loop p (InjPa c π)  =
      parensIf (p > 1) $
        Ppr.char '`' Ppr.<> Ppr.text c Ppr.<+> loop 1 π
    loop p (AnnPa π annot) =
      parensIf (p > 0) $
        Ppr.hang (loop 1 π) 2 (Ppr.char ':' Ppr.<+> ppr annot)

-- | To pretty-print a closed term.
instance Ppr (Term a) where
  pprPrec = loop where
    loop p e0 = case e0 of
      AnnTm e annot       → parensIf (p > 1) $
        Ppr.fsep [ loop 1 e, Ppr.text ":", ppr annot ]
      AbsTm _ _           →
        let (πs, e)        = unfoldAbs e0
         in parensIf (p > 0) $
              Ppr.hang
                (Ppr.char 'λ'
                   Ppr.<> Ppr.fsep (map (pprPrec 3) πs)
                   Ppr.<> Ppr.char '.')
                2
                (loop 0 e)
      LetTm π e1 e2       →
        parensIf (p > 0) $
          Ppr.hang
            (Ppr.text "let" Ppr.<+> pprPrec 0 π Ppr.<+> Ppr.char '=' Ppr.<+>
             loop 0 e1)
            1
            (Ppr.text "in" Ppr.<+> loop 0 e2)
      MatTm e1 bs         →
        parensIf (p > 0) . Ppr.vcat $
          Ppr.text "match" Ppr.<+> loop 0 e1 Ppr.<+> Ppr.text "with" :
          [ Ppr.hang
              (Ppr.char '|' Ppr.<+> pprPrec 0 πi Ppr.<+> Ppr.char '→')
              4
              (loop 0 ei)
          | (πi, ei) ← bs ]
      RecTm bs e2         →
        parensIf (p > 0) $
          Ppr.text "let" Ppr.<+>
          Ppr.vcat
            [ Ppr.text kw Ppr.<+>
              Ppr.hang
                (Ppr.text ni Ppr.<+>
                 maybe Ppr.empty ((Ppr.char ':' Ppr.<+>) . ppr) mai
                 Ppr.<+> Ppr.char '=')
                2
                (loop 0 ei)
            | (ni,mai,ei) ← bs
            | kw          ← "rec" : repeat "and" ]
          Ppr.$$ Ppr.text " in" Ppr.<+> loop 0 e2
      VarTm name          → Ppr.text name
      ConTm name es       → parensIf (p > 2 && not (null es)) $
        Ppr.sep (Ppr.text name : map (loop 3) es)
      LabTm inj name     →
        Ppr.char (if inj then '`' else '#') Ppr.<> Ppr.text name
      AppTm e1 e2         → parensIf (p > 2) $
        Ppr.sep [loop 2 e1, loop 3 e2]

instance Show Annot where
  show = Ppr.render . ppr

instance Ppr a ⇒ Show (Type a) where
  showsPrec p t = showString (Ppr.render (pprPrec p t))

instance Ppr a ⇒ Show (Patt a) where
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
  , "∀ α. α"                    ==> allTy [A] (bv 0 0)
  , "∀ 'α. 'α"                  ==> allTy [U] (bv 0 0)
  , "∀ `α. `α"                  ==> allTy [A] (bv 0 0)
  , "∀ α β. α"                  ==> allTy [A,A] (bv 0 0)
  , "∀ α β. β"                  ==> allTy [A,A] (bv 0 1)
  , "∀ α, β. α"                 ==> allTy [A,A] (bv 0 0)
  , "∀ α 'β. 'β"                ==> allTy [A,U] (bv 0 1)
  , "∃ α. α"                    ==> exTy [A] (bv 0 0)
  , "∃ α β. α"                  ==> exTy [A,A] (bv 0 0)
  , "∃ α β. β"                  ==> exTy [A,A] (bv 0 1)
  , "∀ α β. C α → C β"
      ==> allTy [A,A] (c (bv 0 0) ↦ c (bv 0 1))
  , "∀ α. ∀ β. C α → C β → A"
      ==> allTy [A] (allTy [A] (c (bv 1 0) ↦ c (bv 0 0) ↦ a))
  , "∀ α. α → ∀ β. β → α"
      ==> allTy [A] (bv 0 0 ↦ allTy [A] (bv 0 0 ↦ bv 1 0))
  , "∃ α β. C α → C β"
      ==> exTy [A,A] (c (bv 0 0) ↦ c (bv 0 1))
  , "∃ α. ∃ β. C α → C β → A"
      ==> exTy [A] (exTy [A] (c (bv 1 0) ↦ c (bv 0 0) ↦ a))
  , "∃ α. α → ∃ β. β → α"
      ==> exTy [A] (bv 0 0 ↦ exTy [A] (bv 0 0 ↦ bv 1 0))
  , "∃ α ∀ β. C α → C β → A"
      ==> exTy [A] (allTy [A] (c (bv 1 0) ↦ c (bv 0 0) ↦ a))
  , "∃ α. α → ∀ β. β → α"
      ==> exTy [A] (bv 0 0 ↦ allTy [A] (bv 0 0 ↦ bv 1 0))
  , "[ A : A ]"
      ==> RowTy "A" a endTy
  , "[ A : A | B : B ]"
      ==> RowTy "A" a (RowTy "B" b endTy)
  , "[ A : A | B : B | A : C B ]"
      ==> RowTy "A" a (RowTy "B" b (RowTy "A" (c b) endTy))
  , "∀ α. [ A : A | B : B | α ]"
      ==> allTy [A] (RowTy "A" a (RowTy "B" b (bv 0 0)))
  , "∀ α β γ. [ A : α | B : β | γ ]"
      ==> allTy [A,A,A] (RowTy "A" (bv 0 0) (RowTy "B" (bv 0 1) (bv 0 2)))
  , "∀ β. μ α. [ A : α | β ]"
      ==> allTy [A] (RecTy Nope (RowTy "A" (bv 0 0) (bv 1 0)))
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
  , "∀ α. [ A : A | B : B | α ]"
      <==>* "∀ α. [ A : A | B : B | α ]"
  , "μ α. [ A : α ]"
      <==>* "μ α. [ A : α ]"
  , "μ α. [ A : M ]"
      <==>* "[ A : M ]"
  , "μ α. [ A : α | B : α ]"
      <==>* "μ α. [ A : α | B : α ]"
  , "μ α. μ β. [ A : α | B : α ]"
      <==>* "μ α. [ A : α | B : α ]"
  , "μ α. μ β. [ A : α | B : β ]"
      <==>* "μ α. [ A : α | B : α ]"
  , "μ β. μ α. [ A : α | B : β ]"
      <==>* "μ α. [ A : α | B : α ]"
  , "μ α. μ β. μ γ. [ A : α | B : β ]"
      <==>* "μ α. [ A : α | B : α ]"
  , let str = "∀ α. α → ∀ β. β → α" in
    T.assertBool str
      ((standardize (read str) ∷ Type Empty) ==
       allTy [A] (VarTy (boundVar 0 0 "α") ↦
                  allTy [A] (VarTy (boundVar 0 0 "β") ↦
                             VarTy (boundVar 1 0 "α"))))
  ]

{-
tryParsePprPatt ∷ String → IO ()
tryParsePprPatt s =
  case runParser (parsePatt 0 <* eof) [] "" s of
    Left e              → print e
    Right (patt, names) → print (pprPatt 0 names (patt ∷ Patt Empty))

-}

