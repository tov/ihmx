{-# LANGUAGE
      DeriveFunctor,
      FlexibleInstances,
      FunctionalDependencies,
      MultiParamTypeClasses,
      TypeSynonymInstances,
      UnicodeSyntax
      #-}
module Env (
  Δ,
  Γ, rankΓ, emptyΓ, bumpΓ, cleanΓ, MakeEnvMap(..), (&+&), (&.&)
) where

import Util
import Syntax
import qualified Rank
import Ppr

import Data.Map as M
import qualified Text.PrettyPrint as Ppr

type Δ tv = Map Name tv

data Γ tv
  = Γ {
      rankΓ ∷ !Rank.Rank,
      mapΓ  ∷ !(Map Name (Type tv))
    }
  deriving (Show, Functor)

emptyΓ ∷ Γ tv
emptyΓ = Γ Rank.zero M.empty

cleanΓ ∷ Γ tv → Γ tv
cleanΓ γ = γ { mapΓ = unγ0 (mapΓ γ) }

infix  3 &:&
infixl 2 &+&

class MakeEnvMap n tv t | n tv → t where
  (&:&) ∷ n → t → Map Name (Type tv)

instance MakeEnvMap Name tv (Type tv) where
  (&:&) = singleton

instance MakeEnvMap [Name] tv [Type tv] where
  (&:&) = fromList <$$> zip

instance MakeEnvMap (Patt a) tv [Type tv] where
  (&:&) = (&:&) . pattBv

(&+&) ∷ Γ tv → Map Name (Type tv) → Γ tv
γ &+& m2 = γ { mapΓ = m2 `M.union` mapΓ γ } -- left biased union

bumpΓ ∷ Γ tv → Γ tv
bumpΓ γ = γ { rankΓ = Rank.inc (rankΓ γ) }

(&.&) ∷ Monad m ⇒ Γ tv → Name → m (Type tv)
Γ { mapΓ = m } &.& n = case M.lookup n m of
  Just t  → return t
  Nothing → fail $ "Unbound variable ‘" ++ n ++ "’"

instance Ftv tv tv ⇒ Ftv (Γ tv) tv where
  ftvTree = ftvTree . mapΓ

instance Ppr tv ⇒ Ppr (Γ tv) where
  pprPrec p γ = parensIf (p > 10) $
    Ppr.char 'Γ' Ppr.<+> ppr (rankΓ γ) Ppr.<+> ppr (mapΓ (cleanΓ γ))

