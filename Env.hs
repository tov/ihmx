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
  Γ, rankΓ, emptyΓ, bumpΓ, MakeEnvMap(..), (&+&), (&.&)
) where

import Util
import Syntax

import Data.Map as M

type Δ tv = Map Name (Type tv)

data Γ tv
  = Γ {
      rankΓ ∷ !Int,
      mapΓ  ∷ !(Map Name (Type tv))
    }
  deriving (Show, Functor)

emptyΓ ∷ Γ tv
emptyΓ = Γ 0 M.empty

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
bumpΓ γ = γ { rankΓ = rankΓ γ + 1 }

(&.&) ∷ Monad m ⇒ Γ tv → Name → m (Type tv)
Γ { mapΓ = m } &.& n = case M.lookup n m of
  Just t  → return t
  Nothing → fail $ "Unbound variable ‘" ++ n ++ "’"

instance Tv tv ⇒ Ftv (Γ tv) tv where
  ftvTree = ftvTree . mapΓ
