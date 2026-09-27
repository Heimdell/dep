module Phase.Scoped.Patterns where

open import Prelude
open import Phase.Scoped.Contexts

{-
  We only have 2 ctors to match against - (Suc n) and Zero.
-}
data Pat : Ctx → Set

data Pats : Ctx → Set where
  []  : Pats []
  _∷_ : Pat Δ → Pats Γ → Pats (Γ + Δ)

data Pat where
  %Var  : (n : Name)               → Pat (n ∷ [])  -- variable
  %Ctor : (ctor : String) → Pats Δ → Pat Δ         -- (Suc <pat>)

instance
  {-# TERMINATING #-}
  show-pat  : Show (Pat  Δ)
  show-pats : Show (Pats Δ)

  show-pat .show = λ where
    (%Var  n)         → n
    (%Ctor ctor pats) → "(" + ctor + show pats + ")"

  show-pats .show = λ where
    [] → ""
    (pat ∷ pats) → " " + show pat + show pats
