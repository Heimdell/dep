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

open import Pretty
open import Pretty.Syntax

instance
  {-# TERMINATING #-}
  show-pat  : PP (Pat  Δ)

show-pats : Pats Δ → List Doc

show-pat .pp = λ where
  (%Var  n)         → decl⟨ n ⟩
  (%Ctor ctor pats) → `⟨` (sep (ctor⟨ ctor ⟩ ∷ show-pats pats)) `⟩`

show-pats = λ where
  []           → []
  (pat ∷ pats) → pp pat ∷ show-pats pats
