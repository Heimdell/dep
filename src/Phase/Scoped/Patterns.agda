module Phase.Scoped.Patterns where

open import Prelude
open import Phase.Scoped.Contexts

{-
  We only have 2 ctors to match against - (Suc n) and Zero.
-}
data Pat : Ctx → Set where
  %Var  : (n : String) → Pat (n ∷ [])  -- variable
  %Suc  : Pat Δ        → Pat Δ         -- (Suc <pat>)
  %Zero :                Pat []        -- Zero

instance
  {-# TERMINATING #-}
  show-pat  : Show (Pat Δ)
  show-pat .show = λ where
    (%Var n)   → n
    (%Suc pat) → "(suc " + show pat + ")"
    (%Zero)    → "0"
