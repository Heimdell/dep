
module Phase.Scoped.Contexts where

open import Prelude

Ctx : Set
Ctx = List String

variable
  Γ Δ Θ Ξ : Ctx
  n m     : String
