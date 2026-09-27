
module Phase.Scoped.Contexts where

open import Prelude

Name : Set
Name = String

Ctx : Set
Ctx = List Name

variable
  Γ Δ Θ Ξ : Ctx
  n       : Name
