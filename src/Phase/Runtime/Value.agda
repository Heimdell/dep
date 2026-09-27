
module Phase.Runtime.Value where

open import Prelude

open import Phase.Scoped.Contexts
open import Phase.Scoped.Case-splits
open import Phase.Scoped.Patterns

{-
  NbE part is quite standard, for some exceptions.

  I have no idea if this is correct.
-}

data   Value (Γ : Ctx) : Set
data   Stuck (Γ : Ctx) : Set
record Match (Γ : Ctx) : Set

{-
  Normal form.

  `%Recur` (the recursive function body) is here, because it is not, in fact, stuck.
-}
data Value Γ where
  %Stuck : Stuck Γ → Value Γ
  %Ctor  : String → List (Value Γ) → Value Γ
  %Lam   : List (Match Γ) → Value Γ
  %Recur :
    (n      : Maybe Name)
    (body   : Case Value Δ Γ)
    (recure : Vec (Case Value Δ Γ) (length Δ))
            → Value Γ

{-
  `%Match` constructor is `Stuck` with 2 `Value`s because
  pattern `%Suc (%Suc (%Var "n"))`
  can stuck on `%Suc (%Var "m" _)`
  and nether of them are `Stuck`.

  I do not want to make pattern matching more complex than it already is.
-}
data Stuck Γ where
  %Var   : n ∈ Γ → Stuck Γ
  %App   : (f : Stuck Γ) (x : Value Γ) → Stuck Γ
  %Match : (f : Value Γ) (x : Value Γ) → Stuck Γ

{-
  Normal, non-recursive lambda's pattern match in a branch.

  > \(Suc n) -> Suc Zero,
  >   Zero   -> Zero
-}
record Match Γ where
  inductive
  constructor %Match
  field
    {δ}  : Ctx            -- vars to be captured
    pat  : Pat δ          -- pattern to match against
    body : Value (δ + Γ)  -- body of the alt
open Match public

{-
  Various printing. Skip till `M` is defined.
-}
instance
  {-# TERMINATING #-}
  show-value : Show (Value Γ)
  show-stuck : Show (Stuck Γ)
  show-match : Show (Match Γ)

value-vec→string : (Δ : Ctx) → Vec (Value Γ) (length Δ) → String
value-vec→string [] [] = 𝟘
value-vec→string  (n ∷ Δ) (expr ∷ decls) = n + ": " + show expr + "; " + value-vec→string Δ decls

show-value .show = λ where
  (%Stuck stuck) → show stuck + "ₛ"
  (%Ctor ctor exprs) → "(" + fold-l _◈_ ctor (show <$> exprs) + ")"
  (%Lam alts)    → "{" + intercalate " | " (show <$> alts) + "}"
  (%Recur (just n) _ _) → "⋯" + n
  (%Recur nothing case _) → show case

show-stuck .show = λ where
  (%Var   {n} var) → n
  (%App       f x) → "(" + show f + " " + show x + ")"
  (%Match     f x) → "[" + show f + " " + show x + "]"

show-match .show (%Match pat body) = show pat + " ⇒ " + show body
