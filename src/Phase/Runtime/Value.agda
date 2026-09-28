
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
  %U     : Value Γ
  %Pi    : (n : Name) → Value Γ → Value (n ∷ Γ) → Value Γ
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

open import Pretty
open import Pretty.Syntax

{-
  Various printing. Skip till `M` is defined.
-}
instance
  {-# TERMINATING #-}
  show-value : PP (Value Γ)
  show-stuck : PP (Stuck Γ)
  show-match : PP (Match Γ)

value-vec→string : (Δ : Ctx) → Vec (Value Γ) (length Δ) → List Doc
value-vec→string [] [] = []
value-vec→string  (n ∷ Δ) (expr ∷ decls) =
  hang (text n ◈ `=`) (pp expr) ∷ value-vec→string Δ decls

show-value .pp = λ where
  (%Stuck stuck)          → pp stuck + `ₛ`
  (%Ctor  ctor exprs)     → `⟨` fold-l _◈_ (green (text ctor)) (pp <$> exprs) `⟩`
  (%Lam   alts)           → vcat (pp <$> alts)
  (%Recur (just n) _ _)   → rec⟨ n ⟩
  (%Recur nothing case _) → pp case
  (%U)                    → `Type`
  (%Pi    n dom cod)      → `[` text n + `:` ◈ pp dom `]` ◈ pp cod

show-stuck .pp = λ where
  (%Var   {n} var) → use⟨ n ⟩
  (%App       f x) → `⟨` (pp f ◈ pp x) `⟩`
  (%Match     f x) → `[` (pp f ◈ pp x) `]`

show-match .pp (%Match pat body) = hang (pp pat ◈ `⇒`) (pp body)
