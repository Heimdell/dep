
module Phase.Runtime.Value where

open import Prelude

open import Phase.Scoped.Contexts
open import Phase.Scoped.Patterns
open import Name

{-
  NbE part is quite standard, for some exceptions.

  I have no idea if this is correct.
-}

data   Value (Γ : Ctx) : Set
data   Stuck (Γ : Ctx) : Set
record Match (Γ : Ctx) : Set

data   Split (Δ Γ : Ctx) : Set
record Case  (Δ Γ : Ctx) : Set where
  inductive
  constructor %Case
  field
    {γ} : Ctx
    pat : Pat γ
    body : Split Δ (γ + Γ)
open Case public

data Split Δ Γ where
  %Run   : Value (Δ + Γ)   → Split Δ Γ
  %Split : List (Case Δ Γ) → Split Δ Γ

data Tele (Γ : Ctx) : Ctx → Set where
  _≔_   : (n : Name) (ty : Value Γ) → Tele Γ ([ n ] ∷ [])
  _∶_∷_ : (n : Name) (ty : Value Γ) (rest : Tele ([ n ] ∷ Γ) Δ) → Tele Γ ([ n ] ∷ Δ)

data Newtype (Γ : Ctx) : Set where
  %Data %Codata : Name → List (Name × Value Γ) → Newtype Γ

record Type (Γ : Ctx) : Set where
  inductive
  constructor %Type
  field
    {γ}  : Ctx
    tele : Tele Γ γ
    type : Newtype (γ + Γ)
open Type public

{-
  Normal form.

  `%Recur` (the recursive function body) is here, because it is not, in fact, stuck.
-}
data Value Γ where
  %Stuck   : Stuck Γ → Value Γ
  %Ctor    : Name → List (Value Γ) → Value Γ
  %Field   : Name → Value Γ
  %Lam     : List (Match Γ) → Value Γ
  %Record  : List (Name × Value Γ) → Value Γ
  %U       : Value Γ
  %Erased  : Value Γ
  %Pi      : (n : Name) → Value Γ → Value ([ n ] ∷ Γ) → Value Γ
  %Type    : (t : Type Γ) → Value Γ
  %Newtype : (n : Newtype Γ) → Value Γ
  %Recur   :
    (n      : Maybe Name)
    (body   : Split Δ Γ)
    (recure : Vec (Split Δ Γ) (length Δ))
            → Value Γ

{-
  `%Match` constructor is `Stuck` with 2 `Value`s because
  pattern `%Suc (%Suc (%Var "n"))`
  can stuck on `%Suc (%Var "m" _)`
  and nether of them are `Stuck`.

  I do not want to make pattern matching more complex than it already is.
-}
data Stuck Γ where
  %Var   : (n : Name) → [ n ] ∈ Γ → Stuck Γ
  %App   : (f : Stuck Γ) (x : Value Γ) → Stuck Γ
  %Match : (f : Value Γ) (x : Value Γ) → Stuck Γ
  %Get   : (f : Stuck Γ) (n : Name)    → Stuck Γ

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
  show-value : PP (Value   Γ)
  show-stuck : PP (Stuck   Γ)
  show-match : PP (Match   Γ)
  show-split : PP (Split Δ Γ)
  show-case  : PP (Case  Δ Γ)
  show-nty   : PP (Newtype Γ)

show-nty .pp = λ where
  (%Data   n _) → use⟨ [ n ] ⟩
  (%Codata n _) → use⟨ [ n ] ⟩

{-# TERMINATING #-}
show-case .pp (%Case pat body) = hang (pp pat ◈ MAGENTA (text "⇒")) (pp body)

show-split .pp = λ where
  (%Run    plain)  → pp plain
  (%Split  cases)  → vcat (pp <$> cases)

value-vec→string : (Δ : Ctx) → Vec (Value Γ) (length Δ) → List Doc
value-vec→string [] [] = []
value-vec→string  (n ∷ Δ) (expr ∷ decls) =
  hang (text n ◈ `=`) (pp expr) ∷ value-vec→string Δ decls

show-value .pp = λ where
  (%Stuck  stuck)          → pp stuck
  (%Ctor   ctor [])        → ctor⟨ [ ctor ] ⟩
  (%Field  name)           → field⟨ [ name ] ⟩
  (%Ctor   ctor exprs)     → `⟨` sep (ctor⟨ [ ctor ] ⟩ ∷ (pp <$> exprs)) `⟩`
  (%Record fields)         → `⟪` vcat ((λ (n , v) → hang field⟨ [ n ] ⟩ (pp v)) <$> fields) `⟫`
  (%Lam    alts)           → vcat (pp <$> alts)
  (%Recur  (just n) _ _)   → rec⟨ [ n ] ⟩
  (%Recur  nothing case _) → pp case
  (%Type   ty)             → pp (ty .type)
  (%Newtype ty)            → pp ty
  (%U)                     → `Type`
  (%Erased)                → `erased`
  (%Pi     n dom cod)      → `[` text [ n ] + `:` ◈ pp dom `]` ◈ pp cod

call-spine  : Stuck Γ → List Doc
call-spine′ : Value Γ → List Doc
call-spine = λ where
  (%App   f x) → call-spine  f + (pp x ∷ [])
  (%Match f x) → call-spine′ f + (pp x ∷ [])
  (%Get   b n) → call-spine  b + (field⟨ [ n ] ⟩ ∷ [])
  other        → pp other ∷ []

call-spine′ = λ where
  (%Stuck s) → call-spine s
  other      → pp other ∷ []

show-stuck .pp = λ where
  (%Var   n var) → use⟨ [ n ] ⟩
  p              → `⟨` sep (call-spine p) `⟩`

show-match .pp (%Match pat body) = hang (pp pat ◈ `⇒`) (pp body)
