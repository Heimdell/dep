
module Phase.Scoped.Terms where

open import Prelude
open import Phase.Scoped.Contexts
open import Phase.Scoped.Case-splits
open import Phase.Scoped.Patterns

record Alt (Γ : Ctx) : Set

{-
  Expression of the modelled language.

  Let-rec bindings are encoded case expressions.
  Their mutual references are linked through variable-holes,
  thus their import Phase.Scoped.Contexts are `Δ Γ`, and in `%Run` ctor we have `Expr (Δ + Γ)`.

  This makes mutually-recursive substitution effectively delayed.
-}
data Expr (Γ : Ctx) : Set where
  %Var  : (n : Name) → n ∈ Γ → Expr Γ
  %Ctor : String → List (Expr Γ) → Expr Γ
  %App  : (f x : Expr Γ) → Expr Γ
  %Lam  : List (Alt Γ) → Expr Γ

  %U    : Expr Γ
  %Pi   : (n : Name) → Expr Γ → Expr (n ∷ Γ) → Expr Γ

  %Let  : (ty value : Expr Γ) → Expr (n ∷ Γ) → Expr Γ

  -- let rec
  %Rec  :
    (binds : Vec (Case Expr Δ Γ) (length Δ))
    (cont  : Expr (Δ + Γ))
           → Expr Γ

record Alt Γ where
  inductive
  constructor %Alt
  field
    {δ}  : Ctx           -- vars to be captured
    pat  : Pat   δ       -- pattern to match against
    body : Expr (δ + Γ)  -- body of the alt
open Alt

open import Pretty
open import Pretty.Syntax

instance
  {-# TERMINATING #-}
  show-expr : PP (Expr Γ)
  show-alt : PP (Alt Γ)
  show-alt .pp (%Alt pat body) = hang (pp pat ◈ `⇒`) (pp body)

expr-vec→string : (Δ : Ctx) → Vec (Case Expr Ξ Γ) (length Δ) → List Doc
expr-vec→string [] [] = []
expr-vec→string  (n ∷ Δ) (expr ∷ decls) =
  hang (decl⟨ n ⟩ ◈ `=`) (pp expr) ∷ expr-vec→string Δ decls

instance
  show-expr .pp = λ where
    (%Var  n _)               → use⟨ n ⟩
    (%Ctor ctor exprs)        → `⟨` sep (ctor⟨ ctor ⟩ ∷ (pp <$> exprs)) `⟩`
    (%App  f x)               → `⟨` (pp f ◈ pp x) `⟩`
    (%Lam  alts)              → vcat (pp <$> alts)
    (%Let  {n} ty value expr) → vcat ( `let`
                                     ∷ nest (hang (decl⟨ n ⟩ ◈ `:`) (pp ty))
                                     ∷ nest (hang (decl⟨ n ⟩ ◈ `=`) (pp value))
                                     ∷ pp expr
                                     ∷ []
                                     )
    (%U)                      → `Type`
    (%Pi   n dom cod)         → `[` text n + `:` ◈ pp dom `]` ◈ pp cod
    (%Rec  {Δ} δ expr)        → vcat ( `let-rec`
                                     ∷ nest (vcat (expr-vec→string Δ δ))
                                     ∷ pp expr
                                     ∷ []
                                     )
