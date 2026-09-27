
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

  %Let  : Expr Γ → Expr (n ∷ Γ) → Expr Γ

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

instance
  {-# TERMINATING #-}
  show-expr : Show (Expr Γ)
  show-alt : Show (Alt Γ)
  show-alt .show (%Alt pat body) = show pat + " ⇒ " + show body

expr-vec→string : (Δ : Ctx) → Vec (Case Expr Ξ Γ) (length Δ) → String
expr-vec→string [] [] = 𝟘
expr-vec→string  (n ∷ Δ) (expr ∷ decls) = n + ": " + show expr + "; " + expr-vec→string Δ decls

instance
  show-expr .show = λ where
    (%Var n _)            → n
    (%Ctor ctor exprs)    → "(" + fold-l _◈_ ctor (show <$> exprs) + ")"
    (%App f x)            → "(" + show f + " " + show x + ")"
    (%Lam alts)           → "{" + intercalate ", " (show <$> alts) + "}"
    (%Rec {Δ} δ expr)     → "let " + expr-vec→string Δ δ + "in " + show expr
    (%Let {n} value expr) → "let " + n + " = " + show value + " in " + show expr
