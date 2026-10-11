
module Phase.Raw.Terms where

open import Prelude
open import Name
open import Position

record Alt  : Set
data   Expr : Set

{-
  Expression of the modelled language.

  Let-rec bindings are encoded case expressions.
  Their mutual references are linked through variable-holes,
  thus their import Phase.Scoped.Contexts are `Δ Γ`, and in `%Run` ctor we have `Expr (Δ + Γ)`.

  This makes mutually-recursive substitution effectively delayed.
-}
data Expr where
  %Var   : (n : Name) → Expr
  %Ctor  : Name → Expr
  %Field : Name → Expr
  %App   : (p : Pos) (f x : Expr)  → Expr
  %Lam   : (p : Pos) (alts : List Alt) → Expr
  %Record : (p : Pos) → (fields : List (Name × Expr)) → Expr

  %U     : Expr
  %Pi    : (n : Name) (dom cod : Expr) → Expr

  %Let   : (n : Name) (ty value k : Expr) → Expr

  -- let rec
  %Rec   :
    (binds : List (Name × Expr × Expr))
    (cont  : Expr)
           → Expr

data Pat : Set where
  %Var  : Name → Pat
  %Ctor : Name → List Pat → Pat

record Alt where
  inductive
  constructor %Alt
  field
    pat  : Pat
    body : Expr
open Alt

open import Pretty
open import Pretty.Syntax

instance
  {-# TERMINATING #-}
  show-expr  : PP Expr
  show-alt   : PP Alt
  show-pat   : PP Pat
--   show-split : PP (Split Δ Γ)
--   show-case  : PP (Case  Δ Γ)

call-spine : Expr → List Doc
call-spine = λ where
  (%App _ f x) → call-spine f + (pp x ∷ [])
  other        → pp other ∷ []

show-alt .pp (%Alt pat body) = hang (pp pat ◈ `⇒`) (sep (call-spine body))

{-# TERMINATING #-}
show-pat .pp = λ where
  (%Var  name)      → decl⟨ [ name ] ⟩
  (%Ctor name args) → `⟨` hang ctor⟨ [ name ] ⟩ (sep (pp <$> args))  `⟩`

expr-vec→string : Name × Expr × Expr → Doc
expr-vec→string (name , type , value) =
  hang (hang decl⟨ [ name ] ⟩ (`:` ◈ pp type) ◈ `=`) (pp value)

show-field : Name × Expr → Doc
show-field (name , value) = hang field⟨ [ name ] ⟩ (pp value)

instance
  show-expr .pp = λ where
    (%Var  n)                 → use⟨ [ n ] ⟩
    (%Ctor ctor)              → ctor⟨ [ ctor ] ⟩
    (%Field name)             → field⟨ [ name ] ⟩
    (%Record _ fields)        → `⟪` vcat (show-field <$> fields) `⟫`
    p@(%App _ f x)             → `⟨` sep (call-spine p) `⟩`
    (%Lam _ alts)              → vcat (pp <$> alts)
    (%Let n ty value expr) → vcat ( `let`
                                     ∷ nest (hang (decl⟨ [ n ] ⟩ ◈ `:`) (pp ty))
                                     ∷ nest (hang (decl⟨ [ n ] ⟩ ◈ `=`) (pp value))
                                     ∷ empty
                                     ∷ pp expr
                                     ∷ []
                                     )
    (%U)                      → `Type`
    (%Pi   n dom cod)         → `[` decl⟨ [ n ] ⟩ + `:` ◈ pp dom `]` ◈ pp cod
    (%Rec  binds expr)        → vcat ( `let-rec`
                                     ∷ nest (vcat (expr-vec→string <$> binds))
                                     ∷ empty
                                     ∷ pp expr
                                     ∷ []
                                     )
