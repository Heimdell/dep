
module Phase.Raw.Terms where

open import Prelude
open import Name
open import Position

record Alt  : Set
data   Expr : Set

data Expr where
  %Var   : (n : Name) → Expr
  %Ctor  : Name → Expr
  %Field : Name → Expr
  %App   : (p : Pos) (f x : Expr)  → Expr
  %Lam   : (p : Pos) (alts : List Alt) → Expr
  %Record : (p : Pos) → (fields : List (Name × Expr)) → Expr

  %U     : Expr
  %Pi    : (n : Name) (dom cod : Expr) → Expr

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

data Stmts : Set where
  %Do    : Expr → Stmts
  %Let   : (n : Name) (ty value : Expr) → Stmts → Stmts

  -- let rec
  %Rec   :
    (binds : List (Name × Expr × Expr))
    (cont  : Stmts)
           → Stmts

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
    (%U)                      → `Type`
    (%Pi   n dom cod)         → `[` decl⟨ [ n ] ⟩ + `:` ◈ pp dom `]` ◈ pp cod
instance
  show-stmt : PP Stmts
  show-stmt .pp = λ where
    (%Do expr) → pp expr
    (%Let n ty value expr) → vcat ( `let`
                                     ∷ nest (hang (decl⟨ [ n ] ⟩ ◈ `:`) (pp ty))
                                     ∷ nest (hang (decl⟨ [ n ] ⟩ ◈ `=`) (pp value))
                                     ∷ empty
                                     ∷ pp expr
                                     ∷ []
                                     )
    (%Rec  binds expr)        → vcat ( `let-rec`
                                     ∷ nest (vcat (expr-vec→string <$> binds))
                                     ∷ empty
                                     ∷ pp expr
                                     ∷ []
                                     )
