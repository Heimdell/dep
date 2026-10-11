
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

data Newtype : Set where
  %Data %Codata : List (Name × Expr) → Newtype

record Type : Set where
  constructor %Type
  field
    pos     : Pos
    params  : List (Name × Expr)
    indices : Expr
    newtype : Newtype
open Type public

data Stmts : Set where
  %Do    : Expr → Stmts
  %Let   : (n : Name) (ty value : Expr) → Stmts → Stmts

  %Rec   :
    (binds : List (Name × Expr × Expr))
    (cont  : Stmts)
           → Stmts

  %Let-type   : (n : Name) (value : Type) → Stmts → Stmts

  %Rec-type   :
    (binds : List (Name × Type))
    (cont  : Stmts)
           → Stmts

open import Pretty
open import Pretty.Syntax

instance
  {-# TERMINATING #-}
  show-expr  : PP Expr
  show-alt   : PP Alt
  show-pat   : PP Pat

call-spine : Expr → List Doc
call-spine = λ where
  -- (%App _ (%Field x) f) → pp x ∷ call-spine f
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
show-field (name , value) = hang (field⟨ [ name ] ⟩ ◈ `=`) (pp value)

sep′ : List Doc → Doc
sep′ = λ where
  []       → text ""
  (x ∷ xs) → hang x (sep′ xs)

instance
  show-expr .pp = λ where
    (%Var  n)                 → use⟨ [ n ] ⟩
    (%Ctor ctor)              → ctor⟨ [ ctor ] ⟩
    (%Field name)             → field⟨ [ name ] ⟩
    (%Record _ fields)        → `⟪` vcat (show-field <$> fields) `⟫`
    p@(%App _ f x)             → `⟨` hang (pp f) (pp x) `⟩`
    (%Lam _ alts)              → `⟪` vcat (pp <$> alts) `⟫`
    (%U)                      → `Type`
    (%Pi   n dom cod)         → `[` decl⟨ [ n ] ⟩ + `:` ◈ pp dom `]` ◈ pp cod

instance
  show-newtype : PP Newtype
  show-newtype .pp = λ where
    (%Data   dat) → hang `data`   (vcat ((λ ((n , e)) → pp n + `:` ◈ pp e) <$> dat))
    (%Codata cod) → hang `codata` (vcat ((λ ((n , e)) → pp n + `:` ◈ pp e) <$> cod))

  show-type : PP Type
  show-type .pp (%Type pos params indices newtype) =
    hang (sep ((λ ((n , e)) → pp n + `:` ◈ pp e) <$> params) ◈ `:` ◈ pp indices) (pp newtype)

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
    (%Let-type n value expr) → vcat ( `let`
                                     ∷ nest (hang (decl⟨ [ n ] ⟩ ◈ `=`) (pp value))
                                     ∷ empty
                                     ∷ pp expr
                                     ∷ []
                                     )
    (%Rec-type  binds expr)        → vcat ( `let-rec`
                                     ∷ nest (vcat ((λ ((n , ty)) → hang (decl⟨ [ n ] ⟩ ◈ `=`) (pp ty)) <$> binds))
                                     ∷ empty
                                     ∷ pp expr
                                     ∷ []
                                     )
