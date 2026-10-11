
module Phase.Scoped.Terms where

open import Prelude
open import Phase.Scoped.Contexts
open import Phase.Scoped.Patterns
open import Name
open import Position

record Alt  (Γ : Ctx) : Set
data   Expr (Γ : Ctx) : Set
{-
  Split-tree for argument list.

  The idea is that we match arguments until we destructure or run out of parameters.

  Each spine in the tree ends either right after destructiring pattern, or when
  definition ran out of params.
-}
data Split (Δ Γ : Ctx) : Set

data Tele (Γ : Ctx) : Ctx → Set where
  []    : Tele Γ []
  _∶_∷_ : (n : Name) (ty : Expr Γ) (rest : Tele ([ n ] ∷ Γ) Δ) → Tele Γ ([ n ] ∷ Δ)

data RecTele (Γ : Ctx) : Set where
  []  : RecTele Γ
  _∶_∷_ : (f : Name) (ty : Expr Γ) (rest : RecTele ([ f ] ∷ Γ)) → RecTele Γ

data Newtype (Γ : Ctx) : Set where
  %Data   : Name → List (Name × Expr Γ) → Newtype Γ
  %Codata : Name → RecTele Γ            → Newtype Γ

record Type (Γ : Ctx) : Set where
  inductive
  constructor %Type
  field
    {δ}     : Ctx
    tele    : Tele Γ δ
    newtype : Newtype (δ + Γ)
open Type public

{-
  Attempt to match against pattern `pat`.
-}
record Case (Δ Γ : Ctx) : Set where
  inductive
  constructor %Case
  field
    {δ}  : Ctx               -- vars to be captured
    pat  : Pat δ             -- pattern to match against
    tree : Split Δ (δ + Γ)  -- remainder of the case-tree
open Case

data Split Δ Γ where
  %Run    : Expr (Δ + Γ)                   → Split Δ Γ  -- tree is done; you can apply it as normal
  %Split  : List (Case Δ Γ)                → Split Δ Γ  -- we still haven't matched enough of the params
  -- %Record : List (Name × Split Δ Γ)        → Split Δ Γ
  -- %With   : Expr (Δ + Γ) → List (Case Δ Γ) → Split Δ Γ

{-
  Expression of the modelled language.

  Let-rec bindings are encoded case expressions.
  Their mutual references are linked through variable-holes,
  thus their import Phase.Scoped.Contexts are `Δ Γ`, and in `%Run` ctor we have `Expr (Δ + Γ)`.

  This makes mutually-recursive substitution effectively delayed.
-}
data Expr Γ where
  %Var    : (n : Name) → [ n ] ∈ Γ → Expr Γ
  %Ctor   : Name → Expr Γ
  %Field  : Name → Expr Γ
  %App    : (f x : Expr Γ) → Expr Γ
  %Lam    : List (Alt Γ) → Expr Γ
  %Record : List (Name × Expr Γ) → Expr Γ
  %U      : Expr Γ
  %Type   : Type Γ → Expr Γ
  %Pi     : (n : Name) → Expr Γ → Expr ([ n ] ∷ Γ) → Expr Γ

record Alt Γ where
  inductive
  constructor %Alt
  field
    {δ}  : Ctx           -- vars to be captured
    pat  : Pat   δ       -- pattern to match against
    body : Expr (δ + Γ)  -- body of the alt
open Alt

data Stmts (Γ : Ctx) : Set where
  %Do  : Expr Γ → Stmts Γ
  %Let : (n : Name) (ty : Expr Γ) (val : Expr Γ) → Stmts ([ n ] ∷ Γ) → Stmts Γ
  %Rec :
    (binds : Vec (Pos × (Type (Δ + Γ) ⊎ Split Δ Γ)) (length Δ))
    (cont  : Stmts (Δ + Γ))
           → Stmts      Γ

open import Pretty
open import Pretty.Syntax

instance
  {-# TERMINATING #-}
  show-expr  : PP (Expr    Γ)
  show-alt   : PP (Alt     Γ)
  show-split : PP (Split Δ Γ)
  show-case  : PP (Case  Δ Γ)

  show-tele : PP (Tele Γ Δ)
  show-tele .pp = λ where
    [] → empty
    (n ∶ ty ∷ tele) → `⟨` decl⟨ [ n ] ⟩ + `:` ◈ pp ty `⟩` ◈ pp tele

  show-rectele : PP (RecTele Γ)
  show-rectele .pp = λ where
    []             → empty
    (f ∶ ty ∷ rec) → vcat ((field⟨ [ f ] ⟩ + `:` ◈ pp ty) ∷ pp rec ∷ [])

  show-newtype : PP (Newtype Γ)
  show-newtype .pp = λ where
    (%Data   n dat) → hang `data`   (vcat ((λ ((n , e)) → pp n + `:` ◈ pp e) <$> dat))
    (%Codata n cod) → hang `codata` (pp cod)

  show-type : PP (Type Γ)
  show-type .pp (%Type tele newtype) =
    hang (pp tele) (pp newtype)

call-spine : Expr Γ → List Doc
call-spine = λ where
  (%App f x) → call-spine f + (pp x ∷ [])
  other      → pp other ∷ []

show-alt .pp (%Alt pat body) = hang (pp pat ◈ `⇒`) (sep (call-spine body))

expr-vec→string : (Δ : Ctx) → Vec (Pos × (Type (Ξ + Γ) ⊎ Split Ξ Γ)) (length Δ) → List Doc
expr-vec→string [] [] = []
expr-vec→string  (n ∷ Δ) ((_ , expr) ∷ decls) =
  hang (decl⟨ n ⟩ ◈ `=`) (pp expr) ∷ expr-vec→string Δ decls

show-field : Name × Expr Γ → Doc
show-field (name , value) = hang field⟨ [ name ] ⟩ (pp value)

instance
  show-expr .pp = λ where
    (%Var  n _)       → use⟨ [ n ] ⟩
    (%Ctor ctor)      → ctor⟨ [ ctor ] ⟩
    (%Field name)     → field⟨ [ name ] ⟩
    (%Record fields)  → `⟪` vcat (show-field <$> fields) `⟫`
    p@(%App  f x)     → `⟨` sep (call-spine p) `⟩`
    (%Lam  alts)      → vcat (pp <$> alts)
    (%U)              → `Type`
    (%Type ty)        → pp (ty .newtype)
    (%Pi   n dom cod) → `[` text [ n ] + `:` ◈ pp dom `]` ◈ pp cod

{-# TERMINATING #-}
show-case .pp (%Case pat body) = hang (pp pat ◈ MAGENTA (text "⇒")) (pp body)

show-split .pp = λ where
  (%Run    plain)  → pp plain
  (%Split  cases)  → vcat (pp <$> cases)

types→string : (Δ : Ctx) → Vec (Pos × Type Γ) (length Δ) → List Doc
types→string [] [] = []
types→string  (n ∷ Δ) ((_ , expr) ∷ decls) =
  hang (decl⟨ n ⟩ ◈ `=`) (pp expr) ∷ types→string Δ decls

instance
  show-stmt : PP (Stmts Γ)
  show-stmt .pp = λ where
    (%Do  expr) → `do` ◈ pp expr
    (%Let n ty val stmt) → vcat ( `let`
                                ∷ nest (hang (decl⟨ [ n ] ⟩ ◈ `:`) (pp ty))
                                ∷ nest (hang (decl⟨ [ n ] ⟩ ◈ `=`) (pp val))
                                ∷ empty
                                ∷ pp stmt
                                ∷ []
                                )
    (%Rec {Δ} binds cont) → vcat ( `let-rec`
                                 ∷ nest (vcat (expr-vec→string Δ binds))
                                 ∷ empty
                                 ∷ pp cont
                                 ∷ []
                                 )
