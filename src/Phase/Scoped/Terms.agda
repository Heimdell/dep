
module Phase.Scoped.Terms where

open import Prelude
open import Phase.Scoped.Contexts
open import Phase.Scoped.Patterns
open import Name

record Alt  (Γ : Ctx) : Set
data   Expr (Γ : Ctx) : Set
{-
  Split-tree for argument list.

  The idea is that we match arguments until we destructure or run out of parameters.

  Each spine in the tree ends either right after destructiring pattern, or when
  definition ran out of params.
-}
data Split (Δ Γ : Ctx) : Set

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
  %Pi     : (n : Name) → Expr Γ → Expr ([ n ] ∷ Γ) → Expr Γ

  %Let    : (n : Name) (ty value : Expr Γ) → Expr ([ n ] ∷ Γ) → Expr Γ

  %Rec    :
    (binds : Vec (Split Δ Γ) (length Δ))
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

-- data Stmts (Γ : Ctx) : Set where
--   %Do  : Expr Γ → Stmts Γ
--   %Let : (n : Name) (ty val : Expr Γ) → Stmts ({![_]  !} ∷ Γ) → Stmts Γ

open import Pretty
open import Pretty.Syntax

instance
  {-# TERMINATING #-}
  show-expr  : PP (Expr    Γ)
  show-alt   : PP (Alt     Γ)
  show-split : PP (Split Δ Γ)
  show-case  : PP (Case  Δ Γ)

call-spine : Expr Γ → List Doc
call-spine = λ where
  (%App f x) → call-spine f + (pp x ∷ [])
  other      → pp other ∷ []

show-alt .pp (%Alt pat body) = hang (pp pat ◈ `⇒`) (sep (call-spine body))

expr-vec→string : (Δ : Ctx) → Vec (Split Ξ Γ) (length Δ) → List Doc
expr-vec→string [] [] = []
expr-vec→string  (n ∷ Δ) (expr ∷ decls) =
  hang (decl⟨ n ⟩ ◈ `=`) (pp expr) ∷ expr-vec→string Δ decls

show-field : Name × Expr Γ → Doc
show-field (name , value) = hang field⟨ [ name ] ⟩ (pp value)

instance
  show-expr .pp = λ where
    (%Var  n _)               → use⟨ [ n ] ⟩
    (%Ctor ctor)              → ctor⟨ [ ctor ] ⟩
    (%Field name)             → field⟨ [ name ] ⟩
    (%Record fields)          → `⟪` vcat (show-field <$> fields) `⟫`
    p@(%App  f x)             → `⟨` sep (call-spine p) `⟩`
    (%Lam  alts)              → vcat (pp <$> alts)
    (%Let  n ty value expr)   → vcat ( `let`
                                     ∷ nest (hang (decl⟨ [ n ] ⟩ ◈ `:`) (pp ty))
                                     ∷ nest (hang (decl⟨ [ n ] ⟩ ◈ `=`) (pp value))
                                     ∷ empty
                                     ∷ pp expr
                                     ∷ []
                                     )
    (%U)                      → `Type`
    (%Pi   n dom cod)         → `[` text [ n ] + `:` ◈ pp dom `]` ◈ pp cod
    (%Rec  {Δ} δ expr)        → vcat ( `let-rec`
                                     ∷ nest (vcat (expr-vec→string Δ δ))
                                     ∷ empty
                                     ∷ pp expr
                                     ∷ []
                                     )

{-# TERMINATING #-}
show-case .pp (%Case pat body) = hang (pp pat ◈ MAGENTA (text "⇒")) (pp body)

show-split .pp = λ where
  (%Run    plain)  → pp plain
  (%Split  cases)  → vcat (pp <$> cases)
  -- (%With   expr cases) → hang (`with` ◈ pp expr) (vcat (pp <$> cases))
