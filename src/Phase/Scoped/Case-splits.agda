
module Phase.Scoped.Case-splits where

open import Prelude
open import Phase.Scoped.Contexts
open import Phase.Scoped.Patterns
{-
  Case-tree for argument list.

  The idea is that we match arguments until we destructure or run out of parameters.

  Each spine in the tree ends either right after destructiring pattern, or when
  definition ran out of params.
-}
data Case (S : Ctx → Set) (Δ Γ : Ctx) : Set

{-
  Attempt to match against pattern `pat`.
-}
record Split (S : Ctx → Set) (Δ Γ : Ctx) : Set where
  inductive
  constructor %Split
  field
    {δ}  : Ctx               -- vars to be captured
    pat  : Pat δ             -- pattern to match against
    tree : Case S Δ (δ + Γ)  -- remainder of the case-tree
open Split

data Case S Δ Γ where
  %Run  : S (Δ + Γ)          → Case S Δ Γ  -- tree is done; you can apply it as normal
  %Case : List (Split S Δ Γ) → Case S Δ Γ  -- we still haven't matched enough of the params

instance
  {-# TERMINATING #-}
  show-tree  : {S : Ctx → Set} {{_ : {Δ : Ctx} → Show (S Δ)}} → Show (Case S Δ Γ)
  show-split : {S : Ctx → Set} {{_ : {Δ : Ctx} → Show (S Δ)}} → Show (Split S Δ Γ)

  show-split .show (%Split pat body) = show pat + " ⇒ " + show body

  show-tree .show = λ where
    (%Run  plain) → show plain
    (%Case cases) → "{" + intercalate " | " (show <$> cases) + "}"
