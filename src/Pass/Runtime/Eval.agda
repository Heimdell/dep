
module Pass.Runtime.Eval where

open import Prelude
open import Phase.Scoped.Contexts
open import Phase.Scoped.Terms as In
open import Phase.Runtime.Value as Out
open import Pass.Runtime.Substitutions

open import Control.Monad.Error
open import Name

module _ {M : Set → Set} {{_ : Monad M}} where

  {-# TERMINATING #-}
  eval : Expr Γ → T M (Value Γ)

  eval-tele : In.Tele Γ Δ → T M (Out.Tele Γ Δ ⊎ Δ ≡ [])
  eval-tele₁ : (n : Name) → In.Tele Γ ([ n ] ∷ Δ) → T M (Out.Tele Γ ([ n ] ∷ Δ))
  eval-tele₁ n₀ = λ where
    (n ∶ ty ∷ []) → ⦇ (n ≔_) (eval ty) ⦈
    (n ∶ ty ∷ (n₁ ∶ ty₁ ∷ tele₁)) → do
      tele ← eval-tele₁ n₁ (n₁ ∶ ty₁ ∷ tele₁)
      ty ← eval ty
      pure (n ∶ ty ∷ tele)

  eval-tele = λ where
    []              → ⦇ (inj₂ refl) ⦈
    (n ∶ ty ∷ tele) → ⦇ inj₁ (eval-tele₁ n (n ∶ ty ∷ tele)) ⦈

  eval-rte : In.RecTele Γ → T M (Out.RecTele Γ)
  eval-rte = λ where
    []              → ⦇ [] ⦈
    (n ∶ ty ∷ tele) → do
      ty ← eval ty
      tele ← eval-rte tele
      pure (n ∶ ty ∷ tele)

  eval-nty : In.Newtype Γ → T M (Out.Newtype Γ)
  eval-nty = λ where
    (%Data   n x) → ⦇ (%Data   n) (for x (traverse ⦃ pair-is-traversable ⦄ eval)) ⦈
    (%Codata n x) → ⦇ (%Codata n) (eval-rte x) ⦈

  eval-ty : In.Type Γ → T M (Value Γ)
  eval-ty (%Type tele newtype) = do
    eval-tele tele >>= λ where
      (inj₁ tele) → ⦇ %Type ⦇ (%Type tele) (eval-nty newtype) ⦈ ⦈
      (inj₂ refl) → ⦇ %Newtype (eval-nty newtype) ⦈

  alt→match : Alt Γ → T M (Match Γ)
  alt→match (%Alt pat body) = ⦇ (%Match pat) (eval body) ⦈

  {-# TERMINATING #-}
  eval-case  : In.Case  Δ Γ → T M (Out.Case  Δ Γ)
  eval-split : In.Split Δ Γ → T M (Out.Split Δ Γ)
  eval-case (%Case pat tree) = ⦇ (%Case pat) (eval-split tree) ⦈

  eval-split = λ where
    (%Run    f)         → ⦇ %Run   (eval f) ⦈
    (%Split  splits)    → ⦇ %Split (for splits eval-case) ⦈

  eval expr = do
    case expr of λ where
      (%Var n var)        → ⦇ (%Stuck (%Var n var)) ⦈
      (%Ctor  ctor)       → ⦇ (%Ctor ctor []) ⦈
      (%App   f x)        → do f ← eval f; x ← eval x; call f x
      (%Lam   alts)       → ⦇ %Lam (for alts alt→match) ⦈
      (%Record fields)    → ⦇ %Record (for fields (traverse ⦃ pair-is-traversable ⦄ eval)) ⦈
      (%U)                → ⦇ %U ⦈
      (%Type ty)          → eval-ty ty
      (%Pi n dom cod)     → ⦇ (%Pi n) (eval dom) (eval cod) ⦈
      (%Field name)       → ⦇ (%Field name) ⦈

  all-erased : _⇶_ {M = M} Δ Γ
  all-erased n _ = pure %Erased

  open import Phase.Scoped.Patterns

  eval→split : In.Type (Δ + Γ) ⊎ In.Split Δ Γ → T M (Out.Split Δ Γ)
  eval→split = λ where
    (inj₁ ty) → ⦇ %Run (eval-ty ty) ⦈
    (inj₂ fu) → eval-split fu

  run : Stmts Γ → T M (Value Γ)
  run = λ where
    (%Do expr) → eval expr
    (%Let n _ value expr) → do
      value ← eval value
      expr  ← run expr
      apply (push value ⊕ keep) expr

    (%Rec Δ expr) → do
      Δ    ← for Δ (eval→split ∘ proj₂)
      expr ← run expr
      apply (recure Δ ⊕ keep) expr

    -- (%Let-type n value expr) → do
    --   expr  ← run expr
    --   apply (push %Erased ⊕ keep) expr

    -- (%Rec-type Δ expr) → do
    --   expr ← run expr
    --   apply (all-erased ⊕ keep) expr
