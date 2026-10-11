
module Pass.Runtime.Eval where

open import Prelude
open import Phase.Scoped.Contexts
open import Phase.Scoped.Terms as In
open import Phase.Runtime.Value as Out
open import Pass.Runtime.Substitutions

open import Control.Monad.Error

module _ {M : Set → Set} {{_ : Monad M}} where

  {-# TERMINATING #-}
  eval : Expr Γ → T M (Value Γ)

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
      (%Pi n dom cod)     → ⦇ (%Pi n) (eval dom) (eval cod) ⦈
      (%Field name)       → ⦇ (%Field name) ⦈

  all-erased : _⇶_ {M = M} Δ Γ
  all-erased n _ = pure %Erased

  run : Stmts Γ → T M (Value Γ)
  run = λ where
    (%Do expr) → eval expr
    (%Let n _ value expr) → do
      value ← eval value
      expr  ← run expr
      apply (push value ⊕ keep) expr

    (%Rec Δ expr) → do
      Δ    ← for Δ (eval-split ∘ proj₂)
      expr ← run expr
      apply (recure Δ ⊕ keep) expr

    (%Let-type n value expr) → do
      expr  ← run expr
      apply (push %Erased ⊕ keep) expr

    (%Rec-type Δ expr) → do
      expr ← run expr
      apply (all-erased ⊕ keep) expr
