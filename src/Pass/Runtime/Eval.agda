
module Pass.Runtime.Eval where

open import Prelude
open import Phase.Scoped.Contexts
open import Phase.Scoped.Case-splits
open import Phase.Scoped.Terms
open import Phase.Runtime.Value
open import Pass.Runtime.Substitutions

{-# TERMINATING #-}
eval : Expr Γ → M (Value Γ)

alt→match : Alt Γ → M (Match Γ)
alt→match (%Alt pat body) = ⦇ (%Match pat) (eval body) ⦈

{-# TERMINATING #-}
eval-case  : Case  Expr Δ Γ → M (Case  Value Δ Γ)
eval-split : Split Expr Δ Γ → M (Split Value Δ Γ)
eval-split (%Split pat tree) = ⦇ (%Split pat) (eval-case tree) ⦈

eval-case = λ where
  (%Run  f)      → ⦇ %Run  (eval f) ⦈
  (%Case splits) → ⦇ %Case (for splits eval-split) ⦈

eval expr = do
  case expr of λ where
    (%Var _ var)  → ⦇ (%Stuck (%Var var)) ⦈
    (%Suc   expr) → ⦇ %Suc (eval expr) ⦈
    (%Zero)       → ⦇ %Zero ⦈
    (%App   f x)  → do f ← eval f; x ← eval x; call f x
    (%Lam   alts) → ⦇ %Lam (for alts alt→match) ⦈
    (%Let Δ expr) → do
      Δ    ← for Δ eval-case
      expr ← eval expr
      apply (recure Δ ⊕ keep) expr
