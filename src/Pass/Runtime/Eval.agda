
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

      (%Let n _ value expr) → do
        value ← eval value
        expr  ← eval expr
        apply (push value ⊕ keep) expr

      (%Rec Δ expr) → do
        Δ    ← for Δ eval-split
        expr ← eval expr
        apply (recure Δ ⊕ keep) expr

      (%Field name) → ⦇ (%Field name) ⦈
