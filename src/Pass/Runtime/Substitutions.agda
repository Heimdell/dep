
module Pass.Runtime.Substitutions where

open import Prelude
open import Phase.Scoped.Contexts
open import Phase.Runtime.Value
open import Phase.Scoped.Case-splits
open import Phase.Scoped.Patterns

{-
  Situations.
-}
data Err : Set where
  %type-err : Err
  %no-match : Err
  %no-match-lethal : Err


instance
  show-err : Show Err
  show-err .show = λ where
    %type-err        → "type error"
    %no-match        → "no match"
    %no-match-lethal → "no match for real"

{-
  The monad we work in.
-}
M : Set → Set
M A = A ⊎ Err

{-
  Substitution is a function
    from a variable in a source context
    to value in a destination context.
-}
_⇶_ : (Δ Γ : Ctx) → Set
Δ ⇶ Γ = ∀ n → n ∈ Δ → M (Value Γ)

{-
  Unit substitution, does nothing.
-}
keep : Γ ⇶ Γ
keep _ = pure ∘ %Stuck ∘ %Var

{-
  Vacuous substitution.
-}
vacuous : [] ⇶ Γ
vacuous _ ()

{-
  Push a single value.
-}
push : Value Γ → (n ∷ []) ⇶ Γ
push val _ var = pure val


{-
  Use substitution to change context of normal form.
-}
apply : Δ ⇶ Γ → Value Δ → M (Value Γ)

{-
  Compose two substitutions sequentally.
-}
_∙_ : Ξ ⇶ Γ → Δ ⇶ Ξ → Δ ⇶ Γ
(ΞΓ ∙ ΔΞ) _ var = do
  value ← ΔΞ _ var
  apply ΞΓ value

{-
  Merge two subsitutions.
-}
_⊕_ : Δ ⇶ Γ → Θ ⇶ Γ → (Δ + Θ) ⇶ Γ
(ΔΓ ⊕ ΘΞ) _ var with split-ptr var
... | err top = ΔΓ _ top
... | ok  bot = ΘΞ _ bot

{-
  Compose two substitutions in parallel.
-}
_⊜_ : Δ ⇶ Γ → Θ ⇶ Ξ → (Δ + Θ) ⇶ (Γ + Ξ)
(ΔΓ ⊜ ΘΞ) = (weaken-r ∙ ΔΓ) ⊕ (weaken ∙ ΘΞ)
  where
    weaken : Γ ⇶ (Δ + Γ)
    weaken _ = keep _ ∘ weaken-ptr

    weaken-r : Γ ⇶ (Γ + Δ)
    weaken-r _ = keep _ ∘ weaken-ptr-r

{-
  Apply substitutions to variuos things.
-}
applyₛ : Δ ⇶ Γ → Stuck         Δ → M (Value         Γ)
applyₘ : Δ ⇶ Γ → Match         Δ → M (Match         Γ)
applyₜ : Δ ⇶ Γ → Case  Value Θ Δ → M (Case  Value Θ Γ)
applyₚ : Δ ⇶ Γ → Split Value Θ Δ → M (Split Value Θ Γ)

applyₜ sub = λ where
  (%Run  plain) → ⦇ %Run  (apply (keep ⊜ sub) plain) ⦈
  (%Case cases) → ⦇ %Case (for cases (applyₚ sub)) ⦈

applyₚ sub (%Split pat case) = ⦇ (%Split pat) (applyₜ (keep ⊜ sub) case) ⦈

{-# TERMINATING #-}
apply sub value = do
  case value of λ where
    (%Stuck stuck)        → applyₛ sub stuck
    (%Ctor  ctor values)  → ⦇ (%Ctor ctor) (for values (apply sub)) ⦈
    (%Lam   cases)        → ⦇  %Lam (for cases (applyₘ sub)) ⦈
    (%Recur n case trees) → ⦇ (%Recur n) (applyₜ sub case) (for trees (applyₜ sub)) ⦈

applyₘ sub match@(%Match pat value) = do
  ⦇ (%Match pat) (apply (keep ⊜ sub) value) ⦈

{-
  Make recursive binings into a substitution that removes them from a context.
  Effectively, we send their bodies in place of their references, and
  `let rec ... in ...` goes there with them.

  Substitution will replace each rec-binding with `let rec <binds> in <body>`.

  Imagine we have a program:

  > let
  >   even (Suc n) = odd n
  >   even  Zero   = True
  >
  >   odd  (Suc n) = even n
  >   odd   Zero   = False
  > in
  >   odd

  this subst will transform

  > odd                                              (Suc (Suc n))

  to

  > ({(Suc n) -> (let ... in even) n}, Zero -> True) (Suc (Suc n))

  The name is carried along so we do not print the bodies when they weren't
  at least partially applied.
-}
recure : Vec (Case Value Δ Γ) (length Δ) → Δ ⇶ Γ
recure funs n var = pure (%Recur (just n) (lookup funs (index-of var)) funs)

{-
  Call something.
-}
call : (f x : Value Γ) → M (Value Γ)

{-
  Pattern-match a value against a pattern, produce a substitution.

  If the matching is stuck, return `nothing`.
-}
destruct : Value Γ → Pat Δ → M (Maybe (Δ ⇶ Γ))

destruct-all : List (Value Γ) → Pats Δ → M (Maybe (Δ ⇶ Γ))
destruct-all [] [] = pure (just vacuous)
destruct-all (val ∷ vals) (pat ∷ pats) = do
  δ ← destruct     val  pat
  Δ ← destruct-all vals pats
  pure do
    δ ← δ
    Δ ← Δ
    pure (Δ ⊕ δ)
destruct-all vals pats = err %type-err

destruct  value         (%Var n)   = pure (just (push value))
destruct (%Stuck stuck)  pat       = pure  nothing
destruct (%Ctor ctor vals) (%Ctor ctor′ pats) = do
  if ctor == ctor′
    then destruct-all vals pats
    else err %no-match
destruct (%Lam x)        pat       = err %type-err
destruct  _              _         = err %no-match

{-
  Attempt a single pattern in a recursive setting.

  `rec : Vec (Case Value Δ Γ) (length Δ)` - are recursive bindings
  `arg : Value Γ`                         - value to be matched
  `split : Split Value Δ Γ`               - (pat ⇒ rec-body)

  If result is `nothing`, the match got stuck.
-}
split : Vec (Case Value Δ Γ) (length Δ) → Value Γ → Split Value Δ Γ → M (Maybe (Value Γ))

{-
  If the pattern is irrefutable, pass whatever argument in.

  Return the subtree of the branch. Substitute the var with the value.

  {n -> rest} arg => rest [n / arg]
-}
split rec arg (%Split (%Var n) tree) = do
  tree ← applyₜ (push arg ⊕ keep) tree
  pure (just (%Recur nothing tree rec))

{-
  Refutable import Phase.Scoped.Patterns get stuck on Stuck import Phase.Scoped.Terms.
  Report getting stuck.
-}
split rec (%Stuck _) (%Split pat tree) = pure nothing

{-
  Can't match lambdas.
-}
split rec (%Lam _) (%Split pat tree) = err %type-err

{-
  Finally, actual pattern matching!
-}
split rec (%Ctor ctor args) (%Split (%Ctor ctor′ pats) tree) = do
  if ctor == ctor′
    then (do
      case destruct-all args pats of λ where
        (err e) → err e
        (ok nothing) → ok nothing
        (ok (just Δ)) → do
          tree ← applyₜ (Δ ⊕ keep) tree
          pure (just (%Recur nothing tree rec)))
    else err %no-match

{-
  Match Zero witj Zero. Return the subtree of the branch.

  {Zero -> rest} Zero => rest
-}
-- split rec %Zero (%Split %Zero tree) = pure (just (%Recur nothing tree rec))

{-
  Match failed.
-}
split rec arg (%Split pat tree) = err %no-match

{-
  Try a list of import Phase.Scoped.Patterns until one returns something (result or stuck), or throws anything
  other than %no-match.
-}
splits : Vec (Case Value Δ  Γ) (length Δ) → Value Γ → List (Split Value Δ Γ) → M (Maybe (Value Γ))
splits rec val = λ where
  [] → err %no-match-lethal
  (case ∷ cases) → do
    case split rec val case of λ where
      (err %no-match) → splits rec val cases
      other           → other

{-
  Try to apply a case-tree to a value.
-}
case-tree : Vec (Case Value Δ Γ) (length Δ) → Value Γ → Case Value Δ Γ → M (Maybe (Value Γ))
case-tree rec arg = λ where
  -- 'tis not a case tree, apply it as normal function
  (%Run f) → do
    f ← apply (recure rec ⊕ keep) f
    ⦇ just (call f arg) ⦈

  -- it is a case tree; try all cases in sequence
  (%Case cases) → do
    splits rec arg cases

{-
  Check if the value is a case tree with no matches left.

  If it is, run it.
-}
force : Value Γ → M (Value Γ)
force f = do
  case f of λ where
    (%Recur _ (%Run f) funs) → apply (recure funs ⊕ keep) f
    other → pure other

{-
  Normal pattern match, no recursion involved.
-}
match-one : Value Γ → List (Match Γ) → Match Γ → M (Value Γ)
match-one val all-alts (%Match pat body) = do
  δ ← destruct val pat
  case δ of λ where
    (nothing) → pure (%Stuck (%Match (%Lam all-alts) val))
    (just  δ) → apply (δ ⊕ keep) body

{-
  Apply body of lambda (list of matches) to a value
-}
match : Value Γ → List (Match Γ) → List (Match Γ) → M (Value Γ)
match val all-alts = λ where
  [] → err %no-match-lethal
  (alt ∷ alts) → do
    case match-one val alts alt of λ where
      (err %no-match) → match val all-alts alts
      other           → other

{-
  Call something.

  If it is recirsive, force its result if neccesary.
-}
{-# TERMINATING #-}
call f x = do
  case f of λ where
    (%Recur n case trees) → do
      case-tree trees x case >>= λ where
        (just res) → force res
        nothing    → pure (%Stuck (%Match f x))
    (%Stuck f)  → ⦇ (%Stuck (%App f x)) ⦈
    (%Ctor ctor args) → ⦇ (%Ctor ctor (args + (x ∷ []))) ⦈
    (%Lam alts) → match x alts alts

applyₛ sub stuck = do
  case stuck of λ where
    (%Var   var)    → sub _ var
    (%App   f x)    → do
      f ← applyₛ sub f
      x ← apply  sub x
      call f x
    (%Match f x) -> do
      f ← apply sub f
      x ← apply sub x
      call f x
