
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
  %type-err        : Err
  %no-match        : Err
  %no-match-lethal : Err

module _ where

  open import Pretty

  instance
    show-inj₂ : PP Err
    show-inj₂ .pp = λ where
      %type-err        → text "type error"
      %no-match        → text "no match"
      %no-match-lethal → text "no match for real"

open import Control.Monad.Error

T : (Set → Set) → Set → Set
T = ErrorT Err

module _ {M : Set → Set} {{_ : Monad M}} where

  {-
    Substitution is a function
      from a variable in a source context
      to value in a destination context.
  -}
  _⇶_ : (Δ Γ : Ctx) → Set
  Δ ⇶ Γ = ∀ n → n ∈ Δ → T M (Value Γ)

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
  apply : Δ ⇶ Γ → Value Δ → T M (Value Γ)

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
  (ΔΓ ⊕ ΘΞ) _ var | inj₂ top = ΔΓ _ top
  (ΔΓ ⊕ ΘΞ) _ var | inj₁ bot = ΘΞ _ bot

  {-
    Compose two substitutions in parallel.
  -}
  _⊜_ : Δ ⇶ Γ → Θ ⇶ Ξ → (Δ + Θ) ⇶ (Γ + Ξ)
  (ΔΓ ⊜ ΘΞ) = (weaken-r ∙ ΔΓ) ⊕ (weaken ∙ ΘΞ)
    where
      weaken   : Γ ⇶ (Δ + Γ)
      weaken-r : Γ ⇶ (Γ + Δ)

      weaken   _ = keep _ ∘ weaken-ptr
      weaken-r _ = keep _ ∘ weaken-ptr-r

  {-
    Apply substitutions to variuos things.
  -}
  applyₛ : Δ ⇶ Γ → Stuck         Δ → T M (Value         Γ)
  applyₘ : Δ ⇶ Γ → Match         Δ → T M (Match         Γ)
  applyₜ : Δ ⇶ Γ → Case  Value Θ Δ → T M (Case  Value Θ Γ)
  applyₚ : Δ ⇶ Γ → Split Value Θ Δ → T M (Split Value Θ Γ)

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
      (%U)                  → ⦇  %U ⦈
      (%Pi    n dom cod)    → ⦇ (%Pi n) (apply sub dom) (apply (keep ⊜ sub) cod) ⦈

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
  call : (f x : Value Γ) → T M (Value Γ)

  open import Control.Monad.Maybe

  {-
    Pattern-match a value against a pattern, produce a substitution.

    If the matching is stuck, return `nothing`.
  -}
  destruct : Value Γ → Pat Δ → MaybeT (T M) (Δ ⇶ Γ)

  destruct-all : List (Value Γ) → Pats Δ → MaybeT (T M) (Δ ⇶ Γ)
  destruct-all [] [] = pure vacuous
  destruct-all (val ∷ vals) (pat ∷ pats) = do
    δ ← destruct     val  pat
    Δ ← destruct-all vals pats
    pure (Δ ⊕ δ)
  destruct-all vals pats = lift $ throw %type-err

  destruct  value         (%Var n)   = pure (push value)
  destruct (%Stuck stuck)  pat       = loose
  destruct (%Ctor ctor vals) (%Ctor ctor′ pats) = do
    if ctor == ctor′
      then destruct-all vals pats
      else lift (throw %no-match)
  destruct (%Lam x)        pat       = lift $ throw %type-err
  destruct  _              _         = lift $ throw %no-match

  {-
    Attempt a single pattern in a recursive setting.

    `rec : Vec (Case Value Δ Γ) (length Δ)` - are recursive bindings
    `arg : Value Γ`                         - value to be matched
    `split : Split Value Δ Γ`               - (pat ⇒ rec-body)

    If result is `nothing`, the match got stuck.
  -}
  split : Vec (Case Value Δ Γ) (length Δ) → Value Γ → Split Value Δ Γ → MaybeT (T M) (Value Γ)

  {-
    If the pattern is irrefutable, pass whatever argument in.

    Return the subtree of the branch. Substitute the var with the value.

    {n -> rest} arg => rest [n / arg]
  -}
  split rec arg (%Split (%Var n) tree) = do
    tree ← lift $ applyₜ (push arg ⊕ keep) tree
    pure (%Recur nothing tree rec)

  {-
    Refutable import Phase.Scoped.Patterns get stuck on Stuck import Phase.Scoped.Terms.
    Report getting stuck.
  -}
  split rec (%Stuck _) (%Split pat tree) = loose

  {-
    Can't match lambdas.
  -}
  split rec (%Lam _) (%Split pat tree) = lift $ throw %type-err

  {-
    Finally, actual pattern matching!
  -}
  split rec (%Ctor ctor args) (%Split (%Ctor ctor′ pats) tree) = do
    if ctor == ctor′
      then (do
        Δ    ← destruct-all args pats
        tree ← lift $ applyₜ (Δ ⊕ keep) tree
        pure (%Recur nothing tree rec))
      else lift (throw %no-match)

  {-
    Match failed.
  -}
  split rec arg (%Split pat tree) = lift $ throw %no-match

  {-
    Try a list of import Phase.Scoped.Patterns until one returns something (result or stuck), or throws anything
    other than %no-match.
  -}
  splits : Vec (Case Value Δ  Γ) (length Δ) → Value Γ → List (Split Value Δ Γ) → MaybeT (T M) (Value Γ)
  splits rec val = λ where
    [] → lift $ throw %no-match-lethal
    (case ∷ cases) → do
      lift-catch catch (split rec val case) λ where
        %no-match → splits rec val cases
        other     → lift $ throw other

  {-
    Try to apply a case-tree to a value.
  -}
  case-tree : Vec (Case Value Δ Γ) (length Δ) → Value Γ → Case Value Δ Γ → MaybeT (T M) (Value Γ)
  case-tree rec arg = λ where
    -- 'tis not a case tree, apply it as normal function
    (%Run f) → do
      f ← lift $ apply (recure rec ⊕ keep) f
      lift (call f arg)

    -- it is a case tree; try all cases in sequence
    (%Case cases) → do
      splits rec arg cases

  {-
    Check if the value is a case tree with no matches left.

    If it is, run it.
  -}
  force : Value Γ → T M (Value Γ)
  force f = do
    case f of λ where
      (%Recur _ (%Run f) funs) → apply (recure funs ⊕ keep) f
      other → pure other

  {-
    Normal pattern match, no recursion involved.
  -}
  match-one : Value Γ → List (Match Γ) → Match Γ → T M (Value Γ)
  match-one val all-alts (%Match pat body) = do
    δ ← destruct val pat .run-maybe
    case δ of λ where
      (nothing) → pure (%Stuck (%Match (%Lam all-alts) val))
      (just  δ) → apply (δ ⊕ keep) body

  {-
    Apply body of lambda (list of matches) to a value
  -}
  match : Value Γ → List (Match Γ) → List (Match Γ) → T M (Value Γ)
  match val all-alts = λ where
    [] → throw %no-match-lethal
    (alt ∷ alts) → do
      catch (match-one val alts alt) λ where
        %no-match → match val all-alts alts
        other     → throw other

  {-
    Call something.

    If it is recirsive, force its result if neccesary.
  -}
  {-# TERMINATING #-}
  call f x = do
    case f of λ where
      (%Recur n case trees) → do
        case-tree trees x case .run-maybe >>= λ where
          (just res) → force res
          nothing    → pure (%Stuck (%Match f x))
      (%Stuck f)        → ⦇ (%Stuck (%App f x)) ⦈
      (%Ctor ctor args) → ⦇ (%Ctor ctor (args + (x ∷ []))) ⦈
      (%Lam alts)       → match x alts alts
      other             → throw %type-err

  applyₛ sub stuck = do
    case stuck of λ where
      (%Var var) → do
        sub _ var
      (%App f x) → do
        f ← applyₛ sub f
        x ← apply  sub x
        call f x
      (%Match f x) → do
        f ← apply sub f
        x ← apply sub x
        call f x
