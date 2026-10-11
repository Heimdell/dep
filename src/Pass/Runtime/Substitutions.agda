
module Pass.Runtime.Substitutions where

open import Prelude
open import Phase.Scoped.Contexts
open import Phase.Runtime.Value
open import Phase.Scoped.Patterns
open import Name

{-
  Situations.
-}
data Err : Set where
  %type-err        : Err
  %naked-type      : Err
  %no-match        : Err
  %no-match-lethal : Err
  %no-field        : Err

module _ where

  open import Pretty

  instance
    show-inj₂ : PP Err
    show-inj₂ .pp = λ where
      %type-err        → text "type error"
      %naked-type      → text "naked type"
      %no-match        → text "no match"
      %no-match-lethal → text "no match for real"
      %no-field        → text "no field"

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
  Δ ⇶ Γ = (n : Name) → [ n ] ∈ Δ → T M (Value Γ)

  {-
    Unit substitution, does nothing.
  -}
  keep : Γ ⇶ Γ
  keep n = pure ∘ %Stuck ∘ %Var n

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
  (ΞΓ ∙ ΔΞ) n var = do
    value ← ΔΞ n var
    apply ΞΓ value

  infixr 3 _∙_

  {-
    Merge two subsitutions.
  -}
  _⊕_ : Δ ⇶ Γ → Θ ⇶ Γ → (Δ + Θ) ⇶ Γ
  (ΔΓ ⊕ ΘΞ) n var with split-ptr var
  (ΔΓ ⊕ ΘΞ) n var | inj₂ top = ΔΓ n top
  (ΔΓ ⊕ ΘΞ) n var | inj₁ bot = ΘΞ n bot

  {-
    Compose two substitutions in parallel.
  -}
  _⊜_ : Δ ⇶ Γ → Θ ⇶ Ξ → (Δ + Θ) ⇶ (Γ + Ξ)
  (ΔΓ ⊜ ΘΞ) = (weaken-r ∙ ΔΓ) ⊕ (weaken ∙ ΘΞ)
    where
      weaken   : Γ ⇶ (Δ + Γ)
      weaken-r : Γ ⇶ (Γ + Δ)

      weaken   n = keep n ∘ weaken-ptr
      weaken-r n = keep n ∘ weaken-ptr-r

  {-
    Apply substitutions to variuos things.
  -}
  applyₛ : Δ ⇶ Γ → Stuck   Δ → T M (Value   Γ)
  applyₘ : Δ ⇶ Γ → Match   Δ → T M (Match   Γ)
  applyₜ : Δ ⇶ Γ → Split Θ Δ → T M (Split Θ Γ)
  applyₚ : Δ ⇶ Γ → Case  Θ Δ → T M (Case  Θ Γ)

  apply-te  : Δ ⇶ Γ → Tele    Δ Ξ → T M (Tele    Γ Ξ)
  apply-ty  : Δ ⇶ Γ → Type    Δ   → T M (Type    Γ)
  apply-nty : Δ ⇶ Γ → Newtype Δ   → T M (Newtype Γ)

  apply-ty sub (%Type tele type) =
    ⦇ %Type (apply-te sub tele) (apply-nty (keep ⊜ sub) type) ⦈

  apply-te sub = λ where
    (n ≔ ty)             → ⦇ (n ≔_) (apply sub ty) ⦈
    (n ∶ ty ∷ tele) → do
      ty   ← apply            sub  ty
      tele ← apply-te (keep ⊜ sub) tele
      pure (n ∶ ty ∷ tele)

  apply-nty sub = λ where
    (%Data   n ctors)  → ⦇ (%Data   n) (for ctors  (traverse ⦃ pair-is-traversable ⦄ (apply sub))) ⦈
    (%Codata n fields) → ⦇ (%Codata n) (for fields (traverse ⦃ pair-is-traversable ⦄ (apply sub))) ⦈

  applyₜ sub = λ where
    (%Run   plain) → ⦇ %Run   (apply (keep ⊜ sub) plain) ⦈
    (%Split cases) → ⦇ %Split (for cases (applyₚ sub)) ⦈

  applyₚ sub (%Case pat case) = ⦇ (%Case pat) (applyₜ (keep ⊜ sub) case) ⦈

  {-# TERMINATING #-}
  apply sub value = do
    case value of λ where
      (%Stuck  stuck)        → applyₛ sub stuck
      (%Ctor   ctor values)  → ⦇ (%Ctor ctor) (for values (apply sub)) ⦈
      (%Field  name)         → ⦇ (%Field name) ⦈
      (%Record fields)       → ⦇  %Record (for fields (traverse ⦃ pair-is-traversable ⦄ (apply sub))) ⦈
      (%Lam    cases)        → ⦇  %Lam (for cases (applyₘ sub)) ⦈
      (%Recur  n case trees) → ⦇ (%Recur n) (applyₜ sub case) (for trees (applyₜ sub)) ⦈
      (%U)                   → ⦇  %U ⦈
      (%Erased)              → ⦇  %Erased ⦈
      (%Pi     n dom cod)    → ⦇ (%Pi n) (apply sub dom) (apply (keep ⊜ sub) cod) ⦈
      (%Type   t)            → ⦇  %Type (apply-ty sub t) ⦈
      (%Newtype nt)          → ⦇  %Newtype (apply-nty sub nt) ⦈

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
  recure : Vec (Split Δ Γ) (length Δ) → Δ ⇶ Γ
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
    if [ ctor ] == [ ctor′ ]
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
  split : Vec (Split Δ Γ) (length Δ) → Value Γ → Case Δ Γ → MaybeT (T M) (Value Γ)

  {-
    If the pattern is irrefutable, pass whatever argument in.

    Return the subtree of the branch. Substitute the var with the value.

    {n -> rest} arg => rest [n / arg]
  -}
  split rec arg (%Case (%Var n) tree) = do
    tree ← lift $ applyₜ (push arg ⊕ keep) tree
    pure (%Recur nothing tree rec)

  {-
    Refutable import Phase.Scoped.Patterns get stuck on Stuck import Phase.Scoped.Terms.
    Report getting stuck.
  -}
  split rec (%Stuck _) (%Case pat tree) = loose

  {-
    Can't match lambdas.
  -}
  split rec (%Lam _) (%Case pat tree) = lift $ throw %type-err

  {-
    Finally, actual pattern matching!
  -}
  split rec (%Ctor ctor args) (%Case (%Ctor ctor′ pats) tree) = do
    if [ ctor ] == [ ctor′ ]
      then (do
        Δ    ← destruct-all args pats
        tree ← lift $ applyₜ (Δ ⊕ keep) tree
        pure (%Recur nothing tree rec))
      else lift (throw %no-match)

  {-
    Match failed.
  -}
  split rec arg (%Case pat tree) = lift $ throw %no-match

  {-
    Try a list of import Phase.Scoped.Patterns until one returns something (result or stuck), or throws anything
    other than %no-match.
  -}
  splits : Vec (Split Δ  Γ) (length Δ) → Value Γ → List (Case Δ Γ) → MaybeT (T M) (Value Γ)
  splits rec val = λ where
    [] → lift $ throw %no-match-lethal
    (case ∷ cases) → do
      lift-catch catch (split rec val case) λ where
        %no-match → splits rec val cases
        other     → lift $ throw other

  {-
    Try to apply a case-tree to a value.
  -}
  case-tree : Vec (Split Δ Γ) (length Δ) → Value Γ → Split Δ Γ → MaybeT (T M) (Value Γ)
  case-tree rec arg = λ where
    -- 'tis not a case tree, apply it as normal function
    (%Run f) → do
      f ← lift $ apply (recure rec ⊕ keep) f
      lift (call f arg)

    -- it is a case tree; try all cases in sequence
    (%Split cases) → do
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

  access : Name → Value Γ → T M (Value Γ)

  call-ty : Type Γ → Value Γ → T M (Value Γ)
  call-ty (%Type (n ≔ ty) type) value = ⦇ %Newtype (apply-nty (push value ⊕ keep) type) ⦈
  call-ty (%Type (n ∶ ty ∷ tele) type) value = do
    value′ ← apply (vacuous ⊜ keep) value
    ⦇ %Type ⦇ %Type (apply-te (push value ⊕ keep) tele) (apply-nty (push value′ ⊕ keep) type) ⦈ ⦈

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
      (%Field name)     → access name x
      (%Type ty)        → call-ty ty x
      other             → throw %type-err

  assoc : ⦃ _ : Eq A ⦄ (a : A) (as : List (A × B)) → Maybe B
  assoc b = λ where
    [] → nothing
    ((a , c) ∷ as) → (guard (a == b) *> pure c) <|> assoc b as

  access name = λ where
    (%Stuck x) → pure (%Stuck (%Get x name))
    (%Record x) →
      case assoc name x of λ where
        nothing  → throw %no-field
        (just f) → pure f
    other → throw %type-err

  applyₛ sub stuck = do
    case stuck of λ where
      (%Var n var) → do
        sub n var
      (%App f x) → do
        f ← applyₛ sub f
        x ← apply  sub x
        call f x
      (%Match f x) → do
        f ← apply sub f
        x ← apply sub x
        call f x

      (%Get b n) → do
        b ← applyₛ sub b
        access n b
