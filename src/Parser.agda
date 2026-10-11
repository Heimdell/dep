
module Parser where

open import Prelude
open import Position

open import Control.Monad.State
open import Control.Monad.Error

record Input (L : Set) : Set where
  constructor %Input
  field
    offset  : ℕ
    lexemes : List L
    end     : Pos
open Input public

uncons-input : Input C → Maybe (C × Input C)
uncons-input input with input .lexemes
... | []     = nothing
... | l ∷ ls = just (l , record input
  { offset  = suc (input .offset)
  ; lexemes = ls
  })

start-input : List C × Pos → Input C
start-input (lexemes , end) .offset  = zero
start-input (lexemes , end) .lexemes = lexemes
start-input (lexemes , end) .end     = end

module _ {M : Set → Set} {{_ : Monad M}} where

  Parser : (L E : Set) (A : Set) → Set
  Parser L E = ErrorT (List E) (StateT (Input L) M)

  run-parser
    : Parser C E A
    →    Input C
    → M (Input C × (A ⊎ List E))
  run-parser parser = parser .run-error .run-state

  handle : Parser C E A → (List E → Parser C E A) → Parser C E A
  handle parser k =
    %ErrorT do
      %StateT λ input → do
        run-parser parser input >>= λ where
          (rest , inj₁ a) → pure (rest , inj₁ a)
          (rest , inj₂ e) →
            if input .offset == rest .offset
              then run-parser (k e) input
              else pure (rest , inj₂ e)

  fail-with : List E → Parser C E A
  fail-with errs =
    %ErrorT do
      %StateT λ input →
        pure (input , inj₂ errs)

  _∣_ : Parser C E A → Parser C E A → Parser C E A
  left ∣ right =
    handle left  λ errsₗ →
    handle right λ errsᵣ →
      fail-with (errsₗ + errsᵣ)

  _<?>_ : E → Parser C E A → Parser C E A
  e <?> parser = handle parser λ _ → fail-with (e ∷ [])
  infix 1 _<?>_

  match : (C → Maybe A) → Parser C E A
  match project =
    %ErrorT do
      %StateT λ input → do
        pure $ fromMaybe (input , inj₂ []) do
          c , rest ← uncons-input input
          a        ← project c
          pure (rest , inj₁ a)
