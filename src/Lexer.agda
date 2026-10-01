
module Lexer where

open import Prelude
open import Position

record Input : Set where
  constructor %Input
  field
    source : String
    pos    : Pos
open Input public

next : Input → Maybe (Input × Char)
next input = do
  c , source ← uncons (input .source)
  let
    input = record input
      { source = source
      ; pos    = advance c (input .pos)
      }
  pure (input , c)

open import Control.Monad.Maybe
open import Control.Monad.State
open import Control.Monad.Identity

Lexer = MaybeT (StateT Input Identity)

run-m : Lexer A → Input → (Input × Maybe A)
run-m (%MaybeT (%StateT ma)) = run-identity ∘ ma

rollback : Lexer A → Lexer A
rollback ma = %MaybeT do
  %StateT do λ state → do
    case run-m ma state of λ where
      (state′ , just a)  → %Identity (state′ , just a)
      (_      , nothing) → %Identity (state  , nothing)

cover : Lexer A → Lexer String
cover ma = do
  old ← lift get
  a   ← ma
  new ← lift get
  pure (take (new .pos .off ∸ old .pos .off) (old .source))

next-char : Lexer Char
next-char .run-maybe .run-state state .run-identity = case next state of λ where
  (just (state′ , a)) → state′ , just a
  nothing             → state  , nothing

satisfy : (Char → Bool) → Lexer Char
satisfy predᵇ = do
  ch ← next-char
  guard (predᵇ ch)
  pure ch

open import Data.Char using (isSpace; _≤?_) renaming (_≟_ to _≟ᶜ_)
open import Relation.Nullary using (does)

space : Lexer Char
space = satisfy isSpace

spaces : Lexer ⊤
spaces = void $ many space

instance
  choice-pred : Choice λ A → A → Bool
  choice-pred .choice leftᵇ rightᵇ a = leftᵇ a ∨ rightᵇ a

⟦_⋯_⟧ : Char → Char → Char → Bool
⟦ low ⋯ hi ⟧ char = does (low ≤? char) ∧ does (char ≤? hi)

is : Char → Char → Bool
is ch ch′ = does (ch ≟ᶜ ch′)

is-var-start-char : Char → Bool
is-var-start-char = ⟦ 'a' ⋯ 'z' ⟧

is-ctor-start-char : Char → Bool
is-ctor-start-char = ⟦ 'A' ⋯ 'Z' ⟧

is-name-char : Char → Bool
is-name-char = is-var-start-char <|> is-ctor-start-char <|> ⟦ '0' ⋯ '9' ⟧ <|> is '-'

_∈ᵇ_ : String → List String → Bool
_∈ᵇ_ = any ∘ _==_

open import Name

data Payload : Set where
  %Var %Ctor : Name → Payload
  %Keyword   : String → Payload

var : List String → Lexer Payload
var reserved = do
  c ← rollback do
    satisfy is-var-start-char
  cs ← many (satisfy is-name-char)
  let name = fromList (c ∷ cs)
  if name ∈ᵇ reserved
    then pure (%Keyword name)
    else do
      %Input _ pos ← lift get
      pure (%Var (%Name pos name))

ctor : List String → Lexer Payload
ctor reserved = do
  c ← rollback do
    satisfy is-var-start-char
  cs ← many (satisfy is-name-char)
  let name = fromList (c ∷ cs)
  if name ∈ᵇ reserved
    then pure (%Keyword name)
    else do
      %Input _ pos ← lift get
      pure (%Ctor (%Name pos name))

keyword : List String → Lexer Payload
keyword = {! asum !}
