
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
open import Control.Monad.IO

Lexer = MaybeT (StateT Input IO)

run-m : Lexer A → Input → IO (Input × Maybe A)
run-m (%MaybeT (%StateT ma)) = ma

rollback : Lexer A → Lexer A
rollback ma = %MaybeT do
  %StateT do λ state → do
    res ← run-m ma state
    case res of λ where
      (state′ , just a)  → pure (state′ , just a)
      (_      , nothing) → pure (state  , nothing)

not-followed-by : Lexer A → Lexer ⊤
not-followed-by ma = %MaybeT do
  %StateT do λ state → do
    res ← run-m ma state
    case res of λ where
      (_ , just a)  → pure (state , nothing)
      (_ , nothing) → pure (state , just _)

cover : Lexer A → Lexer String
cover ma = do
  old ← lift get
  a   ← ma
  new ← lift get
  pure (take (new .pos .off ∸ old .pos .off) (old .source))

next-char : Lexer Char
next-char .run-maybe .run-state state = case next state of λ where
  (just (state′ , a)) → pure (state′ , just a)
  nothing             → pure (state  , nothing)

satisfy : (Char → Bool) → Lexer Char
satisfy predᵇ = rollback do
  ch ← next-char
  guard (predᵇ ch)
  pure ch

char : Char → Lexer Char
char = satisfy ∘ _==_

any-char : Lexer Char
any-char = satisfy (const true)

open import Data.Char using (isSpace; _≤?_) renaming (_≟_ to _≟ᶜ_)
open import Relation.Nullary using (does)

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
  %Var %Ctor : Name   → Payload
  %Keyword   : String → Payload
  %Field     : Name   → Payload

module _ where

  open import Pretty

  instance
    payload-is-pretty : PP Payload
    payload-is-pretty .pp = λ where
      (%Var     var) → yellow (pp var) + text "_"
      (%Ctor    VAR) → green (pp VAR) + text "_"
      (%Field   VAR) → red (pp VAR) + text "_"
      (%Keyword kw)  → magenta (text kw) + text "_"


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

field′ : Lexer Payload
field′ = do
  %Input _ pos ← lift get
  c ← rollback do
    char '.'
    satisfy is-var-start-char

  cs ← many (satisfy is-name-char)
  pure (%Field (%Name pos (fromList (c ∷ cs))))

ctor : List String → Lexer Payload
ctor reserved = do
  c ← rollback do
    satisfy is-ctor-start-char
  cs ← many (satisfy is-name-char)
  let name = fromList (c ∷ cs)
  if name ∈ᵇ reserved
    then pure (%Keyword name)
    else do
      %Input _ pos ← lift get
      pure (%Ctor (%Name pos name))

exact : String → Lexer Payload
exact str = do
  rollback do
    for (toList str) char
  pure (%Keyword str)

keyword : List String → Lexer Payload
keyword = backtrack exact

comment : Lexer ⊤
comment = void do
  rollback do
    for (toList "/*") char
    many do
      not-followed-by do
        for (toList "*/") char
      any-char
    for (toList "*/") char

record Lexeme : Set where
  constructor %Lexeme
  field
    pos : Pos
    payload : Payload
open Lexeme public

module _ where

  open import Pretty

  instance
    lexeme-is-pretty : PP Lexeme
    lexeme-is-pretty .pp = pp ∘ payload

take-str : ℕ → String → String
take-str  zero   _    = ""
take-str (suc n) str with uncons str
... | just (c , str′) = fromList (c ∷ []) + take-str n str′
... | nothing         = ""

open import Pretty renaming (put to p)

lexeme : (names NAMES symbols : List String) → Lexer Lexeme
lexeme names NAMES symbols = do
  input ← lift get
  -- lift (lift (p (pp (pos input))))
  payload ← var     names
        <|> ctor    NAMES
        <|> keyword symbols
        <|> field′
  pure (%Lexeme (input .pos) payload)

space : Lexer Char
space = rollback do satisfy isSpace

spaces : Lexer ⊤
spaces = void $ many (void space <|> comment)

lexemes : (names NAMES symbols : List String) → Lexer (List Lexeme)
lexemes names NAMES symbols = do
  spaces
  sep-by (lexeme names NAMES symbols) spaces
    <* not-followed-by any-char

lex : (names NAMES symbols : List String) (fname source : String) → IO (List Lexeme ⊎ Pos)
lex names NAMES symbols fname source = do
  let pos₀ = start fname source
  res ←
    lexemes names NAMES symbols
      .run-maybe
      .run-state (%Input source pos₀)
  case res of λ where
    (%Input _ _   , just ls) → pure (inj₁ ls)
    (%Input _ pos , nothing) → pure (inj₂ pos)
