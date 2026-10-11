
module Pass.Lexer where

open import Prelude

open import Position
open import Lexer

lex-file : (file src : String) → IO ((List Lexeme × Pos) ⊎ Pos)
lex-file = lex
  ( "type"
  ∷ "data"
  ∷ "end"
  ∷ "let"
  ∷ "rec"
  ∷ "function"
  ∷ "in"
  ∷ [])
  []
  ("=" ∷ "|" ∷ ":" ∷ "->" ∷ "{" ∷ "}" ∷ "[" ∷ "]" ∷ "(" ∷ ")" ∷ ";" ∷ "_" ∷ [])
