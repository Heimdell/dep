
module Pass.Lexer where

open import Prelude

open import Position
open import Lexer

reserved-list : List String
reserved-list =
  ( "type"
  ∷ "data"
  ∷ "end"
  ∷ "let"
  ∷ "rec"
  ∷ "function"
  ∷ "in"
  ∷ [])

lex-file : (file src : String) → IO ((List Lexeme × Pos) ⊎ Pos)
lex-file = lex reserved-list []
  ("=>" ∷ "|" ∷ ":" ∷ "*" ∷ "=" ∷ "{" ∷ "}" ∷ "[" ∷ "]" ∷ "(" ∷ ")" ∷ ";" ∷ "_" ∷ [])
