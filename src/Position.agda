module Position where

open import Prelude

record Pos : Set where
  constructor %Pos
  field
    file : String
    line : ℕ
    col  : ℕ
    off  : ℕ
open Pos public

start : String → Pos
start file .file = file
start file .line = 0
start file .col  = 0
start file .off  = 0

advance : Char → Pos → Pos
advance '\n' pos = record pos
  { line = suc (pos .line)
  ; off  = suc (pos .off)
  ; col  = 0
  }
advance ch pos = record pos
  { off = suc (pos .off)
  ; col = suc (pos .col)
  }
