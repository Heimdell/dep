module Position where

open import Prelude

record Pos : Set where
  constructor %Pos
  field
    file : String
    src  : String
    line : ℕ
    col  : ℕ
    off  : ℕ
open Pos public

start : String → String → Pos
start file src .file = file
start file src .src  = src
start file src .line = 0
start file src .col  = 0
start file src .off  = 0

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

module _ where

  open import Pretty
  open import Data.String using (lines)

  nth : ℕ → List A → Maybe A
  nth (suc n) (_ ∷ xs) = nth n xs
  nth  zero   (x ∷ xs) = just x
  nth  _       _       = nothing

  instance
    pos-is-pretty : PP Pos
    pos-is-pretty .pp (%Pos file src line col _) = do
      let ls = lines src
      let ln = nth line ls
      vcat
        ( (text file + text ":" + pp line + text ":" + pp col)
        ∷ (text (fill (show line)) ◈ (text "|"))
        ∷ (text       (show line)  ◈ (text "|" ◈ text (maybe id "<no text>" ln)))
        ∷ (text (fill (show line)) ◈ (text "|" ◈ text (times "." col + "^")))
        ∷ []
        )
      where
        fill : String → String
        fill = fromList ∘ map (const ' ') ∘ toList

        open import Data.Nat.Show using (show)
