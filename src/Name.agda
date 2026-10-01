module Name where

open import Prelude
open import Position

record Name : Set where
  constructor %Name
  field
    pos  : Pos
    name : String
open Name public
