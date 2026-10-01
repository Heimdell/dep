module Name where

open import Prelude
open import Position

record Name : Set where
  constructor %Name
  field
    pos  : Pos
    name : String
open Name public

module _ where

  open import Pretty

  instance
    name-is-pretty : PP Name
    name-is-pretty .pp (%Name _ name) = text name
