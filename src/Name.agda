module Name where

open import Prelude
open import Position

record Name : Set where
  constructor %Name
  field
    pos : Pos
    [_] : String
open Name public

♯_ : String → Name
(♯ str) .pos = <nowhere>
[ ♯ str ] = str

module _ where

  open import Pretty

  instance
    name-is-pretty : PP Name
    name-is-pretty .pp name = text [ name ]

  instance
    name-is-eq : Eq Name
    name-is-eq ._==_ a b = [ a ] == [ b ]
