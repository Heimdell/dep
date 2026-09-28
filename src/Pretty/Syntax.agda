
module Pretty.Syntax where

open import Prelude
open import Pretty

`let` : Doc
`let` = MAGENTA (text "let")

`let-rec` : Doc
`let-rec` = MAGENTA (text "let rec")

`⇒` : Doc
`⇒` = MAGENTA (text "⇒")

`⟨`_`⟩` : Doc → Doc
`⟨` doc `⟩` = black (text "(") + doc + black (text ")")

`[`_`]` : Doc → Doc
`[` doc `]` = black (text "[") + doc + black (text "]")

`=` `:` `ₛ` : Doc
`=` = MAGENTA (text "=")
`:` = MAGENTA (text ":")
`ₛ` = MAGENTA (text "ₛ")

`Type` : Doc
`Type` = MAGENTA (text "Type")

use⟨_⟩ : String → Doc
use⟨ var ⟩ = yellow (text var)

rec⟨_⟩ : String → Doc
rec⟨ var ⟩ = red (text var)

decl⟨_⟩ : String → Doc
decl⟨ var ⟩ = YELLOW (text var)

ctor⟨_⟩ : String → Doc
ctor⟨ ctor ⟩ = green (text ctor)
