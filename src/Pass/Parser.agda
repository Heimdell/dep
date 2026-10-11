
module Pass.Parser where

open import Prelude

open import Lexer
open import Parser

open import Control.Monad.State
open import Control.Monad.Error
open import Control.Monad.IO

P = Parser Payload String

`_` : String → P ⊤
` kw ` = kw <?> match λ where
  (%Keyword x) → guard (kw == x)
  _ → nothing

open import Name
open import Position

name : P Name
name = "var-name" <?> match λ where
  (%Var x) → pure x
  other    → nothing

NAME : P Name
NAME = "ctor-name" <?> match λ where
  (%Ctor x) → pure x
  other     → nothing

dot-name : P Name
dot-name = "field-name" <?> match λ where
  (%Field x) → pure x
  other      → nothing

open import Phase.Raw.Terms

`⟨`_`⟩` : P A → P A
`⟨` p `⟩` = ` "(" ` *> p <* ` ")" `

`[`_`]` : P A → P A
`[` p `]` = ` "[" ` *> p <* ` "]" `

`⟪`_`⟫` : P A → P A
`⟪` p `⟫` = ` "{" ` *> p <* ` "}" `

{-# TERMINATING #-}
pat : P Pat
pat =       ⦇ %Var  name ⦈
    <|>     ⦇ %Ctor NAME ⦇ [] ⦈ ⦈
    <|> `⟨` ⦇ %Ctor NAME (many pat) ⦈ `⟩`

alt : P Alt
{-# TERMINATING #-}
expr term : P Expr

pi : P Expr
pi = ⦇ (flip (fold-r (λ (n , ty) → %Pi n ty))) (many `[` ⦇ name , expr ⦈ `]`) expr ⦈

term = ⦇ %Var  name ⦈
   <|> ⦇ %Ctor NAME ⦈
   <|> `⟨` expr `⟩`
   <|> `⟪` ⦇ %Lam cursor (sep-by alt ` "|" `) ⦈ `⟫`
   <|> ` "rec" ` *> `⟪` ⦇ %Record cursor (sep-by ⦇ (dot-name <* ` "=" `) , expr ⦈ ` ";" `) ⦈ `⟫`
   <|> ` "*"   ` *> ⦇ %U ⦈
   <|> ` "pi"  ` *>   pi

apply : Expr → Pos × (Expr ⊎ Name) → Expr
apply f = λ where
  (pos , inj₁ arg)    → %App pos f arg
  (pos , inj₂ method) → %App pos (%Field method) f

expr = do
  f ← term
  xs ← many ⦇ cursor , ⦇ inj₁ term | inj₂ dot-name ⦈ ⦈
  pure (fold-l {F = List} apply f xs)

alt = ⦇ %Alt (pat <* ` "=>" `) expr ⦈

-- stmt : P Stmts
-- stmt = ⦇ {!  !} ⦈
--    <|> ⦇ {!  !} ⦈
--    <|> ⦇ {!  !} ⦈
