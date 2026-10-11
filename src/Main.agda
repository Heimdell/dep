module Main where

open import Prelude

open import Phase.Scoped.Terms
open import Phase.Scoped.Patterns
open import Phase.Scoped.Contexts
open import Phase.Runtime.Value using ()
open import Pass.Runtime.Substitutions using ()
open import Pass.Runtime.Eval
open import Data.List.Relation.Unary.Any using (here; there)
open import Name
open import Position

instance
  deeper : ⦃ it : n ∈ Δ ⦄ → n ∈ (m ∷ Δ)
  deeper ⦃ it ⦄ = there it
  {-# INCOHERENT deeper #-}

  shallow : n ∈ (n ∷ Δ)
  shallow = here refl

module _ where

  open import Phase.Scoped.Contexts

  Sucₚ : Pat Δ → Pat Δ
  Sucₚ pat = %Ctor (♯ "Suc") (pat ∷ [])

  Zeroₚ : Pat []
  Zeroₚ = %Ctor (♯ "Zero") []

  Sucₑ : Expr Γ → Expr Γ
  Sucₑ expr = %App (%Ctor (♯ "Suc")) expr

  Zeroₑ : Expr Γ
  Zeroₑ = %Ctor (♯ "Zero")

  ⟨_◂_⟩ : (f x : Expr Γ) → Expr Γ
  ⟨ f ◂ x ⟩ = %App f x

  Var : (n : Name) ⦃ it : [ n ] ∈ Γ ⦄ → Expr Γ
  Var n ⦃ it ⦄ = %Var n it

  _⇒_ : Pat Θ → Split Δ (Θ + Γ) → Case Δ Γ
  pat ⇒ body = %Case pat body

  _⇉_ : Pat Θ → Expr (Θ + Γ) → Alt Γ
  pat ⇉ body = %Alt pat body

  infixr 6 _⇒_ _⇉_

-- let
--   add (Suc n)     m  = Suc (add n m)
--   add      n (Suc m) = Suc (add n m)
--   add      n      m  = Zero
-- in
-- let
--   mult (Suc n) m = add m (mult n m)
--   mult  Zero   m = Zero
-- in
--   mult 2
expr : Stmts []
expr = %Rec {Δ = "add" ∷ []}
  ( (<nowhere> , %Split
      ( Sucₚ (%Var (♯ "n")) ⇒ %Run (%Lam (%Var (♯ "m") ⇉
          Sucₑ ⟨ ⟨ Var (♯ "add") ◂ Var (♯ "n") ⟩ ◂ Var (♯ "m") ⟩
        ∷ []))
      ∷ %Var (♯ "n") ⇒ %Split
          ( Sucₚ (%Var (♯ "m")) ⇒ %Run (Sucₑ ⟨ ⟨ Var (♯ "add") ◂ Var (♯ "n") ⟩ ◂ Var (♯ "m") ⟩)
          ∷       %Var (♯ "m")  ⇒ %Run  Zeroₑ
          ∷ []
          )
      ∷ []
      ))
  ∷ []
  )
  (%Rec {Δ = "mult" ∷ []}
    ( (<nowhere> , %Split
        ( Sucₚ (%Var (♯ "n")) ⇒ %Run (%Lam (%Var (♯ "m") ⇉
            ⟨ ⟨ (Var (♯ "add")) ◂ Var (♯ "m") ⟩ ◂ ⟨ ⟨ Var (♯ "mult") ◂ Var (♯ "n") ⟩ ◂ Var (♯ "m") ⟩ ⟩
          ∷ []))
        ∷ Zeroₚ ⇒ %Run (%Lam (%Var (♯ "m") ⇉ Zeroₑ ∷ []))
        ∷ []
        ))
    ∷ []
    )
    (%Do ⟨ Var (♯ "mult") ◂ (Sucₑ (Sucₑ Zeroₑ)) ⟩)
  )

open import Pretty

open import Control.Monad.Error
open import Control.Monad.State using ()

open import Lexer
open import Pass.Lexer
import Pass.Parser as P
open import Parser
open import Position
open import Phase.Raw.Terms

main : IO ⊤
main = do
  -- putStrLn "Program"
  -- put (nest (pp expr))
  -- putStrLn "Evaluates to"
  -- run expr .run-error >>= λ where
  --   (inj₁ value) -> put (nest (pp value))
  --   (inj₂ error) -> put (nest (pp error))
  src ← readFile "example/test.dep"
  res ← lex-file "example/test.dep" src
  case res of λ where
    (inj₁ (ls , end)) → do
      run-parser (P.expr <* eof "end-of-file") (%Input 0 ls end) >>= λ where
        (fst , inj₁ x) → put (pp x)
        (fst , inj₂ y) → put (hang (text "expected" ◈ sep (text <$> y) ◈ text "at") (pp (get-cursor fst)))
      -- put (vcat (cat (map pp ls) ∷ pp end ∷ []))
    (inj₂ pos) → put (pp pos)
