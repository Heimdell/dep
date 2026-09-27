module Main where

open import Prelude
open import Phase.Scoped.Terms
open import Phase.Scoped.Case-splits
open import Phase.Scoped.Patterns
open import Phase.Runtime.Value using ()
open import Pass.Runtime.Substitutions using ()
open import Pass.Runtime.Eval using (eval)

module _ where

  open import Phase.Scoped.Contexts

  Sucₚ : Pat Δ → Pat Δ
  Sucₚ pat = %Ctor "Suc" (pat ∷ [])

  Zeroₚ : Pat []
  Zeroₚ = %Ctor "Zero" []

  Sucₑ : Expr Γ → Expr Γ
  Sucₑ expr = %Ctor "Suc" (expr ∷ [])

  Zeroₑ : Expr Γ
  Zeroₑ = %Ctor "Zero" []

  ⟨_◂_⟩ : (f x : Expr Γ) → Expr Γ
  ⟨ f ◂ x ⟩ = %App f x

  instance
    deeper : ⦃ it : n ∈ Δ ⦄ → n ∈ (m ∷ Δ)
    deeper ⦃ it ⦄ = there it
    {-# INCOHERENT deeper #-}

    shallow : n ∈ (n ∷ Δ)
    shallow = here refl

  Var : (n : Name) ⦃ it : n ∈ Γ ⦄ → Expr Γ
  Var n ⦃ it ⦄ = %Var n it

  _⇒_ : Pat Θ → Case Expr Δ (Θ + Γ) → Split Expr Δ Γ
  pat ⇒ body = %Split pat body

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
expr : Expr []
expr = %Rec {Δ = "add" ∷ []}
  ( %Case
      ( Sucₚ (%Var "n") ⇒ %Run (%Lam (%Var "m" ⇉
          Sucₑ ⟨ ⟨ Var "add" ◂ Var "n" ⟩ ◂ Var "m" ⟩
        ∷ []))
      ∷ %Var "n" ⇒ %Case
          ( Sucₚ (%Var "m") ⇒ %Run (Sucₑ ⟨ ⟨ Var "add" ◂ Var "n" ⟩ ◂ Var "m" ⟩)
          ∷       %Var "m"  ⇒ %Run  Zeroₑ
          ∷ []
          )
      ∷ []
      )
  ∷ []
  )
  (%Rec {Δ = "mult" ∷ []}
    ( %Case
        ( Sucₚ (%Var "n") ⇒ %Run (%Lam (%Var "m" ⇉
            ⟨ ⟨ (Var "add") ◂ Var "m" ⟩ ◂ ⟨ ⟨ Var "mult" ◂ Var "n" ⟩ ◂ Var "m" ⟩ ⟩
          ∷ []))
        ∷ Zeroₚ ⇒ %Run (%Lam (%Var "m" ⇉ Zeroₑ ∷ []))
        ∷ []
        )
    ∷ []
    )
    ⟨ Var "mult" ◂ (Sucₑ (Sucₑ Zeroₑ)) ⟩
  )

main : IO ⊤
main = do
  putStrLn (show expr)
  putStrLn "  ⇒"
  case (eval expr) of λ where
    (ok  value) -> putStrLn ("ok " + show value)
    (err error) -> putStrLn ("err " + show error)
