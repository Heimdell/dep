module Main where

open import Prelude
open import Phase.Scoped.Terms
open import Phase.Scoped.Case-splits
open import Phase.Scoped.Patterns
open import Phase.Runtime.Value using ()
open import Pass.Runtime.Substitutions using ()
open import Pass.Runtime.Eval using (eval)

{-

let
  add (Suc n)     m  = Suc (add n m)
  add      n (Suc m) = Suc (add n m)
  add      n      m  = Zero
in
let
  mult (Suc n) m = add m (mult n m)
  mult  Zero   m = Zero
in
  mult 2

-}
expr : Expr []
expr =
  %Rec {Δ = "add" ∷ []}
   ( %Case
      ( %Split (%Suc (%Var "n")) (%Run (%Lam (%Alt (%Var "m")
          (%Suc (%App (%App
            (%Var "add" (there (here refl)))
            (%Var "n" (there (there (here refl)))))
            (%Var "m" (here refl))))
        ∷ [])))
      ∷ %Split (%Var "n") (%Case
          ( %Split (%Suc (%Var "m"))
              (%Run (%Suc (%App (%App (%Var "add" (here refl))
                                (%Var "n" (there (there (here refl)))))
                                (%Var "m" (there (here refl))))))
          ∷ %Split (%Var "m") (%Run %Zero)
          ∷ []))
      ∷ []
      )
   ∷ []
   ) $
  %Rec {Δ = "mult" ∷ []}
   ( %Case
      ( %Split (%Suc (%Var "n")) (%Run (%Lam (%Alt (%Var "m")
          (%App (%App (%Var "add" (there (there (there (here refl)))))
                      (%Var "m" (here refl)))
               (%App (%App (%Var "mult" (there (here refl)))
                           (%Var "n" (there (there (here refl)))))
                           (%Var "m" (here refl))))
        ∷ [])))
      ∷ %Split %Zero (%Run (%Lam (%Alt (%Var "m") %Zero ∷ [])))
      ∷ []
      )
   ∷ []
   ) $
   (%App (%Var "mult" (here refl)) (%Suc (%Suc %Zero)))

main : IO ⊤
main = do
  putStrLn (show expr)
  putStrLn "  ⇒"
  case (eval expr) of λ where
    (ok  value) -> putStrLn ("ok " + show value)
    (err error) -> putStrLn ("err " + show error)
