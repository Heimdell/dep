module Pretty where

open import Prelude

data Size : Set where
  %Finite   : ℕ → Size
  %Infinite : Size

instance
  semigroup-size : RawSemigroup Size
  semigroup-size .add = λ where
    (%Finite x) (%Finite x₁) → %Finite (x + x₁)
    (%Finite x) %Infinite → %Infinite
    %Infinite _ → %Infinite

  monoid-size : RawMonoid Size
  monoid-size .empty = %Finite empty

data Doc′ : Set

Doc = Size × Doc′

data Doc′ where
  %Slug : String → Doc′
  %Cat  : List Doc → Doc′
  %Sep  : List Doc → Doc′
  %VCat : List Doc → Doc′
  %Nest : ℕ → Doc → Doc′
  %Hang : Doc → ℕ → Doc → Doc′

text : String → Doc
text str = %Finite (strlen str) , %Slug str

sep : List Doc → Doc
sep xs = fold-map proj₁ xs , %Sep xs

cat : List Doc → Doc
cat xs = fold-map proj₁ xs , %Cat xs

vcat : List Doc → Doc
vcat [] = %Finite 0 , %Slug ""
vcat (x ∷ []) = x
vcat xs = %Infinite , %VCat xs

nest : Doc → Doc
nest x = %Finite 2 + (proj₁ x) , %Nest 2 x

hang : Doc → Doc → Doc
hang a b = proj₁ a + proj₁ b , %Hang a 2 b

{-# TERMINATING #-}
flatten : Doc → String
flatten = λ where
  (sz , %Slug x) → x
  (_ , %Sep x) → intercalate " " (flatten <$> x)
  (_ , %Cat x) → fold-map flatten x
  (_ , %VCat x) → "<flatten %VCat>"
  (_ , %Nest x x₁) → flatten x₁
  (_ , %Hang x _ x₁) → flatten x + " " + flatten x₁

{-# TERMINATING #-}
norm : Doc → Doc
norm = λ where
  (fst , %Slug x) → fst , %Slug x
  (%Finite x₁ , %Sep x) → text (flatten (%Finite x₁ , %Sep x))
  (%Infinite , %Sep x) → %Infinite , %VCat (norm <$> x)
  (%Finite x₁ , %Cat x) → text (flatten (%Finite x₁ , %Cat x))
  (%Infinite , %Cat x) → %Infinite , %VCat (norm <$> x)
  (fst , %VCat x) → fst , %VCat (norm <$> x)
  (fst , %Nest x x₁) → fst , %Nest x (norm x₁)
  (%Finite x₁ , %Hang x n y) → text (flatten (%Finite x₁ , %Hang x n y))
  (%Infinite , %Hang x n y) → %Infinite , %Hang (norm x) n (norm y)

{-# TERMINATING #-}
render : ℕ → Doc → List String
render indent = λ where
  (fst , %Slug x) → (times "  " indent + x) ∷ []
  (fst , %Sep x) → (times "  " indent + "<render %Sep>") ∷ []
  (fst , %Cat x) → (times "  " indent + "<render %Cat>") ∷ []
  (fst , %VCat x) → fold-map (render indent) x
  (fst , %Nest x x₁) → render (suc indent) x₁
  (fst , %Hang x n y) → render indent x + render (suc indent) y

instance
  semigroup-doc : RawSemigroup Doc
  semigroup-doc .add a b = cat (a ∷ b ∷ [])

  monoid-doc : RawMonoid Doc
  monoid-doc .empty = text ""

infixr 5 _◈_
_◈_ : Doc → Doc → Doc
a ◈ b = sep (a ∷ b ∷ [])

style : String → Doc → Doc
style str doc = (%Finite 0 , %Slug ("\ESC[" + str + "m")) + doc + (%Finite 0 , %Slug "\x1b[0m")

green : Doc → Doc
green = style "32"

YELLOW : Doc → Doc
YELLOW = style "33;1"

yellow : Doc → Doc
yellow = style "33"

magenta : Doc → Doc
magenta = style "35"

MAGENTA : Doc → Doc
MAGENTA = style "35;1"

black : Doc → Doc
black = style "30;1"

red : Doc → Doc
red = style "31"

RED : Doc → Doc
RED = style "31;1"

record PP (A : Set) : Set where
  field
    pp : A → Doc
open PP {{...}} public

pretty : {A : Set} {{_ : PP A}} → A → String
pretty = intercalate "\n" ∘ render 0 ∘ norm ∘ pp

put : Doc → IO ⊤
put = putStrLn ∘ intercalate "\n" ∘ render 0 ∘ norm
