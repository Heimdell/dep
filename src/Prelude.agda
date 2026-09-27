
module Prelude where

open import Agda.Primitive as Prim public
  using    (Level; _⊔_; Setω; lzero; lsuc)

record Bifunctor (S : Set → Set → Set) : Set₁ where
  field
    <_,_> :
      {A B C D : Set}
      (f       : A → B)
      (g       : C → D)
      (sa      : S A C)
               → S B D
open Bifunctor ⦃...⦄ public

open import Function using (constᵣ; const; id; _$_; flip) public

record Functor (S : Set → Set) : Set₁ where
  field
    _<$>_ : {A B : Set} (f : A → B) (sa : S A) → S B
  _<&>_ : {A B : Set} (sa : S A) (f : A → B) → S B
  _<&>_ = flip _<$>_
  infixl 4 _<$>_
  infixr 4 _<&>_

open Functor ⦃...⦄ public

_$>_ : {A B : Set} {F : Set → Set} ⦃ _ : Functor F ⦄ → F A → B → F B
a $> b = const b <$> a
infixl 4 _$>_

_<$_ : {A B : Set} {F : Set → Set} ⦃ _ : Functor F ⦄ → A → F B → F A
a <$ b = const a <$> b
infixl 4 _<$_

record Pointed (S : Set → Set) : Set₁ where
  field
    pure  : {A   : Set} (a : A) → S A
open Pointed ⦃...⦄ public

record Apply (S : Set → Set) : Set₁ where
  field
    _<*>_ : {A B : Set} (f : S (A → B)) (x : S A) → S B
  infixl 4 _<*>_
open Apply ⦃...⦄ public

_*>_ : {A B : Set} {F : Set → Set} ⦃ _ : Functor F ⦄ ⦃ _ : Apply F ⦄ → F A → F B → F B
a *> b = constᵣ <$> a <*> b
infixl 4 _*>_

_<*_ : {A B : Set} {F : Set → Set} ⦃ _ : Functor F ⦄ ⦃ _ : Apply F ⦄ → F A → F B → F A
a <* b = const <$> a <*> b
infixl 4 _<*_

record Monad (S : Set → Set) : Set₁ where
  field
    _>>=_ : {A B : Set} (ma : S A) (k : A → S B) → S B
open Monad ⦃...⦄ public

_>>_ = _*>_

apply+pointed→functor :
  { S : Set → Set}
  ⦃ _ : Pointed S ⦄
  ⦃ _ : Apply S ⦄
      → Functor S
apply+pointed→functor ._<$>_ f = pure f <*>_

monad→apply : {S : Set → Set} ⦃ _ : Monad S ⦄ ⦃ _ : Pointed S ⦄ → Apply S
monad→apply ._<*>_ f x = do
  f ← f
  x ← x
  pure (f x)

record Empty (S : Set → Set) : Set₁ where
  field
    ∅     : {A : Set} → S A
open Empty ⦃...⦄ public

record Choice (S : Set → Set) : Set₁ where
  field
    _<|>_ : {A : Set} → S A → S A → S A
  infixr 3 _<|>_
open Choice ⦃...⦄ public

_∣_ = _<|>_
infixr 3 _∣_

open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤)

guard : {S : Set → Set} {{ _ : Pointed S }} {{ _ : Empty S}} → Bool → S ⊤
guard true  = pure _
guard false = ∅

open import Data.Unit using (⊤; tt) public

open import Data.List using (List; []; _∷_; replicate; drop; head) public
import Data.List as List
import Data.List.Properties as List

open import Function
  using (flip; const; constᵣ; _∘_; case_of_)
  renaming (_|>_ to _▷_) public

instance
  empty-list : Empty List
  empty-list .∅ = []

  choice-list : Choice List
  choice-list ._<|>_ = List._++_

  functor-list : Functor List
  functor-list ._<$>_ = List.map

  pt-list : Pointed List
  pt-list .pure = _∷ []

  app-list : Apply List
  app-list ._<*>_ = List.ap

  monad-list : Monad List
  monad-list ._>>=_ = flip List.concatMap

open import Data.Maybe using (Maybe; nothing; just; maybe) public
import Data.Maybe as Maybe

instance
  empty-maybe : Empty Maybe
  empty-maybe .∅ = nothing

  choice-maybe : Choice Maybe
  choice-maybe ._<|>_ = Maybe._<∣>_

  functor-maybe : Functor Maybe
  functor-maybe ._<$>_ = Maybe.map

  pt-maybe : Pointed Maybe
  pt-maybe .pure  = just

  app-maybe : Apply Maybe
  app-maybe ._<*>_ = Maybe.ap

  monad-maybe : Monad Maybe
  monad-maybe ._>>=_ = Maybe._>>=_

open import Data.Sum using (_⊎_; [_,_]′) renaming (inj₁ to ok; inj₂ to err) public
import Data.Sum as Sum

private variable
  A : Set

instance
  functor-sum : Functor (_⊎ A)
  functor-sum ._<$>_ = Sum.map₁

  pt-sum : Pointed (_⊎ A)
  pt-sum .pure  = ok

  app-sum : Apply (_⊎ A)
  app-sum ._<*>_ = Sum.[ Sum.map₁ , const ∘ err ]

  monad-sum : Monad (_⊎ A)
  monad-sum ._>>=_ = Sum.[ _▷_ , const ∘ err ]

  ⊎-bifunctor : Bifunctor _⊎_
  ⊎-bifunctor .<_,_> f g = Sum.[ ok ∘ f , err ∘ g ]′

open import IO.Primitive.Core using (IO) public
open import IO.Primitive.Finite public
import      IO.Primitive.Core as IO

instance
  pt-io : Pointed IO
  pt-io .pure = IO.pure

  monad-io : Monad IO
  monad-io ._>>=_ = IO._>>=_

  app-io : Apply IO
  app-io = monad→apply

  functor-io : Functor IO
  functor-io = apply+pointed→functor

open import Relation.Nullary using (Dec; yes; no; contraposition; map′) public
open import Relation.Binary.PropositionalEquality using
  ( _≡_
  ; refl
  ; subst
  ; cong
  ; cong₂
  ) public

open import Data.Nat using (ℕ; suc; zero; _∸_; _*_) renaming (_+_ to add-ℕ) public
import      Data.Nat as ℕ
import      Data.Nat.Show as ℕ
import      Data.Nat.Properties as ℕ

open import Data.Integer using (ℤ; -[1+_]; +_) public
import      Data.Integer as ℤ hiding (show)
import      Data.Integer.Show as ℤ-Show
import      Data.Integer.Properties as ℤ

open import Data.Fin using (Fin; suc; zero) public
import      Data.Fin as Fin
import      Data.Fin.Properties as Fin

import      Data.String as String
import      Data.String.Properties as String
open import Data.String
  using (String; fromList; toList; lines; unlines; unwords; uncons)
  renaming (_++_ to _◇_; replicate to replicate-str)
  public

record Monoid (S : Set) : Set where
  field
    𝟘     : S
    _+_   : S → S → S
    -- a+0≡a : ∀{a} → a + 𝟘 ≡ a
  infixr 5 _+_
open Monoid ⦃...⦄ public

{-# DISPLAY Monoid._+_ _ a b = a + b #-}
{-# DISPLAY Monoid.𝟘 _ = 𝟘 #-}
{-# DISPLAY Data.List._++_ a b = a + b #-}

instance
  nat-monoid : Monoid ℕ
  nat-monoid .𝟘     = zero
  nat-monoid ._+_   = ℕ._+_
  -- nat-monoid .a+0≡a = ℕ.+-identityʳ _

  z-monoid : Monoid ℤ
  z-monoid .𝟘     = ℤ.ℤ.pos 0
  z-monoid ._+_   = ℤ._+_
  -- z-monoid .a+0≡a = ℤ.+-identityʳ _

  list-monoid : {A : Set} → Monoid (List A)
  list-monoid .𝟘     = ∅
  list-monoid ._+_   = _<|>_
  -- list-monoid .a+0≡a = List.++-identityʳ _

open import Data.Vec using (Vec; []; _∷_; lookup) renaming (fromList to list→vec; _++_ to _vec-++_) public
import Data.Vec as Vec
import Data.Vec.Properties as Vec

instance
  functor-vec : {n : ℕ} → Functor λ A → Vec A n
  functor-vec ._<$>_ = Vec.map

import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties
open import Data.List.Relation.Unary.Any using (here; there) public
open All using (All; []; _∷_) renaming (map to All-map) public

record Foldable (S : Set → Set) : Set₁ where
  field
    fold-map : {A B : Set} ⦃ _ : Monoid B ⦄ (f : A → B) (sa : S A) → B

  length : {A : Set} (sa : S A) → ℕ
  length = fold-map (const 1)
open Foldable ⦃...⦄ public

fold-l : {A B : Set} (f : B → A → B) (z : B) (xs : List A) → B
fold-l f = λ where
  z []       → z
  z (x ∷ xs) → fold-l f (f z x) xs

open import Function using (const; _∘_) public

instance
  fold-vec : {n : ℕ} → Foldable (λ A → Vec A n)
  fold-vec .fold-map f = Vec.foldr _ (_+_ ∘ f) 𝟘

  fold-list : Foldable List
  fold-list .fold-map f = List.foldr (_+_ ∘ f) 𝟘

  fold-sum : Foldable (_⊎ A)
  fold-sum .fold-map f = Sum.[ f , const 𝟘 ]

  fold-maybe : Foldable Maybe
  fold-maybe .fold-map f = Maybe.maybe f 𝟘

record Traversable (S : Set → Set) : Set₁ where
  field
    traverse :
      { A B : Set }
      { M   : Set → Set }
      ⦃ _   : Apply M ⦄
      ⦃ _   : Pointed M ⦄
      ( f    : A → M B )
      ( sa   : S A )
             → M (S B)
  for :
    { A B : Set }
    { M   : Set → Set }
    ⦃ _   : Apply M ⦄
    ⦃ _   : Pointed M ⦄
    ( sa   : S A )
    ( f    : A → M B )
            → M (S B)
  for = flip traverse
open Traversable ⦃...⦄ public

instance
  {-# TERMINATING #-}
  Traversable-List : Traversable List
  Traversable-List .traverse f = λ where
    []         → ⦇ [] ⦈
    (x ∷ list) → ⦇ f x ∷ traverse f list ⦈

  {-# TERMINATING #-}
  Traversable-Vec : {n : ℕ} → Traversable λ A → Vec A n
  Traversable-Vec .traverse f = λ where
    []         → ⦇ [] ⦈
    (x ∷ list) → ⦇ f x ∷ traverse f list ⦈


open import Data.Product using (_×_; _,_; ∃; proj₁; proj₂; ∃-syntax; Σ) public
import      Data.Product as Product

instance
  Traversable-right : {A : Set} → Traversable (A ×_)
  Traversable-right .traverse f (a , b) = ⦇ pure a , f b ⦈

  Traversable-Maybe : Traversable Maybe
  Traversable-Maybe .traverse f = λ where
    (nothing) → ⦇ nothing    ⦈
    (just  a) → ⦇ just (f a) ⦈

  ×-bifunctor : Bifunctor _×_
  ×-bifunctor .<_,_> = Product.dmap′

  ×-functor : {A : Set} → Functor (A ×_)
  ×-functor ._<$>_ = Product.map₂′

  ×-pointed : {A : Set} ⦃ _ : Monoid A ⦄ → Pointed (A ×_)
  ×-pointed .pure = 𝟘 ,_

  x-apply : {A : Set} ⦃ _ : Monoid A ⦄ → Apply (A ×_)
  x-apply ._<*>_ (n , f) (m , x) = n + m , f x

  x-monad : {A : Set} ⦃ _ : Monoid A ⦄ → Monad (A ×_)
  x-monad ._>>=_ (n , a) k = Product.map₁ (_+ n) (k a)

open import Data.List.Membership.Propositional public

open import Data.Char using (Char; toℕ; fromℕ) public
import      Data.Char as     Char
open import Data.Bool
  using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
  public

record Eq (A : Set) : Set where
  field
    _==_ : A → A → Bool

  _!=_ : A → A → Bool
  a != b = not (a == b)
open Eq ⦃...⦄ public

record Same (A : Set) : Set where
  field
    _≟_ : (a b : A) → Dec (a ≡ b)
open Same ⦃...⦄ public

instance
  eq-char : Eq Char
  eq-char ._==_ = Char._==_

  eq-nat : Eq ℕ
  eq-nat ._==_ x y = Dec.does (x ℕ.≟ y)

  same-nat : Same ℕ
  same-nat ._≟_ x y = x ℕ.≟ y

  eq-z : Eq ℤ
  eq-z ._==_ x y = Dec.does (x ℤ.≟ y)

  eq-str : Eq String
  eq-str ._==_ x y = Dec.does (x String.≟ y)

  eq-maybe : ⦃ _ : Eq A ⦄ → Eq (Maybe A)
  eq-maybe ._==_ = λ where
    (just  x) (just  y) → x == y
    (just  x) (nothing) → false
    (nothing) (just  x) → false
    (nothing) (nothing) → true

_/=_ : ⦃ _ : Eq A ⦄ → A → A → Bool
a /= b = not (a == b)

record Any : Set where
  constructor %Any
  field
    get-any : Bool
open Any public

instance
  monoid-any : Monoid Any
  monoid-any .Monoid.𝟘 = %Any false
  monoid-any .Monoid._+_ (%Any a) (%Any b) = %Any (a ∨ b)
  -- monoid-any .Monoid.a+0≡a {%Any false} = refl
  -- monoid-any .Monoid.a+0≡a {%Any true}  = refl

any :
  {A  : Set}
  {F  : Set → Set}
  ⦃ _ : Foldable F ⦄
  (f  : A → Bool)
  (fa : F A)
      → Bool
any f = get-any ∘ fold-map (%Any ∘ f)

record Every : Set where
  constructor %Every
  field
    get-every : Bool
open Every public

instance
  monoid-every : Monoid Every
  monoid-every .Monoid.𝟘 = %Every true
  monoid-every .Monoid._+_ (%Every a) (%Every b) = %Every (a ∧ b)
  -- monoid-any .Monoid.a+0≡a {%Any false} = refl
  -- monoid-any .Monoid.a+0≡a {%Any true}  = refl

every :
  {A  : Set}
  {F  : Set → Set}
  ⦃ _ : Foldable F ⦄
  (f  : A → Bool)
  (fa : F A)
      → Bool
every f = get-every ∘ fold-map (%Every ∘ f)

instance
  Monoid-String : Monoid String
  Monoid-String .Monoid.𝟘 = ""
  Monoid-String .Monoid._+_ = _◇_
  -- Monoid-String .Monoid.a+0≡a = {! String.++-identityʳ _  !}

{-# TERMINATING #-}
many some :
  {A  : Set}
  {F  : Set → Set}
  ⦃ _ : Apply F ⦄
  ⦃ _ : Pointed F ⦄
  ⦃ _ : Choice F ⦄
  (a  : F A)
      → F (List A)
some a = ⦇ a ∷ many a ⦈

many a = some a <|> pure []

_／⁺_ :
  {A B : Set}
  {F   : Set → Set}
  ⦃ _  : Apply F ⦄
  ⦃ _  : Functor F ⦄
  ⦃ _  : Pointed F ⦄
  ⦃ _  : Choice F ⦄
  (a   : F A)
  (b   : F B)
      → F (List A)
a ／⁺ sep = ⦇ a ∷ many (sep *> a) ⦈

_／_ :
  {A B : Set}
  {F   : Set → Set}
  ⦃ _  : Apply F ⦄
  ⦃ _  : Functor F ⦄
  ⦃ _  : Pointed F ⦄
  ⦃ _  : Choice F ⦄
  (a   : F A)
  (b   : F B)
      → F (List A)
a ／ sep = (a ／⁺ sep) <|> pure []

optional :
  {A   : Set}
  {F   : Set → Set}
  ⦃ _  : Apply F ⦄
  ⦃ _  : Pointed F ⦄
  ⦃ _  : Choice F ⦄
  (a   : F A)
       → F (Maybe A)
optional a = ⦇ just a | nothing ⦈

record Show (A : Set) : Set where
  field
    show : A → String
open Show ⦃...⦄ public

instance
  Show-ℕ : Show ℕ
  Show-ℕ .show = ℕ.show

  Show-ℤ : Show ℤ
  Show-ℤ .show = ℤ-Show.show

  Show-str : Show String
  Show-str .show = String.show

  Show-char : Show Char
  Show-char .show = Char.show

len : String → ℕ
len = List.length ∘ toList

_[_] :
  {A   : Set}
  {P   : A → Set}
  {x   : A}
  {xs  : List A}
  (XS  : All (λ x → P x) xs)
  (ptr : x ∈ xs)
       → P x
(it ∷ _ ) [ here  refl ] = it
(_  ∷ XS) [ there ptr  ] = XS [ ptr ]

_++_ :
  {P     : A → Set}
  {xs ys : List A}
  (XS    : All P xs)
  (YS    : All P ys)
         → All P (xs + ys)
[] ++ YS = YS
(X ∷ XS) ++ YS = X ∷ (XS ++ YS)

when :
  {M  : Set → Set}
  {A  : Set}
  {{_ : Pointed M}}
  {{_ : Empty M}}
  (b  : Bool)
  (a  : A)
      → M A
when b a = if b then pure a else ∅

tt←_ : {A : Set} {F : Set → Set} ⦃ _ : Functor F ⦄ → F A → F ⊤
tt← ma = ma $> _

infix 5 tt←_

data FreeMonoid (A : Set) : Set where
  empty   :                        FreeMonoid A
  ⟨_⟩     :                   A  → FreeMonoid A
  compose : (a b : FreeMonoid A) → FreeMonoid A

instance
  monoid-free : {A : Set} → Monoid (FreeMonoid A)
  monoid-free .𝟘           = empty
  monoid-free ._+_ empty b = b
  monoid-free ._+_ a empty = a
  monoid-free ._+_ a b     = compose a b

  {-# TERMINATING #-}
  free-foldable : Foldable FreeMonoid
  free-foldable .fold-map f = λ where
    empty          → 𝟘
    ⟨ x ⟩          → f x
    (compose m m₁) → fold-map f m + fold-map f m₁

uncons-list : {A : Set} → List A → Maybe (List A × A)
uncons-list = λ where
  []       → nothing
  (x ∷ xs) → just (xs , x)

punctuate :
  {A   : Set}
  {{_  : Monoid A}}
  (sep : A)
  (as  : List A)
       → A
punctuate sep = λ where
  []         → 𝟘
  (x ∷ [])   → x
  (x ∷ list) → x + sep + punctuate sep list

head? :
  {A   : Set}
  (a   : A)
  (as  : List A)
       → A
head? 𝟘 = λ where
  []      → 𝟘
  (x ∷ _) → x

split-ptr : {A : Set} {Δ Γ : List A} {a : A} → a ∈ (Δ + Γ) → a ∈ Γ ⊎ a ∈ Δ
split-ptr {Δ = []}     ptr        = ok ptr
split-ptr {Δ = x ∷ Δ} (here refl) = err (here refl)
split-ptr {Δ = x ∷ Δ} (there ptr) = [ ok , err ∘ there ]′ (split-ptr ptr)

index-of : {A : Set} {n : A} {Δ : List A} → n ∈ Δ → Fin (length Δ)
index-of (here refl) = zero
index-of (there ptr) = suc (index-of ptr)

weaken-ptr : {A : Set} {Δ Γ : List A} {a : A} → a ∈ Γ → a ∈ (Δ + Γ)
weaken-ptr {Δ = []}    ptr = ptr
weaken-ptr {Δ = x ∷ Δ} ptr = there (weaken-ptr ptr)

weaken-ptr-r : {A : Set} {Δ Γ : List A} {a : A} → a ∈ Γ → a ∈ (Γ + Δ)
weaken-ptr-r (here  refl) = here   refl
weaken-ptr-r (there ptr)  = there (weaken-ptr-r ptr)

record ErrorT (E : Set) (M : Set → Set) (A : Set) : Set where
  constructor %ErrorT
  field
    run : M (A ⊎ E)
open ErrorT public

instance
  error-t-monad :
    {E : Set}
    {M : Set → Set}
    ⦃ _ : Monad M ⦄
    ⦃ _ : Pointed M ⦄
      → Monad (ErrorT E M)
  error-t-monad ._>>=_ (%ErrorT ma) amb = %ErrorT do
    ma >>=
      [ run  ∘ amb
      , pure ∘ err
      ]′

  error-t-pointed :
    {E : Set}
    {M : Set → Set}
    ⦃ _ : Pointed M ⦄
      → Pointed (ErrorT E M)
  error-t-pointed .pure a = %ErrorT (pure (ok a))

  error-t-apply :
    {E : Set}
    {M : Set → Set}
    ⦃ _ : Monad M ⦄
    ⦃ _ : Pointed M ⦄
      → Apply (ErrorT E M)
  error-t-apply = monad→apply

  error-t-functor :
    {E : Set}
    {M : Set → Set}
    ⦃ _ : Monad M ⦄
    ⦃ _ : Pointed M ⦄
      → Functor (ErrorT E M)
  error-t-functor = apply+pointed→functor

record Transformer (T : (Set → Set) → Set → Set) : Set₁ where
  field
    lift : {M : Set → Set} {A : Set} {{_ : Functor M}} → M A → T M A
open Transformer {{...}} public

instance
  Transformer-ErrorT : {E : Set} → Transformer (ErrorT E)
  Transformer-ErrorT .lift ma = %ErrorT (ok <$> ma)

throw :
  {A E : Set}
  {M   : Set → Set}
  ⦃ _  : Pointed M ⦄
       → E
       → ErrorT E M A
throw e = %ErrorT (pure (err e))

_catch_ :
  {A E : Set}
  {M   : Set → Set}
  ⦃ _  : Pointed M ⦄
  ⦃ _  : Monad M ⦄
  (ma  : ErrorT E M A)
  (k   : E → ErrorT E M A)
       → ErrorT E M A
%ErrorT ma catch handler = %ErrorT do
  ma >>=
    [ pure ∘ ok
    , run  ∘ handler
    ]′

intercalate : {M : Set} {{ _ : Monoid M}} → M → List M → M
intercalate sep = λ where
  []       → 𝟘
  (x ∷ []) → x
  (x ∷ xs) → fold-l (λ x xs → x + sep + xs) x xs

record StateT (S : Set) (M : Set → Set) (A : Set) : Set where
  constructor %StateT
  field
    run : S → M (S × A)
open StateT public

private variable
  S : Set
  M : Set → Set

instance
  Monad-StateT : {{_ : Monad M}} → Monad (StateT S M)
  Monad-StateT ._>>=_ (%StateT ma) amb = %StateT λ state → do
    state′ , a ← ma state
    amb a .run state′

  Pointed-StateT : {{_ : Pointed M}} → Pointed (StateT S M)
  Pointed-StateT .pure a = %StateT λ state → pure (state , a)

  Apply-StateT : {{_ : Pointed M}} {{_ : Monad M}} → Apply (StateT S M)
  Apply-StateT = monad→apply

  Functor-StateT :{{_ : Pointed M}} {{_ : Monad M}} → Functor (StateT S M)
  Functor-StateT = apply+pointed→functor

  Transformer-StateT : Transformer (StateT S)
  Transformer-StateT .lift ma = %StateT λ state → (state ,_) <$> ma

get : {{_ : Pointed M}} → StateT S M S
get = %StateT (λ state → pure (state , state))

modify : {{_ : Pointed M}} → (S → S) → StateT S M ⊤
modify f = %StateT (λ state → pure (f state , _))

times : {{_ : Monoid A}} → A → ℕ → A
times a = λ where
  0       → 𝟘
  (suc n) → a + times a n

_◈_ : String → String → String
a ◈ b = a + " " + b
