{-# OPTIONS --cubical-compatible --guardedness --sized-types #-}

module induction-ex where

open import Relation.Binary.PropositionalEquality
open import Size
open import Data.Bool

data List (A : Set ) : Set where
    [] : List A
    _∷_ : A → List A → List A

data Nat : Set where
     zero : Nat
     suc  : Nat → Nat

add : Nat → Nat → Nat
add zero x = x
add (suc x) y = suc ( add x y )

_++_ : {A : Set} → List A → List A → List A
[] ++ y = y
(x ∷ t) ++ y = x ∷ ( t ++ y )

test1 = (zero ∷ []) ++ (zero ∷ [])

length : {A : Set } → List A → Nat
length [] = zero
length (_ ∷ t)  = suc ( length t )

lemma1 : {A : Set} → (x y : List A ) → length ( x ++ y ) ≡ add (length x) (length y)
lemma1 [] y = refl
lemma1 (x ∷ t) y = cong ( λ k → suc k ) lemma2  where
   lemma2 : length (t ++ y) ≡ add (length t) (length y)
   lemma2 = lemma1 t y

-- record List1 ( A : Set  ) : Set where
--    inductive
--    field
--       nil : List1 A 
--       cons : A → List1 A → List1 A
-- 
-- record List2 ( A : Set  ) : Set where
--    coinductive
--    field
--       nil : List2 A 
--       cons : A → List2 A → List2 A

data SList (i : Size) (A : Set) : Set where
  []' : SList i A
  _∷'_ : {j : Size< i} (x : A) (xs : SList j A) → SList i A


map : ∀{i A B} → (A → B) → SList i A → SList i B
map f []' = []'
map f ( x ∷' xs)= f x ∷' map f xs

foldr : ∀{i} {A B : Set} → (A → B → B) → B → SList i A → B
foldr c n []' = n
foldr c n (x ∷' xs) = c x (foldr c n xs)

any : ∀{i A} → (A → Bool) → SList i A → Bool
any p xs = foldr _∨_ false (map p xs)

-- Sappend : {A : Set } {i j : Size } → SList i A → SList j A → SList {!!} A
-- Sappend []' y = y
-- Sappend (x ∷' x₁) y =  _∷'_  {?}  x (Sappend x₁ y)

language : { Σ : Set } → Set
language {Σ} = List Σ → Bool

record Lang (i : Size) (A : Set) : Set where
  coinductive
  field
    ν : Bool
    δ : ∀{j : Size< i} → A → Lang j A

open Lang

∅ : ∀ {i A}  → Lang i A
ν ∅   = false
δ ∅ _ = ∅

-- record syntax does not recognize sized data
-- ∅' :  {i : Size } { A : Set }  → Lang i A
-- ∅' {i} {A}  = record { ν = false ; δ = lemma3 } where
--     lemma3 : {j : Size< i} → A → Lang j A
--     lemma3 {j} _ = ∅'

∅l : {A : Set } → language {A}
∅l _ = false

ε : ∀ {i A} → Lang i A
ν ε   = true
δ ε _ = ∅

εl : {A : Set } → language {A}
εl [] = true
εl (_ ∷ _)  = false

_+_ : ∀ {i A} → Lang i A → Lang i A → Lang i A
ν (a + b)   = ν a   ∨  ν b
δ (a + b) x = δ a x + δ b x

Union : {Σ : Set} → ( A B : language {Σ} ) → language {Σ}
Union {Σ} A B x = (A x ) ∨ (B x)

_·_ : ∀ {i A} → Lang i A → Lang i A → Lang i A
ν (a · b)   = ν a ∧ ν b
δ (a · b) x = if (ν a) then ((δ a x · b ) + (δ b x )) else ( δ a x · b )

split : {Σ : Set} → (List Σ → Bool)
      → ( List Σ → Bool) → List Σ → Bool
split x y  [] = x [] ∨ y []
split x y (h  ∷ t) = (x [] ∧ y (h  ∷ t)) ∨
  split (λ t1 → x (  h ∷ t1 ))  (λ t2 → y t2 ) t

Concat : {Σ : Set} → ( A B : language {Σ} ) → language {Σ}
Concat {Σ} A B = split A B

