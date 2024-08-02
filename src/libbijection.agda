{-# OPTIONS --cubical-compatible --safe #-}

module libbijection where

open import Level renaming ( zero to Zero ; suc to Suc )
open import Data.Nat
open import Data.Maybe
open import Data.List hiding ([_] ; sum )
open import Data.Nat.Properties
open import Relation.Nullary
open import Data.Empty
open import Data.Unit 
open import  Relation.Binary.Core hiding (_⇔_)
open import  Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
-- open import Function.Inverse hiding (sym)
-- open import Function.Bijection renaming (Bijection to Bijection1)
open import Function.Equality hiding (cong)

open import logic
open import nat

-- record Bijection {n m : Level} (R : Set n) (S : Set m) : Set (n Level.⊔ m)  where
--    field
--        fun←  :  S → R
--        fun→  :  R → S
--        fiso← : (x : R)  → fun← ( fun→ x )  ≡ x 
--        fiso→ : (x : S ) → fun→ ( fun← x )  ≡ x 
-- 
-- injection :  {n m : Level} (R : Set n) (S : Set m) (f : R → S ) → Set (n Level.⊔ m)
-- injection R S f = (x y : R) → f x ≡ f y → x ≡ y

open Bijection 

b→injection1 : {n m : Level} (R : Set n) (S : Set m)  → (b : Bijection R S) → injection S R (fun← b)
b→injection1 R S b x y eq = trans (  sym ( fiso→ b x ) ) (trans (  cong (λ k → fun→ b k ) eq ) ( fiso→ b y  ))

--
-- injection as an uniquneness of bijection 
--
b→injection0 : {n m : Level} (R : Set n) (S : Set m)  → (b : Bijection R S) → injection R S (fun→ b)
b→injection0 R S b x y eq = begin
          x
        ≡⟨ sym ( fiso← b x ) ⟩
          fun← b ( fun→ b x )
        ≡⟨ cong (λ k → fun← b k ) eq ⟩
          fun← b ( fun→ b y )
        ≡⟨  fiso← b y  ⟩
          y  
        ∎  where open ≡-Reasoning

open import Relation.Binary using (Rel; Setoid; Symmetric; Total)
open import Function.Surjection

≡-Setoid :  {n : Level} (R : Set n) → Setoid n n
≡-Setoid R = record {
      Carrier = R
    ; _≈_ = _≡_
    ; isEquivalence = record { sym = sym ; refl = refl ; trans = trans }
  }


open import bijection 
bij-Setoid :  {n : Level} → Setoid (Level.suc n) n
bij-Setoid {n}  = record {
      Carrier = Set n
    ; _≈_ = Bijection
    ; isEquivalence = bijIsEquivalence  -- record { sym = bi-sym _ _ ; refl = bid _ ; trans = bi-trans _ _ _ }
  }


libBijection :  {n m : Level} (R : Set n) (S : Set m) → Bijection R S  → Bijection1 (≡-Setoid R) (≡-Setoid S)
libBijection R S b = record {
     to = record { _⟨$⟩_   = λ x → fun→ b x ; cong = λ i=j → cong (fun→ b) i=j }
   ; bijective  = record {
         injective = λ {x} {y} eq → b→injection0 R S b x y eq
       ; surjective = record { from = record { _⟨$⟩_   = λ x → fun← b x ; cong = λ i=j → cong (fun← b) i=j }
          ; right-inverse-of = λ x → fiso→ b x }
      }
  }

fromBijection1 :  {n m : Level} (R : Set n) (S : Set m) → Bijection1 (≡-Setoid R) (≡-Setoid S) → Bijection R S  
fromBijection1 R S b = record {
      fun←  = Π._⟨$⟩_ (Surjective.from (Bijective.surjective (Bijection1.bijective b)))
    ; fun→  = Π._⟨$⟩_ (Bijection1.to b)
    ; fiso← = λ x → Bijective.injective (Bijection1.bijective b) (fb1 x)
    ; fiso→ =  Surjective.right-inverse-of  (Bijective.surjective (Bijection1.bijective b))
  } where
      --  fun← b x ≡ fun← b y → x ≡ y
      --  fun← (fun→ ( fun← x ))  ≡  fun← x
      --  fun→ ( fun← x )  ≡ x
     fb1 : (x : R) → Π._⟨$⟩_ (Bijection1.to b) (Surjective.from (Bijective.surjective (Bijection1.bijective b)) ⟨$⟩ (Bijection1.to b ⟨$⟩ x))  ≡ Π._⟨$⟩_ (Bijection1.to b) x
     fb1 x = begin
          Π._⟨$⟩_ (Bijection1.to b) (Surjective.from (Bijective.surjective (Bijection1.bijective b)) ⟨$⟩ (Bijection1.to b ⟨$⟩ x))
             ≡⟨ Surjective.right-inverse-of  (Bijective.surjective (Bijection1.bijective b)) _ ⟩
          Π._⟨$⟩_ (Bijection1.to b) x ∎ where open ≡-Reasoning

