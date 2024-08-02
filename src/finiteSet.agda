{-# OPTIONS --cubical-compatible --safe #-}
module finiteSet  where

open import Data.Nat hiding ( _≟_ )
open import Data.Fin renaming ( _<_ to _<<_ ) hiding (_≤_)
-- open import Data.Fin.Properties  hiding ( ≤-refl )
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import logic
open import nat
open import Data.Nat.Properties hiding ( _≟_ )

-- open import Relation.Binary.HeterogeneousEquality as HE using (_≅_ ) 

record FiniteSet ( Q : Set ) : Set  where
     field
        finite : ℕ
        Q←F : Fin finite → Q
        F←Q : Q → Fin finite
        finiso→ : (q : Q) → Q←F ( F←Q q ) ≡ q
        finiso← : (f : Fin finite ) → F←Q ( Q←F f ) ≡ f
     exists1 : (m : ℕ ) → m Data.Nat.≤ finite → (Q → Bool) → Bool
     exists1  zero  _ _ = false
     exists1 ( suc m ) m<n p = p (Q←F (fromℕ< {m} {finite} m<n)) \/ exists1 m (<to≤ m<n) p
     exists : ( Q → Bool ) → Bool
     exists p = exists1 finite ≤-refl p 

     open import Data.List
     list1 : (m : ℕ ) → m Data.Nat.≤ finite → (Q → Bool) → List Q 
     list1  zero  _ _ = []
     list1 ( suc m ) m<n p with p (Q←F (fromℕ< {m} {finite} m<n)) in eq
     ... | true = Q←F (fromℕ< {m} {finite} m<n) ∷ list1 m (<to≤ m<n) p
     ... | false = list1 m (<to≤ m<n) p
     to-list : ( Q → Bool ) → List Q 
     to-list p = list1 finite ≤-refl p 

     equal? : Q → Q → Bool
     equal? q0 q1 with <-cmp (toℕ (F←Q q0 )) (toℕ ( F←Q q1))
     ... | tri< a ¬b ¬c = false
     ... | tri≈ ¬a b ¬c = true
     ... | tri> ¬a ¬b c = false
     injectQ←F : (p q : Fin  finite) → Q←F p ≡ Q←F q → p ≡ q 
     injectQ←F p q eq = subst₂ (λ j k → j ≡ k ) (finiso←  _) (finiso← _) (cong F←Q eq)
     injectF←Q : (p q : Q) → F←Q p ≡ F←Q q → p ≡ q 
     injectF←Q p q eq = subst₂ (λ j k → j ≡ k ) (finiso→  _) (finiso→ _) (cong Q←F eq)

--
-- we cannot use (Q : P → Bool) → FiniteSet P , because we need functional extensionality which is not available in cubical compatability mode
--   of course we can Cubial Agda
--
record FiniteSetF ( Q F : Set ) : Set  where
     field
        fin : FiniteSet F
        Q←F : F → Q → Bool
        F←Q : (Q → Bool) → F
        finiso→ : (f : Q → Bool ) → (q : Q) → Q←F ( F←Q f ) q ≡ f q
        finiso← : (f : F ) {g : Q → Bool} → ((q : Q) → g q ≡ Q←F f q) → F←Q g  ≡ f 
     finite = FiniteSet.finite fin
     exists1 : (m : ℕ ) → m Data.Nat.≤ finite  → ((Q → Bool) → Bool) → Bool
     exists1 m lt f  = FiniteSet.exists1 fin m lt (λ q → f (Q←F q))
     exists : ( (Q → Bool) → Bool ) → Bool
     exists f = FiniteSet.exists fin (λ q → f (Q←F q))

     open import Data.List
     list1 : (m : ℕ ) → m Data.Nat.≤ finite → ((Q → Bool) → Bool) → List (Q → Bool) 
     list1 m lt f = map Q←F (FiniteSet.list1 fin m lt (λ q → f (Q←F q)) )
     to-list : ( (Q → Bool) → Bool ) → List (Q → Bool)
     to-list f = map Q←F ( FiniteSet.to-list fin (λ q → f (Q←F q)) )

     equal? : (Q → Bool) → (Q → Bool) → Bool
     equal? f g = FiniteSet.equal? fin (F←Q f) (F←Q g)

     injective-Q←F : (p q : F) → ((x : Q) → Q←F p x ≡ Q←F q x) → p ≡ q 
     injective-Q←F p q eq = begin
         p ≡⟨ sym (finiso←  p (λ _ → refl) ) ⟩
         F←Q ( Q←F p ) ≡⟨ finiso←  q eq ⟩
         q ∎ where open ≡-Reasoning
     injective-F←Q : (f g : Q → Bool ) → F←Q f ≡ F←Q g → (q : Q) → f q ≡ g q
     injective-F←Q f g eq q = begin
         f q ≡⟨ sym (finiso→ f q)  ⟩
         Q←F ( F←Q f ) q ≡⟨ cong (λ x → Q←F x q ) eq ⟩
         Q←F ( F←Q g ) q ≡⟨ finiso→ g q ⟩
         g q ∎ where open ≡-Reasoning

     injective-Q←F→iso : ( (p q : F) → ((x : Q) → Q←F p x ≡ Q←F q x) → p ≡ q  ) → (f : F ) {g : Q → Bool} → ((q : Q) → g q ≡ Q←F f q) → F←Q g  ≡ f 
     injective-Q←F→iso inj f {g} EQ = inj (F←Q g) f (λ x → begin 
         Q←F (F←Q g) x ≡⟨ finiso→ _ _  ⟩  
         g x ≡⟨ EQ x ⟩  
         Q←F f x  ∎ ) where open ≡-Reasoning





