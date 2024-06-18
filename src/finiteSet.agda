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
     list1 ( suc m ) m<n p with bool-≡-? (p (Q←F (fromℕ< {m} {finite} m<n))) true
     ... | yes _ = Q←F (fromℕ< {m} {finite} m<n) ∷ list1 m (<to≤ m<n) p
     ... | no  _ = list1 m (<to≤ m<n) p
     to-list : ( Q → Bool ) → List Q 
     to-list p = list1 finite ≤-refl p 

     equal? : Q → Q → Bool
     equal? q0 q1 with F←Q q0 ≟ F←Q q1
     ... | yes p = true
     ... | no ¬p = false

record FiniteSetF ( Q : Set ) : Set  where
     field
        finite : ℕ
        Q←F : Fin finite → Q → Bool
        F←Q : (Q → Bool) → Fin finite
        finiso→ : (f : Q → Bool ) → (q : Q) → Q←F ( F←Q f ) q ≡ f q
        finiso← : (f : Fin finite ) → F←Q ( Q←F f )  ≡ f 

