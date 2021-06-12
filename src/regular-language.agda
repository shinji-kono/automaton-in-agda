module regular-language where

open import Level renaming ( suc to Suc ; zero to Zero )
open import Data.List 
open import Data.Nat hiding ( _≟_ )
open import Data.Fin hiding ( _+_ )
open import Data.Empty 
open import Data.Unit 
open import Data.Product
-- open import Data.Maybe
open import  Relation.Nullary
open import  Relation.Binary.PropositionalEquality hiding ( [_] )
open import logic
open import nat
open import automaton

language : { Σ : Set } → Set
language {Σ} = List Σ → Bool

language-L : { Σ : Set } → Set
language-L {Σ} = List (List Σ)

open Automaton

record RegularLanguage ( Σ : Set ) : Set (Suc Zero) where
   field
      states : Set 
      astart : states 
      automaton : Automaton states Σ
   contain : List Σ → Bool
   contain x = accept automaton astart x

Union : {Σ : Set} → ( A B : language {Σ} ) → language {Σ}
Union {Σ} A B x = (A x ) \/ (B x)

split : {Σ : Set} → (List Σ → Bool)
      → ( List Σ → Bool) → List Σ → Bool
split x y  [] = x [] /\ y []
split x y (h  ∷ t) = (x [] /\ y (h  ∷ t)) \/
  split (λ t1 → x (  h ∷ t1 ))  (λ t2 → y t2 ) t

Concat : {Σ : Set} → ( A B : language {Σ} ) → language {Σ}
Concat {Σ} A B = split A B

{-# TERMINATING #-}
Star : {Σ : Set} → ( A : language {Σ} ) → language {Σ}
Star {Σ} A = split A ( Star {Σ} A )

open import automaton-ex

test-AB→split : {Σ : Set} → {A B : List In2 → Bool} → split A B ( i0 ∷ i1 ∷ i0 ∷ [] ) ≡ (
       ( A [] /\ B ( i0 ∷ i1 ∷ i0 ∷ [] ) ) \/ 
       ( A ( i0 ∷ [] ) /\ B ( i1 ∷ i0 ∷ [] ) ) \/ 
       ( A ( i0 ∷ i1 ∷ [] ) /\ B ( i0 ∷ [] ) ) \/
       ( A ( i0 ∷ i1 ∷ i0 ∷ [] ) /\ B  []  ) 
   )
test-AB→split {_} {A} {B} = refl

open RegularLanguage 
isRegular : {Σ : Set} → (A : language {Σ} ) → ( x : List Σ ) → (r : RegularLanguage Σ ) → Set
isRegular A x r = A x ≡ contain r x 

-- postulate 
--   fin-× : {A B : Set} → { a b : ℕ } → FiniteSet A {a} → FiniteSet B {b} → FiniteSet (A × B) {a * b}

M-Union : {Σ : Set} → (A B : RegularLanguage Σ ) → RegularLanguage Σ
M-Union {Σ} A B = record {
       states =  states A × states B
     ; astart = ( astart A , astart B )
     ; automaton = record {
             δ = λ q x → ( δ (automaton A) (proj₁ q) x , δ (automaton B) (proj₂ q) x )
           ; aend = λ q → ( aend (automaton A) (proj₁ q) \/ aend (automaton B) (proj₂ q) )
        }
   }  

closed-in-union :  {Σ : Set} → (A B : RegularLanguage Σ ) → ( x : List Σ ) → isRegular (Union (contain A) (contain B)) x ( M-Union A B )
closed-in-union A B [] = lemma where
   lemma : aend (automaton A) (astart A) \/ aend (automaton B) (astart B) ≡
           aend (automaton A) (astart A) \/ aend (automaton B) (astart B)
   lemma = refl
closed-in-union {Σ} A B ( h ∷ t ) = lemma1 t ((δ (automaton A) (astart A) h)) ((δ (automaton B) (astart B) h)) where
   lemma1 : (t : List Σ) → (qa : states A ) → (qb : states B ) → 
     accept (automaton A) qa t \/ accept (automaton B) qb  t
       ≡ accept (automaton (M-Union A B)) (qa , qb) t
   lemma1 [] qa qb = refl
   lemma1 (h ∷ t ) qa qb = lemma1 t ((δ (automaton A) qa h)) ((δ (automaton B) qb h))

