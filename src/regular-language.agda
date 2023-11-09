{-# OPTIONS --cubical-compatible --safe #-}

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

Union : {Σ : Set} → ( A B : language {Σ} ) → language {Σ}
Union {Σ} A B x = A x  \/ B x

split : {Σ : Set} → (x y : language {Σ} ) → language {Σ}
split x y  [] = x [] /\ y []
split x y (h  ∷ t) = (x [] /\ y (h  ∷ t)) \/
  split (λ t1 → x (  h ∷ t1 ))  (λ t2 → y t2 ) t

Concat : {Σ : Set} → ( A B : language {Σ} ) → language {Σ}
Concat {Σ} A B = split A B

-- {-# TERMINATING #-}
-- Star1 : {Σ : Set} → ( A : language {Σ} ) → language {Σ}
-- Star1 {Σ} A [] = true
-- Star0 {Σ} A (h ∷ t) = split A ( Star1 {Σ} A ) (h ∷ t)

-- Terminating version of Star1
--
repeat : {Σ : Set} → (x : List Σ → Bool) → (y : List Σ ) → Bool 
repeat2 : {Σ : Set} → (x : List Σ → Bool) → (pre y : List Σ ) → Bool
repeat2 x pre [] = false
repeat2 x pre (h ∷ y) = 
   (x (pre ++ (h ∷ [])) /\ repeat x y )
   \/ repeat2 x (pre ++ (h ∷ [])) y 

repeat {Σ} x [] = true
repeat {Σ} x (h ∷ y) = repeat2 x [] (h ∷ y) 

Star : {Σ : Set} → (x : List Σ → Bool) → (y : List Σ ) → Bool 
Star {Σ} x y = repeat x y

-- We have to prove definitions of Concat and Star are equivalent to the set theoretic definitions

-- 1.  A ∪ B = { x | x ∈ A \/ x ∈ B }
-- 2.  A ∘ B = { x | ∃ y ∈ A, z ∈ B, x = y ++ z }
-- 3.  A* = { x | ∃ n ∈ ℕ, y1, y2, ..., yn ∈ A, x = y1 ++ y2 ++ ... ++ yn }

-- lemma-Union : {Σ : Set} → ( A B : language {Σ} ) → ( x : List Σ ) → Union A B x ≡ ( A x \/ B x )
-- lemma-Union = ?

-- lemma-Concat : {Σ : Set} → ( A B : language {Σ} ) → ( x : List Σ ) 
--    → Concat A B x ≡ ( ∃ λ y → ∃ λ z → A y /\ B z /\ x ≡ y ++ z )
-- lemma-Concat = ?

open import automaton-ex

test-AB→split : {Σ : Set} → {A B : List In2 → Bool} → split A B ( i0 ∷ i1 ∷ i0 ∷ [] ) ≡ (
       ( A [] /\ B ( i0 ∷ i1 ∷ i0 ∷ [] ) ) \/ 
       ( A ( i0 ∷ [] ) /\ B ( i1 ∷ i0 ∷ [] ) ) \/ 
       ( A ( i0 ∷ i1 ∷ [] ) /\ B ( i0 ∷ [] ) ) \/
       ( A ( i0 ∷ i1 ∷ i0 ∷ [] ) /\ B  []  ) 
   )
test-AB→split {_} {A} {B} = refl

star-nil : {Σ : Set} → ( A : language {Σ} ) → Star A [] ≡ true
star-nil A = refl

open Automaton
open import finiteSet
open import finiteSetUtil

record RegularLanguage ( Σ : Set ) : Set (Suc Zero) where
   field
      states : Set
      astart : states
      afin : FiniteSet states
      automaton : Automaton states Σ
   contain : List Σ → Bool
   contain x = accept automaton astart x

open RegularLanguage

isRegular : {Σ : Set} → (A : language {Σ} ) → ( x : List Σ ) → (r : RegularLanguage Σ ) → Set
isRegular A x r = A x ≡ contain r x

RegularLanguage-is-language : { Σ : Set } → RegularLanguage Σ  → language {Σ} 
RegularLanguage-is-language {Σ} R = RegularLanguage.contain R 

RegularLanguage-is-language' : { Σ : Set } → RegularLanguage Σ  → List Σ  → Bool
RegularLanguage-is-language' {Σ} R x = accept (automaton R) (astart R) x where
   open RegularLanguage

--  a language is implemented by an automaton

-- postulate 
--   fin-× : {A B : Set} → { a b : ℕ } → FiniteSet A {a} → FiniteSet B {b} → FiniteSet (A × B) {a * b}

M-Union : {Σ : Set} → (A B : RegularLanguage Σ ) → RegularLanguage Σ
M-Union {Σ} A B = record {
       states =  states A × states B
     ; astart = ( astart A , astart B )
     ; afin = fin-× (afin A) (afin B)
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


       
record Split {Σ : Set} (A : List Σ → Bool ) ( B : List Σ → Bool ) (x :  List Σ ) : Set where
    field
        sp0 sp1 : List Σ
        sp-concat : sp0 ++ sp1 ≡ x
        prop0 : A sp0 ≡ true
        prop1 : B sp1 ≡ true

open Split

list-empty++ : {Σ : Set} → (x y : List Σ) → x ++ y ≡ [] → (x ≡ [] ) ∧ (y ≡ [] )
list-empty++ [] [] refl = record { proj1 = refl ; proj2 = refl }
list-empty++ [] (x ∷ y) ()
list-empty++ (x ∷ x₁) y ()

open _∧_

open import Relation.Binary.PropositionalEquality hiding ( [_] )

c-split-lemma : {Σ : Set} → (A B : List Σ → Bool ) → (h : Σ) → ( t : List Σ ) → split A B (h ∷ t ) ≡ true
   → ( ¬ (A [] ≡ true )) ∨ ( ¬ (B ( h ∷ t ) ≡ true) )
   → split (λ t1 → A (h ∷ t1)) B t ≡ true
c-split-lemma {Σ} A B h t eq p = sym ( begin
      true
  ≡⟨  sym eq  ⟩
      split A B (h ∷ t ) 
  ≡⟨⟩
      A [] /\ B (h ∷ t) \/ split (λ t1 → A (h ∷ t1)) B t
  ≡⟨  cong ( λ k → k \/ split (λ t1 → A (h ∷ t1)) B t ) (lemma-p p ) ⟩
      false \/ split (λ t1 → A (h ∷ t1)) B t
  ≡⟨ bool-or-1 refl ⟩
      split (λ t1 → A (h ∷ t1)) B t
  ∎ ) where
     open ≡-Reasoning 
     lemma-p : ( ¬ (A [] ≡ true )) ∨ ( ¬ (B ( h ∷ t ) ≡ true) ) → A [] /\ B (h ∷ t) ≡ false
     lemma-p (case1 ¬A ) = bool-and-1 ( ¬-bool-t ¬A )
     lemma-p (case2 ¬B ) = bool-and-2 ( ¬-bool-t ¬B )

split→AB :  {Σ : Set} → (A B : List Σ → Bool ) → ( x : List Σ ) → split A B x ≡ true → Split A B x
split→AB {Σ} A B [] eq with bool-≡-? (A []) true | bool-≡-? (B []) true 
split→AB {Σ} A B [] eq | yes eqa | yes eqb = 
    record { sp0 = [] ; sp1 = [] ; sp-concat = refl ; prop0 = eqa ; prop1 = eqb }
split→AB {Σ} A B [] eq | yes p | no ¬p = ⊥-elim (lemma-∧-1 eq (¬-bool-t ¬p ))
split→AB {Σ} A B [] eq | no ¬p | t = ⊥-elim (lemma-∧-0 eq (¬-bool-t ¬p ))
split→AB {Σ} A B (h ∷ t ) eq with bool-≡-? (A []) true | bool-≡-? (B (h ∷ t )) true
... | yes px | yes py = record { sp0 = [] ; sp1 = h ∷ t ; sp-concat = refl ; prop0 = px ; prop1 = py }
... | no px | _ with split→AB (λ t1 → A ( h ∷ t1 )) B t (c-split-lemma A B h t eq (case1 px) )
... | S = record { sp0 = h ∷ sp0 S  ; sp1 = sp1 S ; sp-concat = cong ( λ k → h ∷ k) (sp-concat S) ; prop0 = prop0 S ; prop1 = prop1 S }
split→AB {Σ} A B (h ∷ t ) eq  | _ | no px with split→AB (λ t1 → A ( h ∷ t1 )) B t (c-split-lemma A B h t eq (case2 px) )
... | S = record { sp0 = h ∷ sp0 S  ; sp1 = sp1 S ; sp-concat = cong ( λ k → h ∷ k) (sp-concat S) ; prop0 = prop0 S ; prop1 = prop1 S }

AB→split :  {Σ : Set} → (A B : List Σ → Bool ) → ( x y : List Σ ) → A x ≡ true → B y ≡ true → split A B (x ++ y ) ≡ true
AB→split {Σ} A B [] [] eqa eqb = begin
       split A B [] 
     ≡⟨⟩
       A [] /\ B []
     ≡⟨ cong₂ (λ j k → j /\ k ) eqa eqb ⟩
      true
     ∎  where open ≡-Reasoning
AB→split {Σ} A B [] (h ∷ y ) eqa eqb = begin
      split A B (h ∷ y )
     ≡⟨⟩
      A [] /\ B (h ∷ y) \/ split (λ t1 → A (h ∷ t1)) B y
     ≡⟨ cong₂ (λ j k → j /\ k \/ split (λ t1 → A (h ∷ t1)) B y ) eqa eqb ⟩
      true /\ true \/ split (λ t1 → A (h ∷ t1)) B y
     ≡⟨⟩
      true \/ split (λ t1 → A (h ∷ t1)) B y
     ≡⟨⟩
      true
     ∎  where open ≡-Reasoning
AB→split {Σ} A B (h ∷ t) y eqa eqb = begin
       split A B ((h ∷ t) ++ y)  
     ≡⟨⟩
       A [] /\ B (h ∷ t ++ y) \/ split (λ t1 → A (h ∷ t1)) B (t ++ y)
     ≡⟨ cong ( λ k →  A [] /\ B (h ∷ t ++ y) \/ k ) (AB→split {Σ} (λ t1 → A (h ∷ t1)) B t y eqa eqb ) ⟩
       A [] /\ B (h ∷ t ++ y) \/ true
     ≡⟨ bool-or-3 ⟩
      true
     ∎  where open ≡-Reasoning

