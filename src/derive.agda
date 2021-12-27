{-# OPTIONS --allow-unsolved-metas #-}

open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.List hiding ( [_] )
open import finiteSet

module derive ( Σ : Set) ( fin : FiniteSet Σ ) ( eq? : (x y : Σ) → Dec (x ≡ y)) where

-- open import nfa
open import Data.Nat
-- open import Data.Nat hiding ( _<_ ; _>_ )
-- open import Data.Fin hiding ( _<_ )
open import finiteSetUtil
open import automaton
open import logic
open import regex
open FiniteSet

-- whether a regex accepts empty input
--
empty? : Regex  Σ → Bool
empty?  ε       = true
empty?  φ       = false
empty? (x *)    = true
empty? (x & y)  = empty? x /\ empty? y
empty? (x || y) = empty? x \/ empty? y
empty? < x >    = false

derivative :  Regex  Σ → Σ → Regex  Σ
derivative ε s = φ
derivative φ s = φ
derivative (x *) s with derivative x s
... | ε = x *
... | φ = φ
... | t = t & (x *)
derivative (x & y) s with empty? x
... | true with derivative x s | derivative y s
... | ε | φ = φ
... | ε | t = y || t
... | φ | t = t
... | x1 | φ = x1 & y
... | x1 | y1 = (x1 & y) || y1
derivative (x & y) s | false with derivative x s 
... | ε = y
... | φ = φ
... | t = t & y
derivative (x || y) s with derivative x s | derivative y s
... | φ | y1 = y1
... | x1 | φ = x1
... | x1 | y1 = x1 || y1
derivative < x > s with eq? x s
... | yes _ = ε
... | no  _ = φ

data regex-states (x : Regex  Σ ) : Regex  Σ → Set where
    unit   : regex-states x x
    derive : { y : Regex  Σ } → regex-states x y → (s : Σ)  → regex-states x ( derivative y s )

record Derivative (x : Regex  Σ ) : Set where
    field
       state : Regex  Σ
       is-derived : regex-states x state

open Derivative

open import Data.Fin hiding (_<_)

-- derivative generates   (x & y) || ... form. y and x part is a substerm of original regex
-- since subterm is finite, only finite number of state is generated for each operator 
-- this does not work, becuase it depends on input sequences
-- finite-derivative : (r : Regex  Σ) → FiniteSet Σ  → FiniteSet (Derivative r) 
-- order : Regex  Σ → ℕ
-- decline-derive : (x : Regex Σ ) (i : Σ ) → 0 < order x → order (derivative x i) < order x 
--    is not so easy
-- in case of automaton, number of derivative is limited by iteration of input length, so it is finite.
-- so we cannot say derived automaton is finite i.e. regex-match is regular language now

regex→automaton : (r : Regex   Σ) → Automaton (Derivative r) Σ
regex→automaton r = record { δ = λ d s → record { state = derivative (state d) s ; is-derived = derive-step d s} ; aend = λ d → empty? (state d) }  where
    derive-step : (d0 : Derivative r) → (s : Σ) → regex-states r (derivative (state d0) s)
    derive-step d0 s = derive (is-derived d0) s

regex-match : (r : Regex   Σ) →  (List Σ) → Bool
regex-match ex is = accept ( regex→automaton ex ) record { state =  ex ; is-derived = unit } is 

open import Relation.Binary.Definitions

cmp-regex : (x y : Regex Σ) → Dec ( x ≡ y )
cmp-regex ε ε = yes refl
cmp-regex ε φ = no (λ ())
cmp-regex ε (y *) = no (λ ())
cmp-regex ε (y & y₁) = no (λ ())
cmp-regex ε (y || y₁) = no (λ ())
cmp-regex ε < x > = no (λ ())
cmp-regex φ ε = no (λ ())
cmp-regex φ φ = yes refl
cmp-regex φ (y *) =  no (λ ())
cmp-regex φ (y & y₁) =  no (λ ())
cmp-regex φ (y || y₁) =  no (λ ())
cmp-regex φ < x > =  no (λ ())
cmp-regex (x *) ε =  no (λ ())
cmp-regex (x *) φ =  no (λ ())
cmp-regex (x *) (y *) with cmp-regex x y
... | yes refl = yes refl
... | no ne = no (λ x → ne (cmp1 x)) where
   cmp1 : (x *) ≡ (y *) → x ≡ y
   cmp1 refl = refl
cmp-regex (x *) (y & y₁) = no (λ ())
cmp-regex (x *) (y || y₁) = no (λ ())
cmp-regex (x *) < x₁ > = no (λ ())
cmp-regex (x & x₁) ε = no (λ ())
cmp-regex (x & x₁) φ = no (λ ())
cmp-regex (x & x₁) (y *) = no (λ ())
cmp-regex (x & x₁) (y & y₁) with cmp-regex x y | cmp-regex x₁ y₁ 
... | yes refl | yes refl = yes refl
... | no ne | _ = no (λ x → ne (cmp1 x)) where
   cmp1 :  x & x₁ ≡ y & y₁ → x ≡ y
   cmp1 refl = refl
... | _ | no ne  = no (λ x → ne (cmp1 x)) where
   cmp1 :  x & x₁ ≡ y & y₁ → x₁ ≡ y₁
   cmp1 refl = refl
cmp-regex (x & x₁) (y || y₁) = no (λ ())
cmp-regex (x & x₁) < x₂ > = no (λ ())
cmp-regex (x || x₁) ε = no (λ ())
cmp-regex (x || x₁) φ = no (λ ())
cmp-regex (x || x₁) (y *) = no (λ ())
cmp-regex (x || x₁) (y & y₁) = no (λ ())
cmp-regex (x || x₁) (y || y₁) with cmp-regex x y | cmp-regex x₁ y₁ 
... | yes refl | yes refl = yes refl
... | no ne | _ = no (λ x → ne (cmp1 x)) where
   cmp1 :  x || x₁ ≡ y || y₁ → x ≡ y
   cmp1 refl = refl
... | _ | no ne  = no (λ x → ne (cmp1 x)) where
   cmp1 :  x || x₁ ≡ y || y₁ → x₁ ≡ y₁
   cmp1 refl = refl
cmp-regex (x || x₁) < x₂ > = no (λ ())
cmp-regex < x > ε = no (λ ())
cmp-regex < x > φ = no (λ ())
cmp-regex < x > (y *) = no (λ ())
cmp-regex < x > (y & y₁) = no (λ ())
cmp-regex < x > (y || y₁) = no (λ ())
cmp-regex < x > < x₁ > with equal? fin x x₁ | inspect ( equal? fin x ) x₁
... | false | record { eq = eq } = no (λ x → ¬-bool eq (cmp1 x)) where
   cmp1 :  < x > ≡ < x₁ > →  equal? fin x x₁ ≡ true 
   cmp1 refl = equal?-refl fin
... | true | record { eq = eq } with equal→refl fin eq
... | refl = yes refl

insert : List (Regex Σ) → (Regex Σ) → List (Regex Σ) 
insert [] k = k ∷ []
insert (x ∷ t) k with cmp-regex k x
... | no n = x ∷ (insert t k) 
... | yes y = x ∷ t

regex-derive : List (Regex Σ) → List (Regex Σ)
regex-derive t = regex-derive0 t t where
   regex-derive1 : Regex Σ → List Σ → List (Regex Σ) → List (Regex Σ)
   regex-derive1 x [] t = t
   regex-derive1 x (i ∷ t) r =  regex-derive1 x t (insert r (derivative x i))
   regex-derive0 :  List (Regex Σ)  → List (Regex Σ) → List (Regex Σ)
   regex-derive0 [] t = t
   regex-derive0 (x ∷ r) t = regex-derive0 r (regex-derive1 x (to-list fin (λ _ → true)) t) 

--
-- if (Derivative r is finite,  regex→automaton is finite
--
drive-is-finite : (r : Regex   Σ) → FiniteSet (Derivative r) 
drive-is-finite ε = {!!}
drive-is-finite φ = {!!}
drive-is-finite (r *) = {!!} where
   d1 :  FiniteSet (Derivative r )
   d1 = drive-is-finite r
drive-is-finite (r & r₁) = {!!}
drive-is-finite (r || r₁) = {!!}
drive-is-finite < x > = {!!}

