{-# OPTIONS --allow-unsolved-metas #-}

open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.List hiding ( [_] )

module derive ( Σ : Set) ( eq? : (x y : Σ) → Dec (x ≡ y)) where

-- open import nfa
open import Data.Nat
-- open import Data.Nat hiding ( _<_ ; _>_ )
-- open import Data.Fin hiding ( _<_ )

open import finiteSet
open import FSetUtil
open import automaton
open import logic
open import regex

empty? : Regex  Σ → Bool
empty?  ε       = true
empty?  φ       = false
empty? (x *)    = true
empty? (x & y)  = empty? x /\ empty? y
empty? (x || y) = empty? x \/ empty? y
empty? < x >    = false

derivative0 :  Regex  Σ → Σ → Regex  Σ
derivative0 ε s = φ
derivative0 φ s = φ
derivative0 (x *) s = derivative0 x s & (x *)
derivative0 (x & y) s with empty? x
... | true =  (derivative0 x s & y) || derivative0 y s
... | false = derivative0 x s & y
derivative0 (x || y) s = derivative0 x s || derivative0 y s
derivative0 < x > s with eq? x s
... | yes _ = ε
... | no  _ = φ

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

open import Data.Fin

-- derivative generates   (x & y) || ... form. y and x part is a substerm of original regex
-- since subterm is finite, only finite number of state is negerated, if we normalize ||-list.

data subterm (r : Regex Σ) : Regex Σ → Set where
    sε   : subterm r ε
    sφ   : subterm r φ
    orig : subterm r r
    x&   : {x y : Regex Σ } → subterm r (x & y)  → subterm r x
    &y   : {x y : Regex Σ } → subterm r (x & y)  → subterm r y
    x|   : {x y : Regex Σ } → subterm r (x || y) → subterm r x
    |y   : {x y : Regex Σ } → subterm r (x || y) → subterm r y
    s*   : {x : Regex Σ }   → subterm r (x *)    → subterm r x
    s<_>   : (s : Σ) → subterm r < s > → subterm r < s >

record Subterm (r : Regex Σ) : Set where
  field
    subt : Regex Σ
    is-subt : subterm r subt

finsub : (r : Regex Σ ) → FiniteSet (Subterm r)
finsub ε = {!!}
finsub φ = {!!}
finsub (r *) = {!!}
finsub (r & r₁) = {!!}
finsub (r || r₁) = {!!}
finsub < x > = {!!}

finsubList : (r : Regex Σ ) → FiniteSet (Subterm r  ∧ Subterm r → Bool )
finsubList r = fin→ ( fin-∧ (finsub r) (finsub r) )

-- derivative is subset of Subterm r → Subterm r → Bool

der2ssb : {r : Regex Σ } → Derivative r → Subterm r ∧ Subterm r → Bool
der2ssb = {!!}

-- we cannot say this, because Derivative is redundant
-- der2inject : {r : Regex Σ } → (x y : Derivative r ) → ( ( s t : Subterm r ∧ Subterm r ) → der2ssb x s ≡ der2ssb y t ) → x ≡ y

-- this does not work, becuase it depends on input sequences
-- finite-derivative : (r : Regex  Σ) → FiniteSet Σ  → FiniteSet (Derivative r) 

-- in case of automaton, number of derivative is limited by iteration of input length, so it is finite.

regex→automaton : (r : Regex   Σ) → Automaton (Derivative r) Σ
regex→automaton r = record { δ = λ d s → record { state = derivative (state d) s ; is-derived = derive-step d s} ; aend = λ d → empty? (state d) }  where
    derive-step : (d0 : Derivative r) → (s : Σ) → regex-states r (derivative (state d0) s)
    derive-step d0 s = derive (is-derived d0) s

