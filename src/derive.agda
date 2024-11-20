{-# OPTIONS --cubical-compatible --safe  #-}
-- {-# OPTIONS --allow-unsolved-metas #---}

open import Relation.Binary.PropositionalEquality hiding ( [_] )
-- open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.List hiding ( [_] )
open import Data.Empty 
open import finiteSet
-- open import finiteFunc
open import fin
open import logic

module derive ( Σ : Set) ( fin : FiniteSet Σ ) ( eq? : (x y : Σ) → Dec0 (x ≡ y)) where

open import automaton
open import regex
open import regular-language

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
... | ε | t = t || y
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
... | yes0 _ = ε
... | no0  _ = φ

data regex-states (x : Regex  Σ ) : Regex  Σ → Set where
    unit   : { z : Regex Σ} → z ≡ x → regex-states x z
    derive : { y z : Regex  Σ } → regex-states x y → (s : Σ) → z ≡  derivative y s → regex-states x z 

record Derivative (x : Regex  Σ ) : Set where
    field
       state : Regex  Σ
       is-derived : regex-states x state

open Derivative

derive-step : (r : Regex   Σ) (d0 : Derivative r) → (s : Σ) → regex-states r (derivative (state d0) s)
derive-step r d0 s = derive (is-derived d0) s refl

regex→automaton : (r : Regex   Σ) → Automaton (Derivative r) Σ
regex→automaton r = record { δ = λ d s → 
        record { state = derivative (state d) s ; is-derived = derive (is-derived d) s refl } 
   ; aend = λ d → empty? (state d) }  

regex-match : (r : Regex   Σ) →  (List Σ) → Bool
regex-match ex is = accept ( regex→automaton ex ) record { state =  ex ; is-derived = unit refl } is 

-- open import Relation.Binary.HeterogeneousEquality as HE using (_≅_ ) 

-- open import nfa
open import Data.Nat hiding (eq?)
open import Data.Nat.Properties hiding ( eq? )
open import nat
open import finiteSetUtil
open FiniteSet
open import Data.Fin hiding (_<_ ; _≤_ ; pred )

-- finiteness of derivative 
--    term generate   x & y   for each * and & only once
--      rank : Regex → ℕ 
--   r₀ & r₁ ... r
--   generated state is a subset of the term set

open import Relation.Binary.Definitions

open _∧_ 

right& : {r r₁ x : Regex Σ} → r & r₁ ≡ x → Regex Σ
right& {r} {r₁} refl = r₁

left& : {r r₁ x : Regex Σ} → r & r₁ ≡ x → Regex Σ
left& {r} {r₁} refl = r
-- 
-- fb20 : {r s r₁ s₁ : Regex Σ} → r & r₁ ≡ s & s₁ → (r ≡ s ) ∧  (r₁ ≡ s₁ )
-- fb20  refl = ?
-- 
-- fb21 : {r s r₁ s₁ : Regex Σ} → r || r₁ ≡ s || s₁ → (r ≡ s ) ∧  (r₁ ≡ s₁ )
-- fb21  refl eq = ?
-- 
-- rg-eq? : (r s : Regex Σ) → Dec0 ( r ≡ s )
-- rg-eq? ε ε = yes0 refl
-- rg-eq? ε φ = no0 (λ ())
-- rg-eq? ε (s *) = no0 (λ ())
-- rg-eq? ε (s & s₁) = no0 (λ ())
-- rg-eq? ε (s || s₁) = no0 (λ ())
-- rg-eq? ε < x > = no0 (λ ())
-- rg-eq? φ ε = no0 (λ ())
-- rg-eq? φ φ = yes0 refl
-- rg-eq? φ (s *) = no0 (λ ())
-- rg-eq? φ (s & s₁) = no0 (λ ())
-- rg-eq? φ (s || s₁) = no0 (λ ())
-- rg-eq? φ < x > = no0 (λ ())
-- rg-eq? (r *) ε = no0 (λ ())
-- rg-eq? (r *) φ = no0 (λ ())
-- rg-eq? (r *) (s *) with rg-eq? r s
-- ... | yes0 eq = yes0 ( cong (_*) eq)
-- ... | no0 ne = no0 (λ eq → ne (fb10 eq) ) where
--      fb10 : {r s : Regex Σ} → (r *) ≡ (s *) → r ≡ s 
--      fb10  = ?
-- rg-eq? (r *) (s & s₁) = no0 (λ ())
-- rg-eq? (r *) (s || s₁) = no0 (λ ())
-- rg-eq? (r *) < x > = no0 (λ ())
-- rg-eq? (r & r₁) ε = no0 (λ ())
-- rg-eq? (r & r₁) φ = no0 (λ ())
-- rg-eq? (r & r₁) (s *) = no0 (λ ())
-- rg-eq? (r & r₁) (s & s₁) with rg-eq? r s | rg-eq? r₁ s₁
-- ... | yes0 y | yes0 y₁ = yes0 ( cong₂ _&_ y y₁)
-- ... | yes0 y | no0 n  = no0 (λ eq → n (proj2 (fb20 eq) ))
-- ... | no0 n  | yes0 y = no0 (λ eq → n (proj1 (fb20 eq) ))
-- ... | no0 n  | no0 n₁ = no0 (λ eq → n (proj1 (fb20 eq) ))
-- rg-eq? (r & r₁) (s || s₁) = no0 (λ ())
-- rg-eq? (r & r₁) < x > = no0 (λ ())
-- rg-eq? (r || r₁) ε = no0 (λ ())
-- rg-eq? (r || r₁) φ = no0 (λ ())
-- rg-eq? (r || r₁) (s *) = no0 (λ ())
-- rg-eq? (r || r₁) (s & s₁) = no0 (λ ())
-- rg-eq? (r || r₁) (s || s₁) with rg-eq? r s | rg-eq? r₁ s₁
-- ... | yes0 y | yes0 y₁ = yes0 ( cong₂ _||_ y y₁)
-- ... | yes0 y | no0 n  = no0 (λ eq → n (proj2 (fb21 eq) ))
-- ... | no0 n  | yes0 y = no0 (λ eq → n (proj1 (fb21 eq) ))
-- ... | no0 n  | no0 n₁ = no0 (λ eq → n (proj1 (fb21 eq) ))
-- rg-eq? (r || r₁) < x > = no0 (λ ())
-- rg-eq? < x > ε = no0 (λ ())
-- rg-eq? < x > φ = no0 (λ ())
-- rg-eq? < x > (s *) = no0 (λ ())
-- rg-eq? < x > (s & s₁) = no0 (λ ())
-- rg-eq? < x > (s || s₁) = no0 (λ ())
-- rg-eq? < x > < x₁ > with eq? x x₁
-- ... | yes0 y = yes0 (cong <_> y)
-- ... | no0 n = no0 (λ eq → n (fb11 eq))   where
--      fb11 : < x > ≡ < x₁ > → x ≡ x₁
--      fb11 = ?
-- 
-- rank : (r : Regex Σ) → ℕ
-- rank ε = 0
-- rank φ = 0
-- rank (r *) = suc (rank r)
-- rank (r & r₁) = suc (max (rank r) (rank r₁))
-- rank (r || r₁) = max (rank r) (rank r₁)
-- rank < x > = 0
-- 
-- -- finiteness of derivative 
-- --    term generate   ( a₀ & a₁ ... & a ) || ...
-- --    a i is a subterm of r 
-- --      rank a i < rank a i+1 ≤ rank r
-- 
-- --
-- -- s is subterm of r
-- --
-- data SB : (r s : Regex Σ) → Set where
--     sε  : SB ε ε
--     sφ  : SB φ φ
--     s<> : {s : Σ} → SB < s >  < s > 
--     sub|1  : {x y z : Regex Σ} → SB x z → SB (x || y) z
--     sub|2  : {x y z : Regex Σ} → SB y z → SB (x || y) z
--     sub*   : {x y : Regex Σ} → SB x y  → SB (x *) y
--     sub&1  : (x y z : Regex Σ) → SB x z → SB (x & y) z
--     sub&2  : (x y z : Regex Σ) → SB y z → SB (x & y) z
-- --    sub*&  : (x y : Regex Σ)   → rank x < rank y  → SB y x       → SB (y *)   (x & (y *)) 
-- --    sub&&  : (x y z : Regex Σ) → rank z < rank x  → SB (x & y) z → SB (x & y) (z & y) 
-- 
-- fin-derive : (r : Regex Σ) → FiniteSet (Derivative r)
-- fin-derive r = ?
-- 
