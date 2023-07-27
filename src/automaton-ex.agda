{-# OPTIONS --allow-unsolved-metas #-}
module automaton-ex where

open import Data.Nat
open import Data.List
open import Data.Maybe
open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Binary.Definitions
open import Relation.Nullary using (¬_; Dec; yes; no)
open import logic

open import automaton
open Automaton

data  StatesQ   : Set  where
   q1 : StatesQ
   q2 : StatesQ
   q3 : StatesQ

data  In2   : Set  where
   i0 : In2
   i1 : In2

transitionQ : StatesQ → In2 → StatesQ
transitionQ q1 i0 = q1
transitionQ q1 i1 = q2
transitionQ q2 i0 = q3
transitionQ q2 i1 = q2
transitionQ q3 i0 = q2
transitionQ q3 i1 = q2

aendQ : StatesQ → Bool
aendQ q1 = false
aendQ q2 = true
aendQ q3 = false

a1 : Automaton StatesQ In2
a1 = record {
       δ = transitionQ
     ; aend = aendQ
   }

test1 : accept a1 q1 ( i0 ∷ i1 ∷ i0 ∷ [] ) ≡ false
test1 = refl
test2 = accept a1 q1 ( i0 ∷ i1 ∷ i0 ∷ i1 ∷ [] ) 
test3 = trace a1 q1 ( i0 ∷ i1 ∷ i0 ∷ i1 ∷ [] ) 

data  States1   : Set  where
   sr : States1
   ss : States1
   st : States1

transition1 : States1  → In2  → States1
transition1 sr i0  = sr
transition1 sr i1  = ss
transition1 ss i0  = sr
transition1 ss i1  = st
transition1 st i0  = sr
transition1 st i1  = st

fin1 :  States1  → Bool
fin1 st = true
fin1 ss = false
fin1 sr = false

am1  :  Automaton  States1 In2
am1  =  record {  δ = transition1 ; aend = fin1   }


example1-1 = accept am1 sr ( i0  ∷ i1  ∷ i0  ∷ [] )
example1-2 = accept am1 sr ( i1  ∷ i1  ∷ i1  ∷ [] )
trace-2 = trace am1 sr ( i1  ∷ i1  ∷ i1  ∷ [] )

example1-3 = reachable am1 sr st ( i1  ∷ i1  ∷ i1  ∷ [] )

-- data Dec' (A : Set)  : Set where
--    yes' :   A → Dec' A
--    no'  : ¬ A → Dec' A
-- 
-- ieq' : (i i' : In2 ) → Dec' ( i ≡ i' )
-- ieq' i0 i0 = yes' refl
-- ieq' i1 i1 = yes' refl
-- ieq' i0 i1 = no' ( λ () )
-- ieq' i1 i0 = no' ( λ () )

ieq : (i i' : In2 ) → Dec ( i ≡ i' )
ieq i0 i0 = yes refl
ieq i1 i1 = yes refl
ieq i0 i1 = no ( λ () )
ieq i1 i0 = no ( λ () )

-- p.83 problem 1.4
--
-- w has at least three i0's and at least two i1's

count-chars : List In2 → In2 → ℕ
count-chars [] _ = 0
count-chars (h ∷ t) x with ieq h x
... | yes y = suc ( count-chars t x )
... | no  n = count-chars t x 

test11 : count-chars (  i1  ∷ i1  ∷ i0  ∷ []  ) i0 ≡ 1
test11 = refl

ex1_4a : (x : List In2) → Bool
ex1_4a x =  ( count-chars x i0 ≥b 3 ) /\ ( count-chars x i1 ≥b 2 )

language' : { Σ : Set } → Set
language' {Σ} = List Σ → Bool

lang14a :  language' {In2}
lang14a = ex1_4a

open _∧_

am14a-tr :  ℕ ∧ ℕ → In2 → ℕ ∧ ℕ
am14a-tr p i0 = record { proj1 = suc (proj1 p) ; proj2 = proj2 p }
am14a-tr p i1 = record { proj1 = proj1 p ; proj2 = suc (proj2 p) }

am14a  :  Automaton  (ℕ ∧ ℕ)  In2
am14a  =  record {  δ = am14a-tr ; aend = λ x → ( proj1 x ≥b 3 ) /\ ( proj2 x ≥b 2 )}

data am14s : Set where
  a00 : am14s
  a10 : am14s
  a20 : am14s
  a30 : am14s
  a01 : am14s
  a11 : am14s
  a21 : am14s
  a31 : am14s
  a02 : am14s
  a12 : am14s
  a22 : am14s
  a32 : am14s

am14a-tr' :  am14s  → In2 → am14s
am14a-tr' a00 i0 = a10
am14a-tr' _ _ = a10

am14a'  :  Automaton  am14s  In2
am14a'  =  record {  δ = am14a-tr' ; aend = λ x → {!!} }
