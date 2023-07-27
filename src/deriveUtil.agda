module deriveUtil where

open import Level renaming ( suc to succ ; zero to Zero )
open import Data.Nat
open import Data.Fin
open import Data.List

open import regex
open import automaton
open import nfa
open import logic
open NAutomaton
open Automaton
open import  Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Nullary


open Bool

data alpha2 : Set where
   a : alpha2
   b : alpha2

a-eq? : (x y : alpha2) → Dec (x ≡ y)
a-eq? a a = yes refl
a-eq? b b = yes refl
a-eq? a b = no (λ ())
a-eq? b a = no (λ ())

open Regex

open import finiteSet

fin-a : FiniteSet alpha2
fin-a  = record {
     finite = finite0
   ; Q←F = Q←F0 
   ; F←Q = F←Q0 
   ; finiso→ = finiso→0
   ; finiso← = finiso←0
 } where
     finite0 : ℕ
     finite0 = 2
     Q←F0 : Fin finite0 → alpha2
     Q←F0 zero = a
     Q←F0 (suc zero) = b
     F←Q0 : alpha2 → Fin finite0
     F←Q0 a = # 0
     F←Q0 b = # 1
     finiso→0 : (q : alpha2) → Q←F0 ( F←Q0 q ) ≡ q
     finiso→0 a = refl
     finiso→0 b = refl
     finiso←0 : (f : Fin finite0 ) → F←Q0 ( Q←F0 f ) ≡ f
     finiso←0 zero = refl
     finiso←0 (suc zero) = refl


open import derive alpha2 fin-a a-eq?
test11 = regex→automaton ( < a > & < b > )

test12 = accept test11 record { state =  < a > & < b > ; is-derived = unit refl } ( a ∷ b ∷ [] )
test13 = accept test11 record { state =  < a > & < b > ; is-derived = unit refl } ( a ∷ a ∷ [] )

test14 = regex-match ( (  < a > & < b > ) * ) ( a ∷ b ∷ a ∷ a ∷ [] )

test15 = derive-step ( ( < a > & < b > ) * ) record { state = ( < a > & < b > ) *  ; is-derived = unit refl } a
-- test16 = derive-step ? -- test15
-- test17 : derive-step ? -- test16 ≡ test16
-- test17 = refl

stest11 = regex→automaton1 ( < a > & < b > )
stest12 = accept stest11 (toSB ( < a > & < b > )) ( a ∷ b ∷ [] )
stest13 = accept stest11 (toSB ( < a > & < b > )) ( a ∷ a ∷ [] )





