{-# OPTIONS --allow-unsolved-metas #-}

module regular-star where

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
open import regular-language 

open import nfa
open import sbconst2
open import finiteSet
open import finiteSetUtil
open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import regular-concat

open Automaton
open FiniteSet

open RegularLanguage

--
--   Star (contain A) = Concat (contain A) ( Star (contain A ) ) \/ Empty
--

Star-NFA :  {Σ : Set} → (A : RegularLanguage Σ ) → NAutomaton (states A ) Σ 
Star-NFA {Σ} A  = record { Nδ = δnfa ; Nend = nend } 
   module Star-NFA where
       δnfa : states A → Σ → states A → Bool
       δnfa q i q₁ with aend (automaton A) q
       ... | true = equal? (afin A) ( astart A) q₁ 
       ... | false = equal? (afin A) (δ (automaton A) q i) q₁
       nend : states A → Bool
       nend q = aend (automaton A) q

Star-NFA-start :  {Σ : Set} → (A : RegularLanguage Σ ) → states A  → Bool
Star-NFA-start A q = equal? (afin A) (astart A) q \/  aend (automaton A) q

SNFA-exist : {Σ : Set} → (A : RegularLanguage Σ ) → (states A → Bool) → Bool
SNFA-exist A qs = exists (afin A) qs 

M-Star : {Σ : Set} → (A : RegularLanguage Σ ) → RegularLanguage Σ
M-Star {Σ} A  = record {
       states = states A  → Bool
     ; astart = Star-NFA-start A 
     ; afin = ? -- fin→  (afin A)
     ; automaton = subset-construction (SNFA-exist A ) (Star-NFA A ) 
   } 
       
open Split

open _∧_

open NAutomaton
open import Data.List.Properties

closed-in-star :  {Σ : Set} → (A B : RegularLanguage Σ ) → ( x : List Σ ) → isRegular (Star (contain A) ) x ( M-Star A  )
closed-in-star {Σ} A B x = ≡-Bool-func closed-in-star→ closed-in-star← where
    NFA = (Star-NFA A )

    closed-in-star→ : Star (contain A)  x ≡ true → contain (M-Star A ) x ≡ true
    closed-in-star→ star = {!!}

    open Found

    closed-in-star← : contain (M-Star A ) x ≡ true → Star (contain A)  x ≡ true
    closed-in-star← C with subset-construction-lemma← (SNFA-exist A ) NFA (Star-NFA-start A) x C 
    ... | CC = {!!}




