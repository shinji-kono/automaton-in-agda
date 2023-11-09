{-# OPTIONS --cubical-compatible --safe #-}

-- {-# OPTIONS --allow-unsolved-metas #-}

open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.List hiding ( [_] )        
open import Data.Empty                 
open import finiteSet
open import finiteSetUtil
open import fin

module regex2 ( Σ : Set) ( fin : FiniteSet Σ ) ( eq? : (x y : Σ) → Dec (x ≡ y)) where

open import Level renaming ( suc to succ ; zero to Zero )
open import Data.Fin hiding ( pred )
open import Data.Nat hiding ( _≟_ )
open import Data.List hiding ( any ;  [_] )
-- import Data.Bool using ( Bool ; true ; false ; _∧_ )
-- open import Data.Bool using ( Bool ; true ; false ; _∧_ ; _∨_ )
open import  Relation.Binary.PropositionalEquality as RBF hiding ( [_] ) 
open import Relation.Nullary using (¬_; Dec; yes; no)
open import regex
open import regular-language
open import automaton
open import logic

open import regular-star 
open import regular-concat 

open Automaton
open FiniteSet

open RegularLanguage

regex→RegularLanguage : Regex Σ → RegularLanguage Σ
regex→RegularLanguage ε = record { states = One ∨ One ; astart = case1 one ; afin = fin-∨1 finOne
    ; automaton = record { δ = λ _ _ → case2 one ; aend = rg00 } } where
      rg00 : One ∨ One → Bool
      rg00 (case1 one) = true
      rg00 (case2 one) = false
regex→RegularLanguage φ = record { states = One ; astart = one ; afin = finOne ; automaton = record { δ = λ _ _ → one ; aend = λ _ → false } }
regex→RegularLanguage (r *) = M-Star ( regex→RegularLanguage r )
regex→RegularLanguage (r & r₁) = M-Concat ( regex→RegularLanguage r ) (regex→RegularLanguage r₁ )
regex→RegularLanguage (r || r₁) = M-Union ( regex→RegularLanguage r ) (regex→RegularLanguage r₁ )
regex→RegularLanguage < x > = record { states = One ∨ One ∨ One ; astart = case1 one ; afin = fin-∨1 (fin-∨1 finOne)
     ; automaton = record { δ = rg01 ; aend = rg00 } } where
      rg00 : One ∨ One ∨ One → Bool
      rg00 (case1 one) = false             -- empty case failure
      rg00 (case2 (case1 one)) = true      -- may true on this phase
      rg00 (case2 (case2 one)) = false     -- no success never after
      rg01 : One ∨ One ∨ One → Σ → One ∨ One ∨ One
      rg01 (case1 one) s with eq? s x
      ... | yes _  = case2 (case1 one)
      ... | no _   = case2 (case2 one)
      rg01 (case2 (case1 one)) s = case2 (case2 one)
      rg01 (case2 (case2 one)) s = case2 (case2 one)


open Split

open _∧_

open import Data.List.Properties

regex-concat : {a b : Regex Σ} → (x : List Σ) → regex-language (a & b) eq? x ≡ Concat (regex-language a eq?) (regex-language b eq?) x
regex-concat  {_} {_} x = refl

open import sbconst2

regex-is-regular :  (r : Regex Σ ) → ( x : List Σ ) → isRegular (regex-language r eq?)  x ( regex→RegularLanguage r  )
regex-is-regular r x = rg00 r x where
      rg00 : (r : Regex Σ) → (x : List Σ) →   regex-language r eq? x ≡ accept (automaton (regex→RegularLanguage r)) (astart (regex→RegularLanguage r)) x 
      rg00 ε x = ?
      rg00 φ x = ?
      rg00 (r *) x = ?
      rg00 (r & r₁) x = begin
              split (regex-language r eq?) (regex-language r₁ eq?) x ≡⟨ cong₂ (λ j k → Concat j k x) 
                   (f-extensionality (rg00 r)) (f-extensionality (rg00 r₁))   ⟩
              Concat (contain (regex→RegularLanguage r)) (contain (regex→RegularLanguage r₁)) x 
                  ≡⟨  closed-in-concat (regex→RegularLanguage r) (regex→RegularLanguage r₁) x ⟩
              contain (M-Concat (regex→RegularLanguage r) (regex→RegularLanguage r₁)) x  ∎
                 where open ≡-Reasoning
      rg00 (r || r₁) x = ?
      rg00 < s > x = ?

-- end
