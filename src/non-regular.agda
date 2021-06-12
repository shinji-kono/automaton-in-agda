module non-regular where

open import Data.Nat
open import Data.List
open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import logic
open import automaton
open import finiteSet
open import Relation.Nullary 

inputnn : ( n :  ℕ )  →  { Σ : Set  } → ( x y : Σ ) → List  Σ → List  Σ 
inputnn zero {_} _ _ s = s
inputnn (suc n) x y s = x  ∷ ( inputnn n x y ( y  ∷ s ) )

lemmaNN :  { Q : Set } { Σ : Set  } →  ( x y : Σ ) → ¬ (x ≡ y)
    → FiniteSet Q
    → (M : Automaton Q  Σ) (q : Q)
    → ¬ ( (n : ℕ) →   accept M q ( inputnn n x y [] ) ≡ true )
lemmaNN = {!!}

