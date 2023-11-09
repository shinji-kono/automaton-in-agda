{-# OPTIONS --cubical-compatible --safe #-}
module automaton where

open import Data.Nat
open import Data.List
open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import logic

record Automaton ( Q : Set ) ( Σ : Set  )
       : Set  where
    field
        δ : Q → Σ → Q
        aend : Q → Bool

open Automaton

accept : { Q : Set } { Σ : Set  }
    → Automaton Q  Σ
    → Q
    → List  Σ → Bool
accept M q [] = aend M q
accept M q ( H  ∷ T ) = accept M ( δ M q H ) T

moves : { Q : Set } { Σ : Set  }
    → Automaton Q  Σ
    → Q → List  Σ → Q
moves M q [] = q
moves M q ( H  ∷ T ) = moves M ( δ M q H)  T

trace : { Q : Set } { Σ : Set  }
    → Automaton Q  Σ
    → Q → List  Σ → List Q
trace {Q} { Σ} M q [] = q ∷ []
trace {Q} { Σ} M q ( H  ∷ T ) = q ∷ trace M ( (δ M) q H ) T

reachable : { Q : Set } { Σ : Set  }
    → (M : Automaton Q  Σ  )
    → (astart q : Q )
    → (L : List  Σ ) → Set
reachable M astart q L = moves M astart  L ≡ q

