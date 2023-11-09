{-# OPTIONS --cubical-compatible --safe #-}

-- {-# OPTIONS --allow-unsolved-metas #-}
module extended-automaton where

open import Level renaming ( suc to succ ; zero to Zero )
open import Data.Nat -- hiding ( erase )
open import Data.List
open import Data.Maybe hiding ( map )
-- open import Data.Bool using ( Bool ; true ; false ) renaming ( not to negate )
open import  Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Level renaming ( suc to succ ; zero to Zero )
open import Data.Product hiding ( map )
open import logic 

record Automaton ( Q : Set ) ( Σ : Set  ) : Set  where
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

NAutomaton : ( Q : Set ) ( Σ : Set  ) → Set  
NAutomaton Q Σ = Automaton ( Q → Bool ) Σ

Naccept : { Q : Set } { Σ : Set  } 
    → Automaton (Q → Bool)  Σ
    → (exists : ( Q → Bool ) → Bool)
    → (Nstart : Q → Bool) → List  Σ → Bool
Naccept M exists sb []  = exists ( λ q → sb q /\ aend M sb )
Naccept M exists sb (i ∷ t ) = Naccept M exists (λ q →  exists ( λ qn → (sb qn /\ ( δ M sb i q )  ))) t

PDA : ( Q : Set ) ( Σ : Set  ) → Set  
PDA Q Σ = Automaton ( List Q  ) Σ

data Write   (  Σ : Set  ) : Set  where
   write   : Σ → Write  Σ
   wnone   : Write  Σ
   --   erase write tnone

data Move : Set  where
   left   : Move  
   right  : Move  
   mnone  : Move  

record OTuring ( Q : Set ) ( Σ : Set  ) 
       : Set  where
    field
        tδ : Q →  Σ → Q × ( Write  Σ ) ×  Move 
        tstart : Q
        tend : Q → Bool
        tnone :  Σ
    taccept : List  Σ → ( Q × List  Σ × List  Σ )
    taccept L = ?

open import bijection 

b0 : ( Q : Set ) ( Σ : Set  ) → Bijection (List Q) (( Q × ( Write  Σ ) ×  Move  ) ∧ ( Q × List  Σ × List  Σ ))
b0 = ?

Turing : ( Q : Set ) ( Σ : Set  ) → Set  
Turing Q Σ = Automaton ( List Q  ) Σ

NDTM : ( Q : Set ) ( Σ : Set  ) → Set  
NDTM Q Σ = Automaton ( List Q → Bool ) Σ

UTM : ( Q : Set ) ( Σ : Set  ) → Set  
UTM Q Σ = Automaton ( List Q ) Σ

SuperTM : ( Q : Set ) ( Σ : Set  ) → Set  
SuperTM Q Σ = Automaton ( List Q ) Σ



