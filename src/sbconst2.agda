module sbconst2 where

open import Level renaming ( suc to succ ; zero to Zero )
open import Data.Nat
open import Data.Fin
open import Data.List

open import automaton
open import nfa
open import logic
open NAutomaton
open Automaton
open import  Relation.Binary.PropositionalEquality hiding ( [_] )

open Bool

δconv : { Q : Set } { Σ : Set  } → ( ( Q → Bool ) → Bool ) →  ( nδ : Q → Σ → Q → Bool ) → (f : Q → Bool) → (i : Σ) → (Q → Bool)
δconv {Q} { Σ} exists nδ f i q =  exists ( λ r → f r /\ nδ r i q )

subset-construction : { Q : Set } { Σ : Set  } → 
    ( ( Q → Bool ) → Bool ) →
    (NAutomaton Q  Σ ) → (Automaton (Q → Bool)  Σ )  
subset-construction {Q} { Σ}  exists NFA = record {
        δ = λ q x → δconv exists ( Nδ NFA ) q x
     ;  aend = λ f → exists ( λ q → f q /\ Nend NFA q )
   } 

test4 = subset-construction existsS1 am2 

test51 = accept test4 start1 ( i0  ∷ i1  ∷ i0  ∷ [] )
test61 = accept test4 start1 ( i1  ∷ i1  ∷ i1  ∷ [] )

subset-construction-lemma→ : { Q : Set } { Σ : Set  } { n  : ℕ }  → (exists : ( Q → Bool ) → Bool ) →
    (NFA : NAutomaton Q  Σ ) → (astart : Q → Bool ) 
    → (x : List Σ)
    → Naccept NFA exists astart  x ≡ true
    → accept (  subset-construction exists NFA ) astart  x ≡ true
subset-construction-lemma→ {Q} {Σ} {n} exists NFA astart x naccept = lemma1 x astart naccept where
    lemma1 :  (x : List Σ) → ( states : Q → Bool )
       → Naccept NFA exists states x ≡ true
       → accept (  subset-construction exists NFA ) states x ≡ true
    lemma1 [] states naccept = naccept
    lemma1 (h ∷ t ) states naccept = lemma1 t (δconv exists (Nδ NFA) states h) naccept

subset-construction-lemma← : { Q : Set } { Σ : Set  } { n  : ℕ }  → (exists : ( Q → Bool ) → Bool ) →
    (NFA : NAutomaton Q  Σ ) → (astart : Q → Bool )
    → (x : List Σ)
    → accept (  subset-construction exists NFA ) astart x ≡ true
    → Naccept NFA exists astart x ≡ true
subset-construction-lemma← {Q} {Σ} {n} exists NFA astart x saccept = lemma2 x astart saccept where
    lemma2 :  (x : List Σ) → ( states : Q → Bool )
       → accept (  subset-construction exists NFA ) states x ≡ true
       → Naccept NFA exists states x ≡ true
    lemma2 [] states saccept = saccept
    lemma2 (h ∷ t ) states saccept = lemma2 t (δconv exists (Nδ NFA) states h) saccept
