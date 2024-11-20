{-# OPTIONS --cubical-compatible --safe #-}

open import finiteSet
open import logic

module regular-concat where

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
open import nat
open import automaton
open import regular-language 

open import nfa
open import sbconst2
open import finiteSetUtil

open Automaton
open FiniteSet
open Split

open RegularLanguage

Concat-NFA :  {Σ : Set} → (A B : RegularLanguage Σ ) → NAutomaton (states A ∨ states B) Σ 
Concat-NFA {Σ} A B = record { Nδ = δnfa ; Nend = nend } 
   module Concat-NFA where
       δnfa : states A ∨ states B → Σ → states A ∨ states B → Bool
       δnfa (case1 q) i (case1 q₁) = equal? (afin A) (δ (automaton A) q i) q₁
       δnfa (case1 qa) i (case2 qb) = (aend (automaton A) qa ) /\
           (equal? (afin B) qb (δ (automaton B) (astart B) i) )
       δnfa (case2 q) i (case2 q₁) = equal? (afin B) (δ (automaton B) q i) q₁
       δnfa _ i _ = false
       nend : states A ∨ states B → Bool
       nend (case2 q) = aend (automaton B) q
       nend (case1 q) = aend (automaton A) q /\ aend (automaton B) (astart B) -- empty B case

Concat-NFA-start :  {Σ : Set} → (A B : RegularLanguage Σ ) → states A ∨ states B → Bool
Concat-NFA-start A B q = equal? (fin-∨ (afin A) (afin B)) (case1 (astart A)) q

CNFA-exist : {Σ : Set} → (A B : RegularLanguage Σ ) → (states A ∨ states B → Bool) → Bool
CNFA-exist A B qs = exists (fin-∨ (afin A) (afin B)) qs 

M-Concat : {Σ : Set} → (A B : RegularLanguage Σ ) → RegularLanguageF Σ
M-Concat {Σ} A B = record {
       states = states A ∨ states B 
     ; astart = Concat-NFA-start A B
     ; afin = fin-∨ (afin A) (afin B)
     ; automaton = subset-construction (CNFA-exist A B) (Concat-NFA A B) 
   } 

M-ConcatF : {Σ : Set} → (A B : RegularLanguage Σ ) → RegularLanguage Σ
M-ConcatF {Σ} A B = record {
       states = Fin (exp 2 (finite fin))
     ; astart = FiniteSetF.F←Q finf (λ s → (Concat-NFA-start A B (FiniteSet.Q←F fin s) ) )
     ; afin = record { Q←F = λ x → x ; F←Q = λ x → x ; finiso← = λ _ → refl ; finiso→  = λ _ → refl }
     ; automaton = atm
   } where
       fin : FiniteSet (states A ∨ states B ) 
       fin = fin-∨ (afin A) (afin B)
       satm : Automaton (states A ∨ states B → Bool) Σ
       satm = subset-construction (CNFA-exist A B) (Concat-NFA A B) 
       finf : FiniteSetF (Fin (FiniteSet.finite fin)) (Fin (exp 2 (FiniteSet.finite fin)))
       finf = fin→ 
       atm : Automaton (Fin (exp 2 (finite fin))) Σ
       atm =  record { δ = λ q i → FiniteSetF.F←Q finf (λ s → (δ satm (λ s → FiniteSetF.Q←F finf q (FiniteSet.F←Q fin s)) i (FiniteSet.Q←F fin s) ) )
           ; aend = λ q → aend satm (λ s → FiniteSetF.Q←F finf q (FiniteSet.F←Q fin s )) } 
       
open _∧_

open import Relation.Binary.PropositionalEquality hiding ( [_] )

open NAutomaton
open import Data.List.Properties

closed-in-concat :  {Σ : Set} → (A B : RegularLanguage Σ ) → ( x : List Σ ) → isRegularF (Concat (contain A) (contain B)) x ( M-Concat A B )
closed-in-concat {Σ} A B x = ≡-Bool-func closed-in-concat→ closed-in-concat← where
    finab = (fin-∨ (afin A) (afin B))
    NFA = (Concat-NFA A B)
    abmove : (q : states A ∨ states B) → (h : Σ ) → states A ∨ states B
    abmove (case1 q) h = case1 (δ (automaton A) q h)
    abmove (case2 q) h = case2 (δ (automaton B) q h)
    lemma-nmove-ab : (q : states A ∨ states B) → (h : Σ ) → Nδ NFA q h (abmove q h) ≡ true
    lemma-nmove-ab (case1 q) h = equal?-refl (afin A) 
    lemma-nmove-ab (case2 q) h = equal?-refl (afin B) 
    nmove : (q : states A ∨ states B) (nq : states A ∨ states B → Bool ) → (nq q ≡ true) → ( h : Σ ) →
       exists finab (λ qn → nq qn /\ Nδ NFA qn h (abmove q h)) ≡ true
    nmove (case1 q) nq nqt h = found finab (case1 q) ( bool-and-tt nqt (lemma-nmove-ab (case1 q)  h) )  
    nmove (case2 q) nq nqt h = found finab (case2 q) ( bool-and-tt nqt (lemma-nmove-ab (case2 q) h) ) 

    acceptB : (z : List Σ) → (q : states B) → (nq : states A ∨ states B → Bool ) → (nq (case2 q) ≡ true) → ( accept (automaton B) q z ≡ true ) 
        → Naccept NFA (CNFA-exist A B) nq z  ≡ true
    acceptB [] q nq nqt fb = lemma8 where
        lemma8 : exists finab ( λ q → nq q /\ Nend NFA q ) ≡ true
        lemma8 = found finab (case2 q) ( bool-and-tt nqt fb )
    acceptB (h ∷ t ) q nq nq=q fb = acceptB t (δ (automaton B) q h) (Nmoves NFA (CNFA-exist A B) nq h) (nmove (case2 q) nq nq=q h) fb 

    acceptA : (y z : List Σ) → (q : states A) → (nq : states A ∨ states B → Bool ) → (nq (case1 q) ≡ true)
        → ( accept (automaton A) q y ≡ true ) → ( accept (automaton B) (astart B) z ≡ true ) 
        → Naccept NFA (CNFA-exist A B) nq (y ++ z)  ≡ true
    acceptA [] [] q nq nqt fa fb = found finab (case1 q) (bool-and-tt nqt (bool-and-tt fa fb )) 
    acceptA [] (h ∷ z)  q nq nq=q fa fb = acceptB z nextb (Nmoves NFA (CNFA-exist A B) nq h) lemma70 fb where
         nextb : states B
         nextb = δ (automaton B) (astart B) h
         lemma70 : exists finab (λ qn → nq qn /\ Nδ NFA qn h (case2 nextb)) ≡ true
         lemma70 = found finab (case1 q) ( bool-and-tt nq=q (bool-and-tt fa (lemma-nmove-ab (case2 (astart B)) h) ))
    acceptA (h ∷ t) z q nq nq=q fa fb = acceptA t z (δ (automaton A) q h) (Nmoves NFA (CNFA-exist A B) nq h) (nmove (case1 q) nq nq=q h)  fa fb 

    acceptAB : Split (contain A) (contain B) x
        → Naccept NFA (CNFA-exist A B) (equal? finab (case1 (astart A))) x  ≡ true
    acceptAB S = subst ( λ k → Naccept NFA (CNFA-exist A B) (equal? finab (case1 (astart A))) k  ≡ true  ) ( sp-concat S )
        (acceptA (sp0 S) (sp1 S)  (astart A) (equal? finab (case1 (astart A))) (equal?-refl finab) (prop0 S) (prop1 S) )

    closed-in-concat→ : Concat (contain A) (contain B) x ≡ true → RegularLanguageF.contain (M-Concat A B) x ≡ true
    closed-in-concat→ concat with split→AB (contain A) (contain B) x concat
    ... | S = begin
          accept  (subset-construction (CNFA-exist A B) (Concat-NFA A B) ) (Concat-NFA-start A B ) x 
       ≡⟨ ≡-Bool-func (subset-construction-lemma←  (CNFA-exist A B)  NFA (equal? finab (case1 (astart A))) x ) 
          (subset-construction-lemma→  (CNFA-exist A B)  NFA (equal? finab (case1 (astart A))) x ) ⟩
          Naccept NFA (CNFA-exist A B) (equal? finab (case1 (astart A))) x
       ≡⟨ acceptAB S ⟩
         true
       ∎  where open ≡-Reasoning

    open Found

    ab-case : (q : states A ∨ states B ) → (qa : states A ) → (x : List Σ ) → Set
    ab-case (case1 qa') qa x = qa'  ≡ qa
    ab-case (case2 qb) qa x = ¬ ( accept (automaton B) qb x  ≡ true )

    contain-A : (x : List Σ) → (nq : states A ∨ states B → Bool ) → (fn : Naccept NFA (CNFA-exist A B) nq x ≡ true )
          → (qa : states A )  → (  (q : states A ∨ states B) → nq q ≡ true → ab-case q qa x )
          → split (accept (automaton A) qa ) (contain B) x ≡ true
    contain-A [] nq fn qa cond with found← finab fn  -- at this stage, A and B must be satisfied with [] (ab-case cond forces it)
    ... | S with found-q S in eq | cond (found-q S) (bool-∧→tt-0 (found-p S))
    ... | case1 qa' | refl = lemma11 where
       lemma12 : found-q S ≡ case1 qa →  aend (automaton A) qa /\ aend (automaton B) (astart B) ≡ Concat-NFA.nend A B (found-q S)
       lemma12 refl = refl
       lemma11 : aend (automaton A) qa /\ aend (automaton B) (astart B) ≡ true
       lemma11 = trans (lemma12 eq) ( bool-∧→tt-1 (found-p S) )
    ... | case2 qb  |  ab  = ⊥-elim ( ab (lemma11 eq) ) where 
       lemma11 : found-q S ≡ case2 qb → aend (automaton B) qb ≡ true
       lemma11 refl = bool-∧→tt-1 (found-p S)
    contain-A (h ∷ t) nq fn qa cond with bool-≡-? ((aend (automaton A) qa) /\  accept (automaton B) (δ (automaton B) (astart B) h) t ) true
    ... | yes0 eq = bool-or-41 eq  -- found A ++ B all end
    ... | no0 ne = bool-or-31 (contain-A t (Nmoves NFA (CNFA-exist A B) nq h) fn (δ (automaton A) qa h) lemma11 ) where -- B failed continue with ab-base condtion
       --- prove ab-case condition (we haven't checked but case2 b may happen)
       lemma11 :  (q : states A ∨ states B) → exists finab (λ qn → nq qn /\ Nδ NFA qn h q) ≡ true → ab-case q (δ (automaton A) qa h) t
       lemma11 (case1 qa')  ex with found← finab ex 
       ... | S with found-q S in eq | cond (found-q S) (bool-∧→tt-0 (found-p S)) 
       ... | case1 qa2 | refl = sym ( equal→refl (afin A) (lemma12 eq) ) where -- continued A case
           lemma12 : found-q S ≡ case1 qa2 → equal? (afin A) (δ (automaton A) qa2 h) qa' ≡ true  
           lemma12 refl = bool-∧→tt-1 (found-p S) 
       ... | case2 qb | nb = ⊥-elim (¬-bool refl ((lemma12 eq)) )  where --  δnfa (case2 q) i (case1 q₁) is false
           lemma12 :  found-q S ≡ case2 qb → false ≡ true 
           lemma12 refl = bool-∧→tt-1 (found-p S) 
       lemma11 (case2 qb)  ex with found← finab ex 
       ... | S with found-q S in eq | cond (found-q S) (bool-∧→tt-0 (found-p S)) 
       lemma11 (case2 qb)  ex | S | case2 qb' | nb = contra-position (lemma13 eq) nb where -- continued B case should fail
           lemma13 :  found-q S ≡ case2 qb' → accept (automaton B) qb t ≡ true → accept (automaton B) qb' (h ∷ t) ≡ true
           lemma13 refl fb = subst (λ k → accept (automaton B) k t ≡ true ) (sym (equal→refl (afin B) (bool-∧→tt-1 (found-p S)))) fb  
       lemma11 (case2 qb)  ex | S | case1 qa | refl with bool-∧→tt-1 (found-p S)
       ... | eee = contra-position (lemma12 eq) ne where -- starting B case should fail
           lemma12 : found-q S ≡ case1 qa  →  
                accept (automaton B) qb t ≡ true → aend (automaton A) qa /\ accept (automaton B) (δ (automaton B) (astart B) h) t ≡ true
           lemma12 refl fb = bool-and-tt (bool-∧→tt-0 eee) (subst ( λ k → accept (automaton B) k t ≡ true ) (equal→refl (afin B) (bool-∧→tt-1 eee) ) fb )

    lemma10 : Naccept NFA (CNFA-exist A B) (equal? finab (case1 (astart A))) x  ≡ true → split (contain A) (contain B) x ≡ true
    lemma10 CC = contain-A x (Concat-NFA-start A B ) CC (astart A) lemma15 where 
       lemma15 : (q : states A ∨ states B) → Concat-NFA-start A B q ≡ true → ab-case q (astart A) x
       lemma15 q nq=t with equal→refl finab nq=t 
       ... | refl = refl

    closed-in-concat← : RegularLanguageF.contain (M-Concat A B) x ≡ true → Concat (contain A) (contain B) x ≡ true
    closed-in-concat← C with subset-construction-lemma← (CNFA-exist A B) NFA (equal? finab (case1 (astart A))) x C 
    ... | CC = lemma10 CC




