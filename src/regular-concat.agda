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
open import logic
open import nat
open import automaton
open import regular-language

open import nfa
open import sbconst2

open RegularLanguage
open Automaton

Concat-NFA :  {Σ : Set} → (A B : RegularLanguage Σ ) → ((x y : states A )→ Dec (x ≡ y)) → ((x y : states B )→ Dec (x ≡ y))
    → NAutomaton (states A ∨ states B) Σ 
Concat-NFA {Σ} A B equal?A equal?B = record { Nδ = δnfa ; Nend = nend } 
   module Concat-NFA where
       δnfa : states A ∨ states B → Σ → states A ∨ states B → Bool
       δnfa (case1 q) i (case1 q₁) with equal?A (δ (automaton A) q i) q₁
       ... | yes _ = true
       ... | no _ =  false
       δnfa (case1 qa) i (case2 qb) with equal?B qb (δ (automaton B) (astart B) i) 
       ... | yes _ = aend (automaton A) qa 
       ... | no _ =  false
       δnfa (case2 q) i (case2 q₁) with equal?B (δ (automaton B) q i) q₁
       ... | yes _ = true
       ... | no _ =  false
       δnfa _ i _ = false
       nend : states A ∨ states B → Bool
       nend (case2 q) = aend (automaton B) q
       nend (case1 q) = aend (automaton A) q /\ aend (automaton B) (astart B) -- empty B case

Concat-NFA-start :  {Σ : Set} → (A B : RegularLanguage Σ ) → states A ∨ states B → ((x y : states A )→ Dec (x ≡ y))  → Bool
Concat-NFA-start A B (case1 a) equal?A with equal?A a (astart A)
... | yes _ = true
... | no _ =  false
Concat-NFA-start A B (case2 b) equal?A = false

M-Concat : {Σ : Set} → (A B : RegularLanguage Σ ) → ((states A → Bool) → Bool) → ((states B → Bool) → Bool)  → RegularLanguage Σ
M-Concat {Σ} A B existsA existsB = record {
       states = states A ∨ states B → Bool
     ; astart = λ ab → Concat-NFA-start A B ab {!!} 
     ; automaton = subset-construction sbexists (Concat-NFA A B {!!} {!!} ) 
   } where
       sbexists : (states A ∨ states B → Bool) → Bool
       sbexists P = existsA ( λ a → existsB ( λ b → P (case1 a) \/ P (case2 b)))
       
record Split {Σ : Set} (A : List Σ → Bool ) ( B : List Σ → Bool ) (x :  List Σ ) : Set where
    field
        sp0 : List Σ
        sp1 : List Σ
        sp-concat : sp0 ++ sp1 ≡ x
        prop0 : A sp0 ≡ true
        prop1 : B sp1 ≡ true

open Split

list-empty++ : {Σ : Set} → (x y : List Σ) → x ++ y ≡ [] → (x ≡ [] ) ∧ (y ≡ [] )
list-empty++ [] [] refl = record { proj1 = refl ; proj2 = refl }
list-empty++ [] (x ∷ y) ()
list-empty++ (x ∷ x₁) y ()

open _∧_

open import Relation.Binary.PropositionalEquality hiding ( [_] )

c-split-lemma : {Σ : Set} → (A B : List Σ → Bool ) → (h : Σ) → ( t : List Σ ) → split A B (h ∷ t ) ≡ true
   → ( ¬ (A [] ≡ true )) ∨ ( ¬ (B ( h ∷ t ) ≡ true) )
   → split (λ t1 → A (h ∷ t1)) B t ≡ true
c-split-lemma {Σ} A B h t eq p = sym ( begin
      true
  ≡⟨  sym eq  ⟩
      split A B (h ∷ t ) 
  ≡⟨⟩
      A [] /\ B (h ∷ t) \/ split (λ t1 → A (h ∷ t1)) B t
  ≡⟨  cong ( λ k → k \/ split (λ t1 → A (h ∷ t1)) B t ) (lemma-p p ) ⟩
      false \/ split (λ t1 → A (h ∷ t1)) B t
  ≡⟨ bool-or-1 refl ⟩
      split (λ t1 → A (h ∷ t1)) B t
  ∎ ) where
     open ≡-Reasoning 
     lemma-p : ( ¬ (A [] ≡ true )) ∨ ( ¬ (B ( h ∷ t ) ≡ true) ) → A [] /\ B (h ∷ t) ≡ false
     lemma-p (case1 ¬A ) = bool-and-1 ( ¬-bool-t ¬A )
     lemma-p (case2 ¬B ) = bool-and-2 ( ¬-bool-t ¬B )

split→AB :  {Σ : Set} → (A B : List Σ → Bool ) → ( x : List Σ ) → split A B x ≡ true → Split A B x
split→AB {Σ} A B [] eq with bool-≡-? (A []) true | bool-≡-? (B []) true 
split→AB {Σ} A B [] eq | yes eqa | yes eqb = 
    record { sp0 = [] ; sp1 = [] ; sp-concat = refl ; prop0 = eqa ; prop1 = eqb }
split→AB {Σ} A B [] eq | yes p | no ¬p = ⊥-elim (lemma-∧-1 eq (¬-bool-t ¬p ))
split→AB {Σ} A B [] eq | no ¬p | t = ⊥-elim (lemma-∧-0 eq (¬-bool-t ¬p ))
split→AB {Σ} A B (h ∷ t ) eq with bool-≡-? (A []) true | bool-≡-? (B (h ∷ t )) true
... | yes px | yes py = record { sp0 = [] ; sp1 = h ∷ t ; sp-concat = refl ; prop0 = px ; prop1 = py }
... | no px | _ with split→AB (λ t1 → A ( h ∷ t1 )) B t (c-split-lemma A B h t eq (case1 px) )
... | S = record { sp0 = h ∷ sp0 S  ; sp1 = sp1 S ; sp-concat = cong ( λ k → h ∷ k) (sp-concat S) ; prop0 = prop0 S ; prop1 = prop1 S }
split→AB {Σ} A B (h ∷ t ) eq  | _ | no px with split→AB (λ t1 → A ( h ∷ t1 )) B t (c-split-lemma A B h t eq (case2 px) )
... | S = record { sp0 = h ∷ sp0 S  ; sp1 = sp1 S ; sp-concat = cong ( λ k → h ∷ k) (sp-concat S) ; prop0 = prop0 S ; prop1 = prop1 S }

AB→split :  {Σ : Set} → (A B : List Σ → Bool ) → ( x y : List Σ ) → A x ≡ true → B y ≡ true → split A B (x ++ y ) ≡ true
AB→split {Σ} A B [] [] eqa eqb = begin
       split A B [] 
     ≡⟨⟩
       A [] /\ B []
     ≡⟨ cong₂ (λ j k → j /\ k ) eqa eqb ⟩
      true
     ∎  where open ≡-Reasoning
AB→split {Σ} A B [] (h ∷ y ) eqa eqb = begin
      split A B (h ∷ y )
     ≡⟨⟩
      A [] /\ B (h ∷ y) \/ split (λ t1 → A (h ∷ t1)) B y
     ≡⟨ cong₂ (λ j k → j /\ k \/ split (λ t1 → A (h ∷ t1)) B y ) eqa eqb ⟩
      true /\ true \/ split (λ t1 → A (h ∷ t1)) B y
     ≡⟨⟩
      true \/ split (λ t1 → A (h ∷ t1)) B y
     ≡⟨⟩
      true
     ∎  where open ≡-Reasoning
AB→split {Σ} A B (h ∷ t) y eqa eqb = begin
       split A B ((h ∷ t) ++ y)  
     ≡⟨⟩
       A [] /\ B (h ∷ t ++ y) \/ split (λ t1 → A (h ∷ t1)) B (t ++ y)
     ≡⟨ cong ( λ k →  A [] /\ B (h ∷ t ++ y) \/ k ) (AB→split {Σ} (λ t1 → A (h ∷ t1)) B t y eqa eqb ) ⟩
       A [] /\ B (h ∷ t ++ y) \/ true
     ≡⟨ bool-or-3 ⟩
      true
     ∎  where open ≡-Reasoning

open NAutomaton
open import Data.List.Properties

open import finiteSet
open import finiteSetUtil

open FiniteSet

closed-in-concat :  {Σ : Set} → (A B : RegularLanguage Σ ) → ( x : List Σ ) → isRegular (Concat (contain A) (contain B)) x ( M-Concat A B )
closed-in-concat {Σ} A B x = ≡-Bool-func closed-in-concat→ closed-in-concat← where
    afin : (A : RegularLanguage Σ ) → FiniteSet A
    afin = ?
    finab = (fin-∨ (afin A) (afin B))
    NFA = (Concat-NFA A B)
    abmove : (q : states A ∨ states B) → (h : Σ ) → states A ∨ states B
    abmove (case1 q) h = case1 (δ (automaton A) q h)
    abmove (case2 q) h = case2 (δ (automaton B) q h)
    lemma-nmove-ab : (q : states A ∨ states B) → (h : Σ ) → Nδ NFA q h (abmove q h) ≡ true
    lemma-nmove-ab (case1 q) _ = ? -- equal?-refl (afin A)
    lemma-nmove-ab (case2 q) _ = ? -- equal?-refl (afin B)
    nmove : (q : states A ∨ states B) (nq : states A ∨ states B → Bool ) → (nq q ≡ true) → ( h : Σ ) →
       exists finab (λ qn → nq qn /\ Nδ NFA qn h (abmove q h)) ≡ true
    nmove (case1 q) nq nqt h = found finab (case1 q) ( bool-and-tt nqt (lemma-nmove-ab (case1 q)  h) )  
    nmove (case2 q) nq nqt h = found finab (case2 q) ( bool-and-tt nqt (lemma-nmove-ab (case2 q) h) ) 
    acceptB : (z : List Σ) → (q : states B) → (nq : states A ∨ states B → Bool ) → (nq (case2 q) ≡ true) → ( accept (automaton B) q z ≡ true ) 
        → Naccept NFA finab nq z  ≡ true
    acceptB [] q nq nqt fb = lemma8 where
        lemma8 : exists finab ( λ q → nq q /\ Nend NFA q ) ≡ true
        lemma8 = found finab (case2 q) ( bool-and-tt nqt fb )
    acceptB (h ∷ t ) q nq nq=q fb = acceptB t (δ (automaton B) q h) (Nmoves NFA finab nq h) (nmove (case2 q) nq nq=q h) fb 

    acceptA : (y z : List Σ) → (q : states A) → (nq : states A ∨ states B → Bool ) → (nq (case1 q) ≡ true)
        → ( accept (automaton A) q y ≡ true ) → ( accept (automaton B) (astart B) z ≡ true ) 
        → Naccept NFA finab nq (y ++ z)  ≡ true
    acceptA [] [] q nq nqt fa fb = found finab (case1 q) (bool-and-tt nqt (bool-and-tt fa fb )) 
    acceptA [] (h ∷ z)  q nq nq=q fa fb = acceptB z nextb (Nmoves NFA finab nq h) lemma70 fb where
         nextb : states B
         nextb = δ (automaton B) (astart B) h
         lemma70 : exists finab (λ qn → nq qn /\ Nδ NFA qn h (case2 nextb)) ≡ true
         lemma70 = found finab (case1 q) ( bool-and-tt nq=q (bool-and-tt fa (lemma-nmove-ab (case2 (astart B)) h) ))
    acceptA (h ∷ t) z q nq nq=q fa fb = acceptA t z (δ (automaton A) q h) (Nmoves NFA finab nq h) (nmove (case1 q) nq nq=q h)  fa fb where

    acceptAB : Split (contain A) (contain B) x
        → Naccept NFA finab (equal? finab (case1 (astart A))) x  ≡ true
    acceptAB S = subst ( λ k → Naccept NFA finab (equal? finab (case1 (astart A))) k  ≡ true  ) ( sp-concat S )
        (acceptA (sp0 S) (sp1 S)  (astart A) (equal? finab (case1 (astart A))) ? (prop0 S) (prop1 S) )

    closed-in-concat→ : Concat (contain A) (contain B) x ≡ true → contain (M-Concat A B) x ≡ true
    closed-in-concat→ concat with split→AB (contain A) (contain B) x concat
    ... | S = begin
          accept (subset-construction finab NFA (case1 (astart A))) (Concat-NFA-start A B ) x 
       ≡⟨ ≡-Bool-func (subset-construction-lemma← finab NFA (case1 (astart A)) x ) 
          (subset-construction-lemma→ finab NFA (case1 (astart A)) x ) ⟩
          Naccept NFA finab (equal? finab (case1 (astart A))) x
       ≡⟨ acceptAB S ⟩
         true
       ∎  where open ≡-Reasoning

    open Found

    ab-case : (q : states A ∨ states B ) → (qa : states A ) → (x : List Σ ) → Set
    ab-case (case1 qa') qa x = qa'  ≡ qa
    ab-case (case2 qb) qa x = ¬ ( accept (automaton B) qb x  ≡ true )

    contain-A : (x : List Σ) → (nq : states A ∨ states B → Bool ) → (fn : Naccept NFA finab nq x ≡ true )
          → (qa : states A )  → (  (q : states A ∨ states B) → nq q ≡ true → ab-case q qa x )
          → split (accept (automaton A) qa ) (contain B) x ≡ true
    contain-A [] nq fn qa cond with found← finab fn 
    ... | S with found-q S | inspect found-q S | cond (found-q S) (bool-∧→tt-0 (found-p S))
    ... | case1 qa' | record { eq = refl } | refl = bool-∧→tt-1 (found-p S)
    ... | case2 qb | record { eq = refl } | ab = ⊥-elim ( ab (bool-∧→tt-1 (found-p S)))
    contain-A (h ∷ t) nq fn qa cond with bool-≡-? ((aend (automaton A) qa) /\  accept (automaton B) (δ (automaton B) (astart B) h) t ) true
    ... | yes eq = bool-or-41 eq
    ... | no ne = bool-or-31 (contain-A t (Nmoves NFA finab nq h) fn (δ (automaton A) qa h) lemma11 ) where
       lemma11 :  (q : states A ∨ states B) → exists finab (λ qn → nq qn /\ Nδ NFA qn h q) ≡ true → ab-case q (δ (automaton A) qa h) t
       lemma11 (case1 qa')  ex with found← finab ex 
       ... | S with found-q S | inspect found-q S | cond (found-q S) (bool-∧→tt-0 (found-p S)) 
       ... | case1 qa | record { eq = refl } | refl = sym ( equal→refl (afin A)  ( bool-∧→tt-1 (found-p S) ))  -- continued A case
       ... | case2 qb | record { eq = refl } | nb with  bool-∧→tt-1 (found-p S) -- δnfa (case2 q) i (case1 q₁) is false
       ... | ()   
       lemma11 (case2 qb)  ex with found← finab ex 
       ... | S with found-q S | inspect found-q S | cond (found-q S) (bool-∧→tt-0 (found-p S)) 
       lemma11 (case2 qb)  ex | S | case2 qb' | record { eq = refl } | nb = contra-position lemma13 nb where -- continued B case should fail
           lemma13 :  accept (automaton B) qb t ≡ true → accept (automaton B) qb' (h ∷ t) ≡ true
           lemma13 fb = subst (λ k → accept (automaton B) k t ≡ true ) (sym (equal→refl (afin B) (bool-∧→tt-1 (found-p S)))) fb  
       lemma11 (case2 qb)  ex | S | case1 qa | record { eq = refl } | refl with bool-∧→tt-1 (found-p S)
       ... | eee = contra-position lemma12 ne where -- starting B case should fail
           lemma12 : accept (automaton B) qb t ≡ true → aend (automaton A) qa /\ accept (automaton B) (δ (automaton B) (astart B) h) t ≡ true
           lemma12 fb = bool-and-tt (bool-∧→tt-0 eee) (subst ( λ k → accept (automaton B) k t ≡ true ) (equal→refl (afin B) (bool-∧→tt-1 eee) ) fb )

    lemma10 : Naccept NFA finab (equal? finab (case1 (astart A))) x  ≡ true → split (contain A) (contain B) x ≡ true
    lemma10 CC = contain-A x (Concat-NFA-start A B ) CC (astart A) lemma15 where 
       lemma15 : (q : states A ∨ states B) → Concat-NFA-start A B q ≡ true → ab-case q (astart A) x
       lemma15 q nq=t with equal→refl finab nq=t 
       ... | refl = refl

    closed-in-concat← : contain (M-Concat A B) x ≡ true → Concat (contain A) (contain B) x ≡ true
    closed-in-concat← C with subset-construction-lemma← finab NFA (case1 (astart A)) x C
    ... | CC = lemma10 CC




