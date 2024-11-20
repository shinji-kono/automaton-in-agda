{-# OPTIONS --cubical-compatible --safe #-}

module regular-language where

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

language : { Σ : Set } → Set
language {Σ} = List Σ → Bool

language-L : { Σ : Set } → Set
language-L {Σ} = List (List Σ)

Union : {Σ : Set} → ( A B : language {Σ} ) → language {Σ}
Union {Σ} A B x = A x  \/ B x

split : {Σ : Set} → (x y : language {Σ} ) → language {Σ}
split x y  [] = x [] /\ y []
split x y (h  ∷ t) = (x [] /\ y (h  ∷ t)) \/
  split (λ t1 → x (  h ∷ t1 ))  (λ t2 → y t2 ) t

Concat : {Σ : Set} → ( A B : language {Σ} ) → language {Σ}
Concat {Σ} A B = split A B

repeat : {Σ : Set} → (P : List Σ → Bool) → (pre y : List Σ ) → Bool
repeat P [] [] = true
repeat P (h ∷ t) [] = P (h ∷ t)
repeat P pre (h ∷ []) =      P (pre ++ (h ∷ []))
repeat P pre (h ∷ y@(_ ∷ _)) =
   ((P (pre ++ (h ∷ []))) /\ repeat P [] y )
   \/ repeat P (pre ++ (h ∷ [])) y

Star : {Σ : Set} → (x : List Σ → Bool) → (y : List Σ ) → Bool
Star {Σ} x y = repeat x [] y

-- We have to prove definitions of Concat and Star are equivalent to the set theoretic definitions

-- 1.  A ∪ B = { x | x ∈ A \/ x ∈ B }
-- 2.  A ∘ B = { x | ∃ y ∈ A, z ∈ B, x = y ++ z }
-- 3.  A* = { x | ∃ n ∈ ℕ, y1, y2, ..., yn ∈ A, x = y1 ++ y2 ++ ... ++ yn }

-- lemma-Union : {Σ : Set} → ( A B : language {Σ} ) → ( x : List Σ ) → Union A B x ≡ ( A x \/ B x )
-- lemma-Union = ?

-- lemma-Concat : {Σ : Set} → ( A B : language {Σ} ) → ( x : List Σ )
--    → Concat A B x ≡ ( ∃ λ y → ∃ λ z → A y /\ B z /\ x ≡ y ++ z )
-- lemma-Concat = ?

open import automaton-ex

-- test-AB→star : {Σ : Set} → {A B : List In2 → Bool} → Star1 A ( i1 ∷ i1 ∷ i1 ∷ [] ) ≡ ?
-- test-AB→star  = ?

test-aaa = Star (accept am1 sr) ( i1 ∷ i1 ∷ i1 ∷ [] )

test-AB→split : {Σ : Set} → {A B : List In2 → Bool} → split A B ( i0 ∷ i1 ∷ i0 ∷ [] ) ≡ (
       ( A [] /\ B ( i0 ∷ i1 ∷ i0 ∷ [] ) ) \/
       ( A ( i0 ∷ [] ) /\ B ( i1 ∷ i0 ∷ [] ) ) \/
       ( A ( i0 ∷ i1 ∷ [] ) /\ B ( i0 ∷ [] ) ) \/
       ( A ( i0 ∷ i1 ∷ i0 ∷ [] ) /\ B  []  )
   )
test-AB→split {_} {A} {B} = refl

star-nil : {Σ : Set} → ( A : language {Σ} ) → Star A [] ≡ true
star-nil A = refl

open Automaton
open import finiteSet
open import finiteSetUtil

record RegularLanguage ( Σ : Set ) : Set (Suc Zero) where
   field
      states : Set
      astart : states
      afin : FiniteSet states
      automaton : Automaton states Σ
   contain : List Σ → Bool
   contain x = accept automaton astart x


isRegular : {Σ : Set} → (A : language {Σ} ) → ( x : List Σ ) → (r : RegularLanguage Σ ) → Set
isRegular A x r = A x ≡ accept (automaton r) (astart r) x
  where open RegularLanguage

RegularLanguage-is-language : { Σ : Set } → RegularLanguage Σ  → language {Σ}
RegularLanguage-is-language {Σ} R = RegularLanguage.contain R

RegularLanguage-is-language' : { Σ : Set } → RegularLanguage Σ  → List Σ  → Bool
RegularLanguage-is-language' {Σ} R x = accept (automaton R) (astart R) x where
   open RegularLanguage

record RegularLanguageF ( Σ : Set ) : Set (Suc Zero) where
   field
      states : Set
      astart : states → Bool
      afin : FiniteSet states
      automaton : Automaton (states → Bool) Σ
   contain : List Σ → Bool
   contain x = accept automaton astart x

isRegularF : {Σ : Set} → (A : language {Σ} ) → ( x : List Σ ) → (r : RegularLanguageF Σ ) → Set
isRegularF A x r = A x ≡ contain r x
  where open RegularLanguageF

--  a language is implemented by an automaton

-- postulate
--   fin-× : {A B : Set} → { a b : ℕ } → FiniteSet A {a} → FiniteSet B {b} → FiniteSet (A × B) {a * b}

open RegularLanguage

M-Union : {Σ : Set} → (A B : RegularLanguage Σ ) → RegularLanguage Σ
M-Union {Σ} A B = record {
       states =  states A × states B
     ; astart = ( astart A , astart B )
     ; afin = fin-× (afin A) (afin B)
     ; automaton = record {
             δ = λ q x →  ( δ (automaton A) (proj₁ q) x , δ (automaton B) (proj₂ q) x )
           ; aend = λ q → ( aend (automaton A) (proj₁ q) \/ aend (automaton B) (proj₂ q) )
        }
   }

closed-in-union :  {Σ : Set} → (A B : RegularLanguage Σ ) → ( x : List Σ ) → isRegular (Union (contain A) (contain B)) x ( M-Union A B )
closed-in-union A B [] = lemma where
   lemma : aend (automaton A) (astart A) \/ aend (automaton B) (astart B) ≡
           aend (automaton A) (astart A) \/ aend (automaton B) (astart B)
   lemma = refl
closed-in-union {Σ} A B ( h ∷ t ) = lemma1 t ((δ (automaton A) (astart A) h)) ((δ (automaton B) (astart B) h)) where
   lemma1 : (t : List Σ) → (qa : states A ) → (qb : states B ) →
     accept (automaton A) qa t \/ accept (automaton B) qb  t
       ≡ accept (automaton (M-Union A B)) (qa , qb) t
   lemma1 [] qa qb = refl
   lemma1 (h ∷ t ) qa qb = lemma1 t ((δ (automaton A) qa h)) ((δ (automaton B) qb h))



record Split {Σ : Set} (A : List Σ → Bool ) ( B : List Σ → Bool ) (x :  List Σ ) : Set where
    field
        sp0 sp1 : List Σ
        sp-concat : sp0 ++ sp1 ≡ x
        prop0 : A sp0 ≡ true
        prop1 : B sp1 ≡ true

open Split

AB→split1 :  {Σ : Set} → (A B : List Σ → Bool ) → ( x y : List Σ ) → {z : List Σ} → A x ≡ true → B y ≡ true →  z ≡ x ++ y → Split A B z
AB→split1 {Σ} A B x y {z} ax by z=xy = record { sp0 = x ; sp1 = y ; sp-concat = sym z=xy ; prop0 = ax ; prop1 = by }

list-empty++ : {Σ : Set} → (x y : List Σ) → x ++ y ≡ [] → (x ≡ [] ) ∧ (y ≡ [] )
list-empty++ [] [] _ = record { proj1 = refl ; proj2 = refl }
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
split→AB {Σ} A B [] eq | yes0 eqa | yes0 eqb =
    record { sp0 = [] ; sp1 = [] ; sp-concat = refl ; prop0 = eqa ; prop1 = eqb }
split→AB {Σ} A B [] eq | yes0 p | no0 ¬p = ⊥-elim (lemma-∧-1 eq (¬-bool-t ¬p ))
split→AB {Σ} A B [] eq | no0 ¬p | t = ⊥-elim (lemma-∧-0 eq (¬-bool-t ¬p ))
split→AB {Σ} A B (h ∷ t ) eq with bool-≡-? (A []) true | bool-≡-? (B (h ∷ t )) true
... | yes0 px | yes0 py = record { sp0 = [] ; sp1 = h ∷ t ; sp-concat = refl ; prop0 = px ; prop1 = py }
... | no0 px | _ with split→AB (λ t1 → A ( h ∷ t1 )) B t (c-split-lemma A B h t eq (case1 px) )
... | S = record { sp0 = h ∷ sp0 S  ; sp1 = sp1 S ; sp-concat = cong ( λ k → h ∷ k) (sp-concat S) ; prop0 = prop0 S ; prop1 = prop1 S }
split→AB {Σ} A B (h ∷ t ) eq  | _ | no0 px with split→AB (λ t1 → A ( h ∷ t1 )) B t (c-split-lemma A B h t eq (case2 px) )
... | S = record { sp0 = h ∷ sp0 S  ; sp1 = sp1 S ; sp-concat = cong ( λ k → h ∷ k) (sp-concat S) ; prop0 = prop0 S ; prop1 = prop1 S }

AB→split :  {Σ : Set} → (A B : List Σ → Bool ) → ( x y : List Σ ) → A x ≡ true → B y ≡ true → split A B (x ++ y ) ≡ true
AB→split {Σ} A B [] [] eqa eqb = begin
       split A B [] ≡⟨⟩
       A [] /\ B [] ≡⟨ cong₂ (λ j k → j /\ k ) eqa eqb ⟩
      true
     ∎  where open ≡-Reasoning
AB→split {Σ} A B [] (h ∷ y ) eqa eqb = begin
      split A B (h ∷ y ) ≡⟨⟩
      A [] /\ B (h ∷ y) \/ split (λ t1 → A (h ∷ t1)) B y ≡⟨ cong₂ (λ j k → j /\ k \/ split (λ t1 → A (h ∷ t1)) B y ) eqa eqb ⟩
      true /\ true \/ split (λ t1 → A (h ∷ t1)) B y ≡⟨⟩
      true \/ split (λ t1 → A (h ∷ t1)) B y ≡⟨⟩
      true ∎  where open ≡-Reasoning
AB→split {Σ} A B (h ∷ t) y eqa eqb = begin
       split A B ((h ∷ t) ++ y)  ≡⟨⟩
       A [] /\ B (h ∷ t ++ y) \/ split (λ t1 → A (h ∷ t1)) B (t ++ y)
     ≡⟨ cong ( λ k →  A [] /\ B (h ∷ t ++ y) \/ k ) (AB→split {Σ} (λ t1 → A (h ∷ t1)) B t y eqa eqb ) ⟩
       A [] /\ B (h ∷ t ++ y) \/ true ≡⟨ bool-or-3 ⟩
      true ∎  where open ≡-Reasoning


split→AB1 :  {Σ : Set} → (A B : List Σ → Bool ) → ( x : List Σ ) → Split A B x →  split A B x ≡ true
split→AB1 {Σ} A B x S = subst (λ k → split A B k ≡ true ) (sp-concat S) ( AB→split A B _ _ (prop0 S) (prop1 S)  )


-- law of exclude middle of Split A B x
lemma-concat : {Σ : Set} → ( A B : language {Σ} ) → (x : List Σ) → Split A B x ∨ ( ¬ Split A B x )
lemma-concat {Σ} A B x with split A B x in eq
... | true = case1 (split→AB A B x eq )
... | false = case2 (λ p →  ¬-bool eq (split→AB1 A B x p ))

-- Concat : {Σ : Set} → ( A B : language {Σ} ) → language {Σ}
-- Concat {Σ} A B = split A B

Concat' : {Σ : Set} → ( A B : language {Σ} ) → (x : List Σ) → Set
Concat' {Σ} A B = λ x → Split A B x

record StarProp {Σ : Set} (A : List Σ → Bool ) (x :  List Σ ) : Set where
    field
        spn : List ( List Σ )
        spn-concat : foldr (λ k → k ++_ ) [] spn ≡ x
        propn : foldr (λ k → λ j → A k /\ j ) true spn ≡ true

open StarProp

open import Data.List.Properties

-- Star→StarProp : {Σ : Set} → ( A : language {Σ} ) → (x : List Σ) → Star A x ≡ true → StarProp A x
-- Star→StarProp {Σ} A x ax = ss00 [] x ax  where
--     ss00 :  (pre x : List Σ) → repeat A pre x ≡ true → StarProp A (pre ++ x )
--     ss00 [] [] eq = record { spn = [] ; spn-concat = refl ; propn = eq }
--     ss00 (h ∷ t) [] eq = record { spn = (h ∷ t) ∷ []  ; spn-concat = refl ; propn = bool-and-tt eq refl }
--     ss00 pre (h ∷ []) eq = record { spn = (pre ++ (h ∷ [])) ∷ []  ; spn-concat = ++-assoc pre _ _
--        ; propn = bool-and-tt (trans (sym (ss01 pre (h ∷ []) refl )) eq) refl } where
--         ss01 : (pre x : List Σ) → x ≡ h ∷ [] → repeat A pre x ≡ A (pre ++ (h ∷ []))
--         ss01 [] (h ∷ []) refl = refl
--         ss01 (x ∷ pre) (h ∷ []) refl = refl
--     ss00 pre (h ∷ y@(i ∷ t)) eq = ? where
--         ss01 : (pre x : List Σ) → x ≡ y → ( ((A (pre ++ (h ∷ []))) /\ repeat A [] y ) \/ repeat A (pre ++ (h ∷ [])) y ) ≡ repeat A pre (h ∷ y )
--         ss01 = ?
--         ss02 :  StarProp A (pre ++ h ∷ y )
--         ss02 with (A (pre ++ (h ∷ []))) /\ repeat A [] y in eq1
--         ... | true = ?
--         ... | false = ? where
--            ss03 : repeat A (pre ++ (h ∷ [])) y ≡ true
--            ss03 = ?
--
--
-- StarProp→Star : {Σ : Set} → ( A : language {Σ} ) → (x : List Σ) → StarProp A x → Star A x ≡ true
-- StarProp→Star {Σ} A x sp = subst (λ k →  Star A k ≡ true ) (spsx (spn sp) refl) ( sps1 (spn sp) refl ) where
--      spsx : (y : List ( List Σ ) ) → spn sp ≡ y → foldr (λ k → k ++_ ) [] y ≡ x
--      spsx y refl = spn-concat sp
--      sps1 : (y : List ( List Σ ) ) → spn sp ≡ y → Star A (foldr (λ k → k ++_ ) [] y) ≡ true
--      sps1 [] sp=y = refl
--      sps1 ([] ∷ t) sp=y = ?
--      sps1 ((x ∷ h) ∷ t) sp=y = ?
--
--
-- lemma-starprop : {Σ : Set} → ( A : language {Σ} ) → (x : List Σ) → StarProp A x ∨ ( ¬ StarProp A x )
-- lemma-starprop = ?
--

open FiniteSet


RLF→RL : {Σ : Set} → RegularLanguageF Σ → RegularLanguage Σ
RLF→RL {Σ} lf = record {
       states = Fin (exp 2 (finite fin))
     ; astart = FiniteSetF.F←Q finf (λ q → RegularLanguageF.astart lf (FiniteSet.Q←F fin q))
     ; afin =  record { Q←F = λ x → x ; F←Q = λ x → x ; finiso← = λ _ → refl ; finiso→  = λ _ → refl }
     ; automaton = record {
             δ =  delta
           ; aend = dend
        }
   } where
       fin = RegularLanguageF.afin lf
       finf : FiniteSetF (Fin (FiniteSet.finite fin)) (Fin (exp 2 (FiniteSet.finite fin)))
       finf = fin→
       delta :  Fin (exp 2 (finite fin)) → Σ → Fin (exp 2 (finite fin))
       delta q i = FiniteSetF.F←Q finf (λ s → (δ (RegularLanguageF.automaton lf) (λ s → FiniteSetF.Q←F finf q (FiniteSet.F←Q fin s)) i (FiniteSet.Q←F fin s)))
       dend : Fin (exp 2 (finite fin)) → Bool
       dend q = aend (RegularLanguageF.automaton lf) (λ s → FiniteSetF.Q←F finf q (FiniteSet.F←Q fin s ))

-- LF→RL-accept→  : {Σ : Set} → (lf : RegularLanguageF Σ ) → (x : List Σ) → (q :  RegularLanguageF.states lf → Bool) 
--        → accept (automaton (RLF→RL lf)) (FiniteSetF.F←Q fin→ (λ s → q (FiniteSet.Q←F (RegularLanguageF.afin lf) s) ) ) x ≡ true
--            →  accept (RegularLanguageF.automaton lf) q x ≡ true
-- LF→RL-accept→ {Σ} lf [] q ac  = ?
-- LF→RL-accept→ {Σ} lf (x ∷ x₁) q ac  = ?

-- How can we remove functional extensionality from the following proof?

RLF→RL-accept : {Σ : Set} → (lf : RegularLanguageF Σ ) → (x : List Σ) → (q :  RegularLanguageF.states lf → Bool) 
         → ( Extensionality : {a b : Level} {A : Set a} {B : A → Set b} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g )
        → accept (automaton (RLF→RL lf)) (FiniteSetF.F←Q fin→ (λ s → q (FiniteSet.Q←F (RegularLanguageF.afin lf) s) ) ) x 
            ≡ accept (RegularLanguageF.automaton lf) q x
RLF→RL-accept {Σ} lf [] q ext = begin
     aend atm (λ s → FiniteSetF.Q←F fin→   (FiniteSetF.F←Q fin→ (λ s₁ → q (Q←F fin s₁))) (FiniteSet.F←Q fin s )) ≡⟨ cong (aend atm) 
        (ext (λ s → FiniteSetF.finiso→ finf _ (FiniteSet.F←Q fin s )) )  ⟩
     aend atm (λ z → q (Q←F fin (F←Q fin z))) ≡⟨ cong (aend atm) (ext (λ x → cong q (finiso→ fin _) ))  ⟩
     aend atm q  ∎
       where
          open ≡-Reasoning
          atm = RegularLanguageF.automaton lf
          fin = RegularLanguageF.afin lf
          finf = fin→
RLF→RL-accept {Σ} lf (x ∷ x₁) q ext = begin
     accept (automaton (RLF→RL lf)) ( FiniteSetF.F←Q fin→  (λ s → (δ atm (λ s₁ → FiniteSetF.Q←F fin→  (FiniteSetF.F←Q fin→ (λ s₂ → q (Q←F fin s₂))) 
             (FiniteSet.F←Q fin s₁)) x (FiniteSet.Q←F fin s)))) x₁ ≡⟨ cong (λ k →  accept (automaton (RLF→RL lf)) (FiniteSetF.F←Q fin→ k) x₁ ) 
                (ext (λ w → cong (λ k → (δ atm k x (FiniteSet.Q←F fin w))) (ext (λ v → (begin 
                  FiniteSetF.Q←F fin→ (FiniteSetF.F←Q fin→ (λ s₂ → q (Q←F fin s₂))) (F←Q fin v)  ≡⟨ FiniteSetF.finiso→ finf _ (F←Q fin v) ⟩
                  q (Q←F fin (F←Q fin v))  ≡⟨ cong q ( finiso→ fin v)   ⟩
                  q v ∎ )) )))  ⟩
     accept (automaton (RLF→RL lf)) (FiniteSetF.F←Q fin→ (λ s → δ (RegularLanguageF.automaton lf) q x (Q←F (RegularLanguageF.afin lf) s))) x₁ ≡⟨ rec _ ⟩
     accept atm (δ (RegularLanguageF.automaton lf) q x ) x₁ ≡⟨⟩
     accept atm q (x ∷ x₁) ∎
       where
          open ≡-Reasoning
          atm = RegularLanguageF.automaton lf
          fin = RegularLanguageF.afin lf
          finf = fin→ 
          delta :  Fin (exp 2 (finite fin)) → Σ → Fin (exp 2 (finite fin))
          delta q i = FiniteSetF.F←Q fin→  (λ s → (δ (RegularLanguageF.automaton lf) (λ s → FiniteSetF.Q←F fin→  q (FiniteSet.F←Q fin s)) i (FiniteSet.Q←F fin s)))
          rec : (q : RegularLanguageF.states lf → Bool) → 
            accept (automaton (RLF→RL lf)) (FiniteSetF.F←Q fin→ (λ s → q (FiniteSet.Q←F (RegularLanguageF.afin lf) s) ) ) x₁ 
              ≡ accept (RegularLanguageF.automaton lf) q x₁
          rec q = RLF→RL-accept {Σ} lf x₁ q ext


RLF→RL-contain : {Σ : Set} → (lf : RegularLanguageF Σ ) → (x : List Σ)  
    → ( Extensionality : {a b : Level} {A : Set a} {B : A → Set b} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g )
    → contain (RLF→RL lf) x ≡ RegularLanguageF.contain lf x
RLF→RL-contain {Σ} lf x ext = RLF→RL-accept {Σ} lf x (RegularLanguageF.astart lf) ext




