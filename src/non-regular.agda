{-# OPTIONS --cubical-compatible --safe #-}

module non-regular where

open import Data.Nat
open import Data.Empty
open import Data.List
open import Data.Maybe hiding ( map )
open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import logic
open import automaton
open import automaton-ex
open import finiteSetUtil
open import finiteSet
open import Relation.Nullary
open import regular-language
open import nat
open import pumping


open FiniteSet

list-eq :  List  In2 → List  In2 → Bool
list-eq [] [] = true
list-eq [] (x ∷ s1) = false
list-eq (x ∷ s) [] = false
list-eq (i0 ∷ s) (i0 ∷ s1) = false
list-eq (i0 ∷ s) (i1 ∷ s1) = false
list-eq (i1 ∷ s) (i0 ∷ s1) = false
list-eq (i1 ∷ s) (i1 ∷ s1) = list-eq s s1

input-addi0 : ( n :  ℕ )  → List In2 →  List  In2
input-addi0 zero x = x
input-addi0 (suc i) x = i0 ∷ input-addi0 i x

input-addi1 : ( n :  ℕ )  →  List  In2
input-addi1 zero = []
input-addi1 (suc i) = i1 ∷ input-addi1 i

inputnn0 : ( n :  ℕ )  →  List  In2
inputnn0 n = input-addi0 n (input-addi1 n)

--
--  using count of i0 and i1 makes the proof easier
--
inputnn1-i1 : (i : ℕ) → List In2 → Bool
inputnn1-i1 zero [] = true
inputnn1-i1 (suc _) [] = false
inputnn1-i1 zero (i1 ∷ x)  = false
inputnn1-i1 (suc i) (i1 ∷ x)  = inputnn1-i1 i x
inputnn1-i1 zero (i0 ∷ x)  = false
inputnn1-i1 (suc _) (i0 ∷ x)  = false

inputnn1-i0 : (i : ℕ) → List In2 → ℕ ∧ List In2
inputnn1-i0 i [] = ⟪ i , [] ⟫
inputnn1-i0 i (i1 ∷ x)  = ⟪ i , (i1 ∷ x)  ⟫
inputnn1-i0 i (i0 ∷ x)  = inputnn1-i0 (suc i) x

open _∧_

inputnn1 : List In2 → Bool
inputnn1 x = inputnn1-i1 (proj1 (inputnn1-i0 0 x)) (proj2 (inputnn1-i0 0 x))

t1 = inputnn1 ( i0 ∷ i1 ∷ [] )
t2 = inputnn1 ( i0 ∷ i0 ∷ i1 ∷ i1 ∷ [] )
t3 = inputnn1 ( i0 ∷ i0 ∷ i0 ∷ i1 ∷ i1 ∷ [] )

t4 : inputnn1 ( inputnn0 5  )  ≡ true
t4 = refl

t5 : ( n : ℕ ) → Set
t5 n = inputnn1 ( inputnn0 n  )  ≡ true

import Level 

cons-inject : {n : Level.Level } (A : Set n) { a b : A } {x1 x2 : List A} → a ∷ x1 ≡ b ∷ x2 → x1 ≡ x2
cons-inject _ refl = refl

append-[] : {A : Set} {x1 : List A } → x1 ++ [] ≡ x1
append-[] {A} {[]} = refl
append-[] {A} {x ∷ x1} = cong (λ k → x ∷ k) (append-[] {A} {x1} )

open import Data.Nat.Properties
open import  Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality

nn30 : (y : List In2) → (j : ℕ) → proj2 (inputnn1-i0 (suc j) y) ≡ proj2 (inputnn1-i0 j y )
nn30 [] _ = refl
nn30 (i0 ∷ y) j = nn30 y (suc j)
nn30 (i1 ∷ y) _ = refl

nn31 : (y : List In2) → (j : ℕ) → proj1 (inputnn1-i0 (suc j) y) ≡ suc (proj1 (inputnn1-i0 j y ))
nn31 [] _ = refl
nn31 (i0 ∷ y) j = nn31 y (suc j)
nn31 (i1 ∷ y) _ = refl

nn01  : (i : ℕ) → inputnn1 ( inputnn0 i  ) ≡ true
nn01  i = subst₂ (λ j k → inputnn1-i1 j k ≡ true) (sym (nn07 i 0 refl)) (sym (nn09 i)) (nn04 i)  where
     nn07 : (j x : ℕ) → x + j ≡ i  → proj1 ( inputnn1-i0 x (input-addi0 j (input-addi1 i))) ≡ x + j
     nn07 zero x eq with input-addi1 i in eq1
     ... | [] = +-comm 0 _
     ... | i0 ∷ t = ⊥-elim ( nn08 i eq1 ) where
          nn08 : (i : ℕ) → ¬ (input-addi1 i ≡ i0 ∷ t )
          nn08 zero ()
          nn08 (suc i) ()
     ... | i1 ∷ t = +-comm 0 _
     nn07 (suc j) x eq = trans (nn07 j (suc x) (trans (cong (λ k → k + j) (+-comm 1 _ )) (trans (+-assoc x _ _) eq)) )
                                               (trans (+-assoc 1 x _) (trans (cong (λ k → k + j) (+-comm 1 _) ) (+-assoc x 1 _) ))
     nn09 : (x : ℕ) → proj2 ( inputnn1-i0 0 (input-addi0 x (input-addi1 i))) ≡ input-addi1 i
     nn09 zero with input-addi1 i in eq1
     ... | [] = refl
     ... | i0 ∷ t = ⊥-elim ( nn08 i eq1 ) where
          nn08 : (i : ℕ) → ¬ (input-addi1 i ≡ i0 ∷ t )
          nn08 zero ()
          nn08 (suc i) ()
     ... | i1 ∷ t = refl
     nn09 (suc j) = trans (nn30 (input-addi0 j (input-addi1 i)) 0) (nn09 j )
     nn04 : (i : ℕ) → inputnn1-i1 i (input-addi1 i) ≡ true
     nn04 zero = refl
     nn04 (suc i) = nn04 i

half : (x : List In2) → ℕ 
half [] = 0
half (x ∷ []) = 0
half (x ∷ x₁ ∷ x₂) = suc (half x₂)

top-is-i0 : (x : List In2) → Bool
top-is-i0 [] = true
top-is-i0 (i0 ∷ _) = true
top-is-i0 (i1 ∷ _) = false

-- if this is easy, we may have an easy proof
-- nn02  : (x : List In2) → inputnn1 x ≡ true → x ≡ inputnn0 (half x)

--
--  if there is an automaton with n states , which accespt inputnn1, it has a trasition function.
--  The function is determinted by inputs,
--

open RegularLanguage
open Automaton

open _∧_


open RegularLanguage
open import Data.Nat.Properties
open import Data.List.Properties
open import nat

lemmaNN : (r : RegularLanguage In2 ) → ¬ ( (s : List In2)  → isRegular inputnn1  s r )
lemmaNN r Rg = tann {TA.x TAnn} (TA.non-nil-y TAnn ) (TA.xyz=is TAnn) (tr-accept→ (automaton r) _  (astart r) (TA.trace-xyz TAnn) )
       (tr-accept→ (automaton r) _  (astart r) (TA.trace-xyyz TAnn) ) where
    n : ℕ
    n = suc (finite (afin r))
    nn =  inputnn0 n
    nn03 : accept (automaton r) (astart r) nn ≡ true
    nn03 = subst (λ k → k ≡ true ) (Rg nn ) (nn01 n)
    nn09 : (n m : ℕ) → n ≤ n + m
    nn09 zero m = z≤n
    nn09 (suc n) m = s≤s (nn09 n m)
    nn04 :  Trace (automaton r) nn (astart r)
    nn04 = tr-accept← (automaton r) nn (astart r) nn03
    nntrace = tr→qs (automaton r) nn (astart r) nn04
    nn07 : (n : ℕ) →  length (inputnn0 n  ) ≡ n + n
    nn07 i = nn19 i where
        nn17 : (i : ℕ) → length (input-addi1 i) ≡ i
        nn17 zero = refl
        nn17 (suc i)= cong suc (nn17 i)
        nn18 : (i j : ℕ) →  length (input-addi0 j (input-addi1 i)) ≡ j +  length (input-addi1 i )
        nn18 i zero = refl
        nn18 i (suc j)= cong suc (nn18 i j)
        nn19 : (i : ℕ) → length (input-addi0 i ( input-addi1 i )) ≡ i + i
        nn19 i = begin
            length (input-addi0 i ( input-addi1 i )) ≡⟨ nn18 i i ⟩
            i + length (input-addi1 i)  ≡⟨ cong (λ k → i + k) ( nn17 i) ⟩
            i + i  ∎ where open ≡-Reasoning
    nn05 : length nntrace > finite (afin r)
    nn05 = begin
         suc (finite (afin r))  ≤⟨ nn09 _ _ ⟩
         n + n   ≡⟨ sym (nn07 n) ⟩
         length (inputnn0 n  ) ≡⟨ tr→qs=is (automaton r) (inputnn0 n  ) (astart r) nn04 ⟩
         length nntrace ∎  where open ≤-Reasoning
    nn06 : Dup-in-list ( afin r) (tr→qs (automaton r) nn (astart r) nn04)
    nn06 = dup-in-list>n (afin r) nntrace nn05

    TAnn : TA (automaton r) (astart r) nn
    TAnn = pumping-lemma (automaton r) (afin r) (astart r) (Dup-in-list.dup nn06) nn nn04 (Dup-in-list.is-dup nn06)

    open import Tactic.MonoidSolver using (solve; solve-macro)

    -- there is a counter example
    --
    tann : {x y z : List In2} → ¬ y ≡ []
       → x ++ y ++ z ≡ nn
       → accept (automaton r) (astart r) (x ++ y ++ z) ≡ true → ¬ (accept (automaton r) (astart r) (x ++ y ++ y ++ z)  ≡ true )
    tann {x} {y} {z} ny eq axyz axyyz = ¬-bool (nn10 x y z ny (trans (Rg (x ++ y ++ z)) axyz ) ) (trans (Rg (x ++ y ++ y ++ z)) axyyz ) where
          count0 : (x : List In2) → ℕ
          count0 [] = 0
          count0 (i0 ∷ x) = suc (count0 x)
          count0 (i1 ∷ x) = count0 x
          count1 : (x : List In2) → ℕ
          count1 [] = 0
          count1 (i1 ∷ x) = suc (count1 x)
          count1 (i0 ∷ x) = count1 x
          -- 
          -- prove some obvious fact
          --
          c0+1=n : (x : List In2 ) → count0 x + count1 x ≡ length x
          c0+1=n [] = refl
          c0+1=n (i0 ∷ t) = cong suc ( c0+1=n t )
          c0+1=n (i1 ∷ t) = begin
             count0 t + suc (count1 t) ≡⟨ sym (+-assoc (count0 t) _ _) ⟩
             (count0 t + 1 ) + count1 t ≡⟨ cong (λ k → k + count1 t) (+-comm _ 1 ) ⟩
             suc (count0 t + count1 t) ≡⟨ cong suc ( c0+1=n t )  ⟩
             suc (length t) ∎ where open  ≡-Reasoning
          --
          nn15 : (x : List In2 ) → inputnn1 x ≡ true → count0 x ≡ count1 x
          nn15 x eq = nn18 where
               nn17 : (x : List In2 ) → (count0 x ≡ proj1 (inputnn1-i0 0 x) + count0 (proj2 (inputnn1-i0 0 x)))
                                      ∧ (count1 x ≡ 0                       + count1 (proj2 (inputnn1-i0 0 x)))
               nn17 [] = ⟪ refl , refl ⟫
               nn17 (i0 ∷ t ) with nn17 t
               ... | ⟪ eq1 , eq2 ⟫ = ⟪ begin
                     suc (count0 t ) ≡⟨ cong suc eq1 ⟩
                     suc (proj1 (inputnn1-i0 0 t) + count0 (proj2 (inputnn1-i0 0 t))) ≡⟨ cong₂ _+_ (sym (nn31 t 0)) (cong count0 (sym (nn30 t 0)))  ⟩
                          proj1 (inputnn1-i0 1 t) + count0 (proj2 (inputnn1-i0 1 t)) ∎
                       , trans eq2 (cong count1 (sym (nn30 t 0)))  ⟫ where
                  open ≡-Reasoning
                  nn20 : proj2 (inputnn1-i0 1 t) ≡ proj2 (inputnn1-i0 0 t)
                  nn20 = nn30 t 0
               nn17 (i1 ∷ x₁) = ⟪ refl , refl  ⟫
               nn19 : (n : ℕ) → (y : List In2 ) → inputnn1-i1 n y ≡ true → (count0 y ≡ 0) ∧ (count1 y ≡ n)
               nn19 zero [] eq = ⟪ refl , refl ⟫
               nn19 zero (i0 ∷ y) ()
               nn19 zero (i1 ∷ y) ()
               nn19 (suc i) (i1 ∷ y) eq with nn19 i y eq
               ... | t = ⟪ proj1 t , cong suc (proj2 t ) ⟫
               nn18 :  count0 x ≡ count1 x
               nn18 = begin
                     count0 x ≡⟨ proj1 (nn17 x) ⟩
                     proj1 (inputnn1-i0 0 x) + count0 (proj2 (inputnn1-i0 0 x))  ≡⟨ cong (λ k → proj1 (inputnn1-i0 0 x) + k)
                                                              (proj1 (nn19 (proj1 (inputnn1-i0 0 x)) (proj2 (inputnn1-i0 0 x)) eq)) ⟩
                     proj1 (inputnn1-i0 0 x) + 0                                 ≡⟨ +-comm _ 0 ⟩
                     0                       + proj1 (inputnn1-i0 0 x)           ≡⟨ cong (λ k → 0 + k) (sym (proj2 (nn19 _ _ eq))) ⟩
                     0                       + count1 (proj2 (inputnn1-i0 0 x))  ≡⟨ sym (proj2 (nn17 x)) ⟩
                     count1 x ∎ where open ≡-Reasoning
          distr0 : (x y : List In2 ) → count0 (x ++ y ) ≡ count0 x + count0 y
          distr0 [] y = refl
          distr0 (i0 ∷ x)  y = cong suc (distr0 x y)
          distr0 (i1 ∷ x)  y = distr0 x y
          distr1 : (x y : List In2 ) → count1 (x ++ y ) ≡ count1 x + count1 y
          distr1 [] y = refl
          distr1 (i1 ∷ x)  y = cong suc (distr1 x y)
          distr1 (i0 ∷ x)  y = distr1 x y
          --
          --  i0 .. i0 ∷ i1 .. i1 sequece does not contains i1 → i0 transition
          --
          record i1i0 (z : List In2) : Set where
             field
                a b : List In2
                i10 : z ≡ a ++ (i1 ∷ i0 ∷ b )
          nn12 : (x : List In2 ) → inputnn1 x ≡ true → ¬ i1i0 x
          nn12 x eq = nn17 x 0 eq  where
               nn17 : (x : List In2 ) → (i : ℕ)
                  → inputnn1-i1 (proj1 (inputnn1-i0 i x)) (proj2 (inputnn1-i0 i x)) ≡ true   → ¬ i1i0 x
               nn17 [] i eq li with i1i0.a li | i1i0.i10 li
               ... | [] | ()
               ... | x ∷ s | ()
               nn17 (i0 ∷ x₁) i eq li = nn17 x₁ (suc i) eq record { a = nn18 (i1i0.a li) (i1i0.i10 li) ; b = i1i0.b li
                 ; i10 = nn19 (i1i0.a li) (i1i0.i10 li) } where
                    -- first half
                    nn18 : (a : List In2 ) → i0 ∷ x₁ ≡ a ++ ( i1 ∷ i0 ∷ i1i0.b li) → List In2
                    nn18 (i0 ∷ t) eq = t
                    nn19 : (a : List In2 ) → (eq : i0 ∷ x₁ ≡ a ++ ( i1 ∷ i0 ∷ i1i0.b li)  )
                       → x₁ ≡ nn18 a eq ++ i1 ∷ i0 ∷ i1i0.b li
                    nn19 (i0 ∷ a) eq = cons-inject In2 eq
               nn17 (i1 ∷ x₁) i eq li = nn20 (i1 ∷ x₁) i eq li where
                    -- second half
                    nn20 : (x : List In2) → (i : ℕ) → inputnn1-i1 i x ≡ true → i1i0 x → ⊥
                    nn20 x i eq li = nn21 (i1i0.a li) x i eq (i1i0.i10 li)  where
                       nn21 : (a x : List In2) → (i : ℕ) → inputnn1-i1 i x ≡ true  → x ≡ a ++ i1 ∷ i0 ∷ i1i0.b li → ⊥
                       nn21 [] [] zero eq1 ()
                       nn21 (i0 ∷ a) [] zero eq1 ()
                       nn21 (i1 ∷ a) [] zero eq1 ()
                       nn21 a (i0 ∷ x₁) zero () eq0
                       nn21 [] (i0 ∷ x₁) (suc i) () eq0
                       nn21 (x ∷ a) (i0 ∷ x₁) (suc i) () eq0
                       nn21 [] (i1 ∷ i0 ∷ x₁) (suc zero) () eq0
                       nn21 [] (i1 ∷ i0 ∷ x₁) (suc (suc i)) () eq0
                       nn21 (i1 ∷ a) (i1 ∷ x₁) (suc i) eq1 eq0 = nn21 a x₁ i eq1 (cons-inject In2 eq0)
          nn11 : (x y z : List In2 ) → ¬ y ≡ [] → inputnn1  (x ++ y ++ z) ≡ true → ¬ ( inputnn1  (x ++ y ++ y ++ z) ≡ true )
          nn11 x y z ny xyz xyyz = ⊥-elim ( nn12 (x ++ y ++ y ++ z ) xyyz record { a = x ++ i1i0.a (bb23 bb22 )
                                                 ; b = i1i0.b (bb23 bb22) ++ z ; i10 = bb24 } )  where
               --
               -- we need simple calcuraion to obtain count0 y ≡ count1 y
               --
               nn21 : count0 x + count0 y + count0 y + count0 z ≡ count1 x + count1 y + count1 y + count1 z
               nn21 = begin
                    (count0 x + count0 y + count0 y) + count0 z ≡⟨ solve +-0-monoid ⟩
                    count0 x + (count0 y + (count0 y + count0 z))  ≡⟨ sym (cong (λ k → count0 x + (count0 y + k)) (distr0  y _ )) ⟩
                    count0 x + (count0 y + count0 (y ++ z))  ≡⟨ sym (cong (λ k → count0 x + k) (distr0  y _ )) ⟩
                    count0 x + (count0 (y ++ y ++ z))  ≡⟨ sym (distr0  x _ ) ⟩
                    count0 (x ++ y ++ y ++ z) ≡⟨ nn15 (x ++ y ++ y ++ z) xyyz ⟩
                    count1 (x ++ y ++ y ++ z) ≡⟨ distr1 x _ ⟩
                    count1 x + (count1 (y ++ y ++ z))  ≡⟨ cong (λ k → count1 x + k) (distr1  y _ ) ⟩
                    count1 x + (count1 y + count1 (y ++ z))  ≡⟨ (cong (λ k → count1 x + (count1 y + k)) (distr1  y _ )) ⟩
                    count1 x + (count1 y + (count1 y + count1 z))  ≡⟨ solve +-0-monoid ⟩
                    count1 x + count1 y + count1 y + count1 z ∎ where open ≡-Reasoning
               nn20 : count0 x + count0 y + count0 z ≡ count1 x + count1 y + count1 z
               nn20 = begin
                    count0 x + count0 y + count0 z ≡⟨ solve +-0-monoid ⟩
                    count0 x + (count0 y + count0 z) ≡⟨ cong (λ k → count0 x + k) (sym (distr0 y z)) ⟩
                    count0 x + (count0 (y ++ z)) ≡⟨ sym (distr0 x _) ⟩
                    count0 (x ++ (y ++ z))  ≡⟨ nn15 (x ++ y ++ z) xyz ⟩
                    count1 (x ++ (y ++ z))  ≡⟨ distr1 x _  ⟩
                    count1 x + count1 (y ++ z)  ≡⟨ cong (λ k → count1 x + k) (distr1 y z) ⟩
                    count1 x + (count1 y + count1 z)  ≡⟨ solve +-0-monoid ⟩
                    count1 x + count1 y + count1 z ∎ where open ≡-Reasoning
               -- this takes very long time to check and needs 10GB
               bb22 : count0 y ≡ count1 y
               bb22 = begin
                    count0 y ≡⟨ ? ⟩
--                     count0 y ≡⟨ sym ( +-cancelʳ-≡  (count1 z  + count0 x + count0 y + count0 z) (count1 y) (count0 y)  (+-cancelˡ-≡ _ (count1 x + count1 y) (
--                        begin 
--                        count1 x + count1 y + (count1 y + (count1 z + count0 x + count0 y + count0 z))  ≡⟨ solve +-0-monoid  ⟩
--                        (count1 x + count1 y + count1 y + count1 z)  + (count0 x + count0 y + count0 z) ≡⟨ sym (cong₂ _+_ nn21 (sym nn20)) ⟩
--                        (count0 x + count0 y + count0 y + count0 z)  + (count1 x + count1 y + count1 z) ≡⟨  +-comm _ (count1 x + count1 y + count1 z) ⟩
--                        (count1 x + count1 y + count1 z) + (count0 x + count0 y + count0 y + count0 z)    ≡⟨  solve +-0-monoid ⟩
--                         count1 x + count1 y + (count1 z + (count0 x + count0 y)) + count0 y + count0 z    
--                             ≡⟨  cong (λ k → count1 x + count1 y + (count1 z + k) + count0 y + count0 z) (+-comm (count0 x) _) ⟩
--                         count1 x + count1 y + (count1 z + (count0 y + count0 x)) + count0 y + count0 z    ≡⟨ solve +-0-monoid ⟩
--                         count1 x + count1 y + ((count1 z + count0 y) + count0 x) + count0 y + count0 z    
--                             ≡⟨  cong (λ k → count1 x + count1 y + (k + count0 x) + count0 y + count0 z    ) (+-comm (count1 z) _) ⟩
--                         count1 x + count1 y + (count0 y + count1 z + count0 x) + count0 y + count0 z    ≡⟨  solve +-0-monoid ⟩
--                         count1 x + count1 y + (count0 y + (count1 z + count0 x + count0 y + count0 z))    ∎ ))) ⟩
                    count1 y ∎ where open ≡-Reasoning
               --
               --  y contains i0 and i1 , so we have i1 → i0 transition in y ++ y
               --
               bb23 : count0 y ≡ count1 y → i1i0 (y ++ y)
               bb23 eq = bb25 y y bb26 (subst (λ k → 0 < k ) (sym eq) bb26)  where
                    bb26 : 0 < count1 y
                    bb26 with <-cmp 0 (count1 y)
                    ... | tri< a ¬b ¬c = a
                    ... | tri≈ ¬a b ¬c = ⊥-elim (nat-≡< (sym bb27 ) (0<ly y ny) ) where
                         0<ly : (y : List In2) → ¬ y ≡ []  → 0 < length y
                         0<ly [] ne = ⊥-elim ( ne refl )
                         0<ly (x ∷ y) ne = s≤s z≤n
                         bb27 : length y ≡ 0
                         bb27 = begin
                            length y ≡⟨ sym (c0+1=n y) ⟩
                            count0 y + count1 y ≡⟨ cong (λ k → k + count1 y ) eq  ⟩
                            count1 y + count1 y ≡⟨ cong₂ _+_ (sym b) (sym b) ⟩
                            0 ∎ where open ≡-Reasoning
                    bb25 : (x y : List In2 ) →  0 < count1 x → 0 < count0 y → i1i0 (x ++ y)
                    bb25 (i0 ∷ x₁) y 0<x 0<y with bb25 x₁ y 0<x 0<y
                    ... | t = record { a = i0 ∷ i1i0.a t ; b = i1i0.b t ; i10 = cong (i0 ∷_) (i1i0.i10 t) }
                    bb25 (i1 ∷ []) y 0<x 0<y = bb27 y 0<y where
                        bb27 : (y : List In2 ) → 0 < count0 y → i1i0 (i1 ∷ y )
                        bb27 (i0 ∷ y) 0<y = record { a = [] ; b = y ; i10 = refl }
                        bb27 (i1 ∷ y) 0<y with bb27 y 0<y
                        ... | t = record { a = i1 ∷ i1i0.a t ; b = i1i0.b t ; i10 = cong (i1 ∷_) (i1i0.i10 t) }
                    bb25 (i1 ∷ i0 ∷ x₁) y 0<x 0<y = record { a = [] ; b = x₁ ++ y ; i10 = refl }
                    bb25 (i1 ∷ i1 ∷ x₁) y (s≤s z≤n) 0<y with bb25 (i1 ∷ x₁) y (s≤s z≤n) 0<y
                    ... | t = record { a = i1 ∷ i1i0.a t ; b = i1i0.b t ; i10 = cong (i1 ∷_) (i1i0.i10 t) }
               bb24 : x ++ y ++ y ++ z ≡ (x ++ i1i0.a (bb23 bb22)) ++ i1 ∷ i0 ∷ i1i0.b (bb23 bb22) ++ z
               bb24 = begin
                    x ++ y ++ y ++ z ≡⟨ solve (++-monoid In2) ⟩
                    x ++ (y ++ y) ++ z ≡⟨ cong (λ k → x ++ k ++ z) (i1i0.i10 (bb23 bb22)) ⟩
                    x ++ (i1i0.a (bb23 bb22) ++ i1 ∷ i0 ∷ i1i0.b (bb23 bb22)) ++ z ≡⟨ cong (λ k → x ++ k)  -- solver does not work here
                            (++-assoc (i1i0.a (bb23 bb22)) (i1 ∷ i0 ∷ i1i0.b (bb23 bb22)) z ) ⟩
                    x ++ (i1i0.a (bb23 bb22) ++ (i1 ∷ i0 ∷ i1i0.b (bb23 bb22) ++ z)) ≡⟨ sym (++-assoc x _ _ ) ⟩
                    (x ++ i1i0.a (bb23 bb22)) ++ i1 ∷ i0 ∷ i1i0.b (bb23 bb22) ++ z ∎ where open ≡-Reasoning

          nn10 : (x y z : List In2 ) → ¬ y ≡ [] → inputnn1  (x ++ y ++ z) ≡ true → inputnn1  (x ++ y ++ y ++ z) ≡ false
          nn10 x y z my eq with inputnn1  (x ++ y ++ y ++ z)  in eq1
          ... | true = ⊥-elim ( nn11 x y z my eq eq1 )
          ... | false  = refl






