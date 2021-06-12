module bijection where

open import Level renaming ( zero to Zero ; suc to Suc )
open import Data.Nat
open import Data.Maybe
open import Data.List hiding ([_])
open import Data.Nat.Properties
open import Relation.Nullary
open import Data.Empty
open import Data.Unit
open import  Relation.Binary.Core hiding (_⇔_)
open import  Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality

open import logic

record Bijection {n m : Level} (R : Set n) (S : Set m) : Set (n Level.⊔ m)  where
   field
       fun←  :  S → R
       fun→  :  R → S
       fiso← : (x : R)  → fun← ( fun→ x )  ≡ x 
       fiso→ : (x : S ) → fun→ ( fun← x )  ≡ x 

injection :  {n m : Level} (R : Set n) (S : Set m) (f : R → S ) → Set (n Level.⊔ m)
injection R S f = (x y : R) → f x ≡ f y → x ≡ y

open Bijection 

b→injection0 : {n m : Level} (R : Set n) (S : Set m)  → (b : Bijection R S) → injection R S (fun→ b)
b→injection0 R S b x y eq = begin
          x
        ≡⟨ sym ( fiso← b x ) ⟩
          fun← b ( fun→ b x )
        ≡⟨ cong (λ k → fun← b k ) eq ⟩
          fun← b ( fun→ b y )
        ≡⟨  fiso← b y  ⟩
          y  
        ∎  where open ≡-Reasoning

b→injection1 : {n m : Level} (R : Set n) (S : Set m)  → (b : Bijection R S) → injection S R (fun← b)
b→injection1 R S b x y eq = trans (  sym ( fiso→ b x ) ) (trans (  cong (λ k → fun→ b k ) eq ) ( fiso→ b y  ))

--  ¬ A = A → ⊥ 

diag : {S : Set }  (b : Bijection  ( S → Bool ) S) → S → Bool
diag b n = not (fun← b n n)

diagonal : { S : Set } → ¬ Bijection  ( S → Bool ) S
diagonal {S} b = diagn1 (fun→ b (diag b) ) refl where
    diagn1 : (n : S ) → ¬ (fun→ b (diag b) ≡ n ) 
    diagn1 n dn = ¬t=f (diag b n ) ( begin
           not (diag b n)
        ≡⟨⟩
           not (not fun← b n n)
        ≡⟨ cong (λ k → not (k  n) ) (sym (fiso← b _)) ⟩
           not (fun← b (fun→ b (diag b))  n)
        ≡⟨ cong (λ k → not (fun← b k n) ) dn ⟩
           not (fun← b n n)
        ≡⟨⟩
           diag b n 
        ∎ ) where open ≡-Reasoning

b1 : (b : Bijection  ( ℕ → Bool ) ℕ) → ℕ 
b1 b = fun→ b (diag b)

b-iso : (b : Bijection  ( ℕ → Bool ) ℕ) → fun← b (b1 b) ≡ (diag b)
b-iso b = fiso← b _

to1 : {n : Level} {R : Set n} → Bijection ℕ R → Bijection ℕ (⊤ ∨ R )
to1 {n} {R} b = record {
       fun←  = to11
     ; fun→  = to12
     ; fiso← = to13
     ; fiso→ = to14
   } where
       to11 : ⊤ ∨ R → ℕ
       to11 (case1 tt) = 0
       to11 (case2 x) = suc ( fun← b x )
       to12 : ℕ → ⊤ ∨ R
       to12 zero = case1 tt
       to12 (suc n) = case2 ( fun→ b n)
       to13 : (x : ℕ) → to11 (to12 x) ≡ x
       to13 zero = refl
       to13 (suc x) = cong suc (fiso← b x)
       to14 : (x : ⊤ ∨ R) → to12 (to11 x) ≡ x
       to14 (case1 x) = refl
       to14 (case2 x) = cong case2 (fiso→ b x)

open _∧_

open import nat

open ≡-Reasoning

--   []     0
--   0    → 1
--   1    → 2
--   01   → 3
--   11   → 4
--   ...
--
{-# TERMINATING #-}
LBℕ : Bijection ℕ ( List Bool ) 
LBℕ = record {
       fun←  = λ x → lton x 
     ; fun→  = λ n → ntol n 
     ; fiso← = lbiso0 
     ; fiso→ = lbisor
   } where
     lton1 : List Bool → ℕ
     lton1 [] = 0
     lton1 (true ∷ t) = suc (lton1 t + lton1 t)
     lton1 (false ∷ t) = lton1 t + lton1 t
     lton : List Bool → ℕ
     lton [] = 0
     lton x  = suc (lton1 x)
     ntol1 : ℕ → List Bool 
     ntol1 0 = []
     ntol1 (suc x) with div2 (suc x)
     ... | ⟪ x1 , true  ⟫ = true  ∷ ntol1 x1 -- non terminating
     ... | ⟪ x1 , false ⟫ = false ∷ ntol1 x1
     ntol : ℕ → List Bool 
     ntol 0 = []
     ntol 1 = false ∷ []
     ntol (suc n) = ntol1 n
     xx :   (x : ℕ ) → List Bool ∧ ℕ
     xx x = ⟪ (ntol x) , lton ((ntol x))  ⟫
     add11 : (x1 : ℕ ) → suc x1 + suc x1 ≡ suc (suc  (x1 + x1))
     add11 zero = refl
     add11 (suc x) = cong (λ k → suc (suc k)) (trans (+-comm x _) (cong suc (+-comm _ x)))
     add12 : (x1 x : ℕ ) → suc x1 + x ≡ x1 + suc x
     add12 zero x = refl
     add12 (suc x1) x = cong suc (add12 x1 x)
     ---- div2-eq : (x : ℕ ) → div2-rev ( div2 x ) ≡ x
     div20 : (x x1 : ℕ ) → div2 (suc x) ≡ ⟪ x1 , false ⟫ → x1 + x1 ≡ suc x
     div20 x x1 eq = begin
         x1 + x1 ≡⟨ cong (λ k → div2-rev k ) (sym eq) ⟩
         div2-rev (div2 (suc x)) ≡⟨ div2-eq _ ⟩
         suc x ∎ 
     div21 : (x x1 : ℕ ) → div2 (suc x) ≡ ⟪ x1 , true ⟫  → suc  (x1 + x1) ≡ suc x
     div21 x x1 eq = begin
         suc  (x1 + x1) ≡⟨ cong (λ k → div2-rev k ) (sym eq) ⟩
         div2-rev (div2 (suc x)) ≡⟨ div2-eq _ ⟩
         suc x ∎ 
     lbiso1 :  (x : ℕ) → suc (lton1 (ntol1 x)) ≡ suc x
     lbiso1 zero = refl
     lbiso1 (suc x) with div2 (suc x) | inspect div2 (suc x)
     ... | ⟪ x1 , true ⟫ | record { eq = eq1 } = begin
         suc (suc (lton1 (ntol1 x1) + lton1 (ntol1 x1))) ≡⟨ sym (add11 _) ⟩
         suc (lton1 (ntol1 x1)) + suc (lton1 (ntol1 x1)) ≡⟨ cong ( λ k → k + k ) (lbiso1 x1) ⟩
         suc x1 + suc x1 ≡⟨ add11 x1 ⟩
         suc (suc  (x1 + x1)) ≡⟨ cong suc (div21 x x1 eq1) ⟩
         suc (suc x) ∎ 
     ... | ⟪ x1 , false ⟫ | record { eq = eq1 } = begin
         suc (lton1 (ntol1 x1) + lton1 (ntol1 x1)) ≡⟨ cong ( λ k → k + lton1 (ntol1 x1) ) (lbiso1 x1) ⟩
         suc x1 + lton1 (ntol1 x1) ≡⟨ add12 _ _ ⟩
         x1 + suc (lton1 (ntol1 x1)) ≡⟨ cong ( λ k → x1 + k )  (lbiso1 x1) ⟩
         x1 + suc x1 ≡⟨ +-comm x1 _ ⟩
         suc (x1 + x1) ≡⟨ cong suc (div20 x x1 eq1) ⟩
         suc (suc x) ∎ 
     lbiso0 :  (x : ℕ) → lton (ntol x)  ≡ x
     lbiso0 zero = refl
     lbiso0 (suc zero) = refl
     lbiso0 (suc (suc x)) = subst (λ k → k ≡ suc (suc x)) (hh x) ( lbiso1 (suc x)) where
        hh : (x : ℕ ) → suc (lton1 (ntol1 (suc x))) ≡ lton (ntol (suc (suc x)))
        hh x with div2 (suc x)
        ... | ⟪ _ , true ⟫ = refl
        ... | ⟪ _ , false ⟫ = refl
     lbisor0 :  (x : List Bool) → ntol1 (lton1 (true ∷ x))  ≡ true ∷ x
     lbisor0 = {!!}
     lbisor1 :  (x : List Bool) → ntol1 (lton1 (false ∷ x))  ≡ false ∷ x
     lbisor1 = {!!}
     lbisor :  (x : List Bool) → ntol (lton x)  ≡ x
     lbisor [] = refl
     lbisor (false ∷ []) = refl
     lbisor (true ∷ []) = refl
     lbisor (false ∷ t) = trans {!!} ( lbisor1 t ) 
     lbisor (true ∷  t) = trans {!!} ( lbisor0 t ) 


