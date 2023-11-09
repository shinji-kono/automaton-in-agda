{-# OPTIONS #-}

module finiteFunc  where

open import Data.Nat hiding ( _≟_ )
open import Data.Fin renaming ( _<_ to _<<_ ; _>_ to _f>_ ; _≟_ to _f≟_ ) hiding (_≤_ ; pred )
open import Data.Fin.Properties hiding ( <-trans ; ≤-trans ; ≤-refl ; <-irrelevant ) renaming ( <-cmp to <-fcmp )
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import logic
open import nat
open import finiteSet
open import finiteSetUtil
open import fin
open import Data.Nat.Properties as NP  hiding ( _≟_ )

open import Axiom.Extensionality.Propositional
open import Level hiding (suc ; zero)

open import Level renaming ( suc to Suc ; zero to Zero) 
postulate f-extensionality : { n : Level}  → Axiom.Extensionality.Propositional.Extensionality n n -- (Level.suc n)
open import Data.Vec hiding ( map ; length )
import Data.Product


-- we cannot simply use f ≡ g for f : Q → A in Bijection of List Bool and (finite → Bool )
-- what we can say is theres a fuction which elementwise equal

F2L-iso : { Q : Set } → (fin : FiniteSet Q ) → (x : Vec Bool (FiniteSet.finite fin) ) → F2L fin a<sa (λ q _ → List2Func fin a<sa x q ) ≡ x
F2L-iso {Q} fin x = f2l m a<sa x where
  m = FiniteSet.finite fin
  f2l : (n : ℕ ) → (n<m : n < suc m )→ (x : Vec Bool n ) → F2L fin n<m (λ q q<n → List2Func fin n<m x q )  ≡ x 
  f2l zero (s≤s z≤n) [] = refl
  f2l (suc n) (s≤s n<m) (h ∷ t ) = lemma1 lemma2 lemma3f where
    lemma1 : {n : ℕ } → {h h1 : Bool } → {t t1 : Vec Bool n } → h ≡ h1 → t ≡ t1 →  h ∷ t ≡ h1 ∷ t1
    lemma1 refl refl = refl
    lemma2 : List2Func fin (s≤s n<m) (h ∷ t) (FiniteSet.Q←F fin (fromℕ< n<m)) ≡ h
    lemma2 with FiniteSet.F←Q fin (FiniteSet.Q←F fin (fromℕ< n<m))  ≟ fromℕ< n<m
    lemma2 | yes p = refl
    lemma2 | no ¬p = ⊥-elim ( ¬p (FiniteSet.finiso← fin _) )
    lemma4 : (q : Q ) → toℕ (FiniteSet.F←Q fin q ) < n → List2Func fin (s≤s n<m) (h ∷ t) q ≡ List2Func fin (NP.<-trans n<m a<sa) t q
    lemma4 q _ with FiniteSet.F←Q fin q ≟ fromℕ< n<m 
    lemma4 q lt | yes p = ⊥-elim ( nat-≡< (toℕ-fromℕ< n<m) (lemma5 n lt (cong (λ k → toℕ k) p))) where 
        lemma5 : {j k : ℕ } → ( n : ℕ) → suc j ≤ n → j ≡ k → k < n
        lemma5 {zero} (suc n) (s≤s z≤n) refl = s≤s  z≤n
        lemma5 {suc j} (suc n) (s≤s lt) refl = s≤s (lemma5 {j} n lt refl)
    lemma4 q _ | no ¬p = refl
    lemma3f :  F2L fin (NP.<-trans n<m a<sa) (λ q q<n → List2Func fin (s≤s n<m) (h ∷ t) q  ) ≡ t
    lemma3f = begin 
         F2L fin (NP.<-trans n<m a<sa) (λ q q<n → List2Func fin (s≤s n<m) (h ∷ t) q )
       ≡⟨ cong (λ k → F2L fin (NP.<-trans n<m a<sa) ( λ q q<n → k q q<n ))
              (f-extensionality ( λ q →  
              (f-extensionality ( λ q<n →  lemma4 q q<n )))) ⟩
         F2L fin (NP.<-trans n<m a<sa) (λ q q<n → List2Func fin (NP.<-trans n<m a<sa) t q )
       ≡⟨ f2l n (NP.<-trans n<m a<sa ) t ⟩
         t
       ∎  where
         open ≡-Reasoning

open Bijection

fin→ : {A : Set} → FiniteSet A → FiniteSet (A → Bool ) 
fin→ {A}  fin = iso-fin fin2List iso where
    a = FiniteSet.finite fin
    iso : Bijection (Vec Bool a ) (A → Bool)
    fun← iso x = F2L fin a<sa ( λ q _ → x q )
    fun→ iso x = List2Func fin a<sa x 
    fiso← iso x  =  F2L-iso fin x 
    fiso→ iso f = lemma where
      lemma : List2Func fin a<sa (F2L fin a<sa (λ q _ → f q)) ≡ f
      lemma = f-extensionality ( λ q → L2F-iso fin f q )

    
