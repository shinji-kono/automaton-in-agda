{-# OPTIONS --allow-unsolved-metas #-} 

module fin where

open import Data.Fin hiding (_<_ ; _≤_ ; _>_ )
open import Data.Fin.Properties hiding ( <-trans )
open import Data.Nat
open import logic
open import nat
open import Relation.Binary.PropositionalEquality


-- toℕ<n
fin<n : {n : ℕ} {f : Fin n} → toℕ f < n
fin<n {_} {zero} = s≤s z≤n
fin<n {suc n} {suc f} = s≤s (fin<n {n} {f})

-- toℕ≤n
fin≤n : {n : ℕ} (f : Fin (suc n)) → toℕ f ≤ n
fin≤n {_} zero = z≤n
fin≤n {suc n} (suc f) = s≤s (fin≤n {n} f)

pred<n : {n : ℕ} {f : Fin (suc n)} → n > 0  → Data.Nat.pred (toℕ f) < n
pred<n {suc n} {zero} (s≤s z≤n) = s≤s z≤n
pred<n {suc n} {suc f} (s≤s z≤n) = fin<n

fin<asa : {n : ℕ} → toℕ (fromℕ< {n} a<sa) ≡ n
fin<asa = toℕ-fromℕ< nat.a<sa

-- fromℕ<-toℕ
toℕ→from : {n : ℕ} {x : Fin (suc n)} → toℕ x ≡ n → fromℕ n ≡ x
toℕ→from {0} {zero} refl = refl
toℕ→from {suc n} {suc x} eq = cong (λ k → suc k ) ( toℕ→from {n} {x} (cong (λ k → Data.Nat.pred k ) eq ))

0≤fmax : {n : ℕ } → (# 0) Data.Fin.≤ fromℕ< {n} a<sa
0≤fmax  = subst (λ k → 0 ≤ k ) (sym (toℕ-fromℕ< a<sa)) z≤n

0<fmax : {n : ℕ } → (# 0) Data.Fin.< fromℕ< {suc n} a<sa
0<fmax = subst (λ k → 0 < k ) (sym (toℕ-fromℕ< a<sa)) (s≤s z≤n)

-- toℕ-injective
i=j : {n : ℕ} (i j : Fin n) → toℕ i ≡ toℕ j → i ≡ j
i=j {suc n} zero zero refl = refl
i=j {suc n} (suc i) (suc j) eq = cong ( λ k → suc k ) ( i=j i j (cong ( λ k → Data.Nat.pred k ) eq) )

-- raise 1
fin+1 :  { n : ℕ } → Fin n → Fin (suc n)
fin+1  zero = zero 
fin+1  (suc x) = suc (fin+1 x)

open import Data.Nat.Properties as NatP  hiding ( _≟_ )

fin+1≤ : { i n : ℕ } → (a : i < n)  → fin+1 (fromℕ< a) ≡ fromℕ< (<-trans a a<sa)
fin+1≤ {0} {suc i} (s≤s z≤n) = refl
fin+1≤ {suc n} {suc (suc i)} (s≤s (s≤s a)) = cong (λ k → suc k ) ( fin+1≤ {n} {suc i} (s≤s a) )

fin+1-toℕ : { n : ℕ } → { x : Fin n} → toℕ (fin+1 x) ≡ toℕ x
fin+1-toℕ {suc n} {zero} = refl
fin+1-toℕ {suc n} {suc x} = cong (λ k → suc k ) (fin+1-toℕ {n} {x})

open import Relation.Nullary 
open import Data.Empty

fin-1 :  { n : ℕ } → (x : Fin (suc n)) → ¬ (x ≡ zero )  → Fin n
fin-1 zero ne = ⊥-elim (ne refl )
fin-1 {n} (suc x) ne = x 

fin-1-sx : { n : ℕ } → (x : Fin n) →  fin-1 (suc x) (λ ()) ≡ x 
fin-1-sx zero = refl
fin-1-sx (suc x) = refl

fin-1-xs : { n : ℕ } → (x : Fin (suc n)) → (ne : ¬ (x ≡ zero ))  → suc (fin-1 x ne ) ≡ x
fin-1-xs zero ne = ⊥-elim ( ne refl )
fin-1-xs (suc x) ne = refl

-- suc-injective
-- suc-eq : {n : ℕ } {x y : Fin n} → Fin.suc x ≡ Fin.suc y  → x ≡ y
-- suc-eq {n} {x} {y} eq = subst₂ (λ j k → j ≡ k ) {!!} {!!} (cong (λ k → Data.Fin.pred k ) eq )

-- this is refl
lemma3 : {a b : ℕ } → (lt : a < b ) → fromℕ< (s≤s lt) ≡ suc (fromℕ< lt)
lemma3 (s≤s lt) = refl

-- fromℕ<-toℕ 
lemma12 : {n m : ℕ } → (n<m : n < m ) → (f : Fin m )  → toℕ f ≡ n → f ≡ fromℕ< n<m 
lemma12 {zero} {suc m} (s≤s z≤n) zero refl = refl
lemma12 {suc n} {suc m} (s≤s n<m) (suc f) refl =  cong suc ( lemma12 {n} {m} n<m f refl  ) 

open import Relation.Binary.HeterogeneousEquality as HE using (_≅_ ) 
open import Data.Fin.Properties

-- <-irrelevant
<-nat=irr : {i j n : ℕ } → ( i ≡ j ) → {i<n : i < n } → {j<n : j < n } → i<n ≅ j<n  
<-nat=irr {zero} {zero} {suc n} refl {s≤s z≤n} {s≤s z≤n} = HE.refl
<-nat=irr {suc i} {suc i} {suc n} refl {s≤s i<n} {s≤s j<n} = HE.cong (λ k → s≤s k ) ( <-nat=irr {i} {i} {n} refl  )

lemma8 : {i j n : ℕ } → ( i ≡ j ) → {i<n : i < n } → {j<n : j < n } → i<n ≅ j<n  
lemma8 {zero} {zero} {suc n} refl {s≤s z≤n} {s≤s z≤n} = HE.refl
lemma8 {suc i} {suc i} {suc n} refl {s≤s i<n} {s≤s j<n} = HE.cong (λ k → s≤s k ) ( lemma8 {i} {i} {n} refl  )

-- fromℕ<-irrelevant 
lemma10 : {n i j  : ℕ } → ( i ≡ j ) → {i<n : i < n } → {j<n : j < n }  → fromℕ< i<n ≡ fromℕ< j<n
lemma10 {n} refl  = HE.≅-to-≡ (HE.cong (λ k → fromℕ< k ) (lemma8 refl  ))

lemma31 : {a b c : ℕ } → { a<b : a < b } { b<c : b < c } { a<c : a < c } → NatP.<-trans a<b b<c ≡ a<c
lemma31 {a} {b} {c} {a<b} {b<c} {a<c} = HE.≅-to-≡ (lemma8 refl) 

-- toℕ-fromℕ<
lemma11 : {n m : ℕ } {x : Fin n } → (n<m : n < m ) → toℕ (fromℕ< (NatP.<-trans (toℕ<n x) n<m)) ≡ toℕ x
lemma11 {n} {m} {x} n<m  = begin
              toℕ (fromℕ< (NatP.<-trans (toℕ<n x) n<m))
           ≡⟨ toℕ-fromℕ< _ ⟩
              toℕ x
           ∎  where
               open ≡-Reasoning

