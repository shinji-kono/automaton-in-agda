{-# OPTIONS --allow-unsolved-metas #-} 

module fin where

open import Data.Fin hiding (_<_ ; _≤_ ; _>_ ; _+_ )
open import Data.Fin.Properties as DFP hiding (≤-trans ;  <-trans ;  ≤-refl  ) renaming ( <-cmp to <-fcmp )
open import Data.Nat
open import Data.Nat.Properties
open import logic
open import nat
open import Relation.Binary.PropositionalEquality


-- toℕ<n
fin<n : {n : ℕ} (f : Fin n) → toℕ f < n
fin<n {_} zero = s≤s z≤n
fin<n {suc n} (suc f) = s≤s (fin<n {n} f)

-- toℕ≤n
fin≤n : {n : ℕ} (f : Fin (suc n)) → toℕ f ≤ n
fin≤n {_} zero = z≤n
fin≤n {suc n} (suc f) = s≤s (fin≤n {n} f)

pred<n : {n : ℕ} {f : Fin (suc n)} → n > 0  → Data.Nat.pred (toℕ f) < n
pred<n {suc n} {zero} (s≤s z≤n) = s≤s z≤n
pred<n {suc n} {suc f} (s≤s z≤n) = fin<n f

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

fin1≡0 : (f : Fin 1) → # 0 ≡ f
fin1≡0 zero = refl

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

x<y→fin-1 : {n : ℕ } → { x y : Fin (suc n)} →  toℕ x < toℕ y  → Fin n
x<y→fin-1 {n} {x} {y} lt = fromℕ< (≤-trans lt (fin≤n _ ))

x<y→fin-1-eq : {n : ℕ } → { x y : Fin (suc n)} → (lt : toℕ x < toℕ y ) → toℕ x ≡ toℕ (x<y→fin-1 lt )
x<y→fin-1-eq {n} {x} {y} lt = sym ( begin
           toℕ (fromℕ< (≤-trans lt (fin≤n y)) ) ≡⟨ toℕ-fromℕ< _ ⟩
           toℕ x  ∎  ) where open ≡-Reasoning

f<→< : {n : ℕ } → { x y : Fin n} → x Data.Fin.< y  →  toℕ x < toℕ y  
f<→< {_} {zero} {suc y} (s≤s lt) = s≤s z≤n
f<→< {_} {suc x} {suc y} (s≤s lt) = s≤s (f<→< {_} {x} {y} lt)

f≡→≡ : {n : ℕ } → { x y : Fin n} → x ≡ y  →  toℕ x ≡ toℕ y  
f≡→≡ refl = refl

open import Data.List
open import Relation.Binary.Definitions

-----
--
-- find duplicate element in a List (Fin n)
--
--    if the length is longer than n, we can find duplicate element as FDup-in-list 

list2func : (n : ℕ) → (x : List (Fin n)) → n < length x → Fin (length x) → Fin n
list2func n x n<l y = lf00 (toℕ y) x (fin<n y)  where
     lf00 : (i : ℕ) → (x : List (Fin n)) → i < length x → Fin n
     lf00 zero (x ∷ t) lt = x
     lf00 (suc i) (x ∷ t) (s≤s lt) = lf00 i t lt

fin-phase2 : { n : ℕ }  (q : Fin n) (qs : List (Fin n) ) → Bool  -- find the dup
fin-phase2 q [] = false
fin-phase2 q (x ∷ qs) with <-fcmp q x
... | tri< a ¬b ¬c = fin-phase2 q qs
... | tri≈ ¬a b ¬c = true
... | tri> ¬a ¬b c = fin-phase2 q qs
fin-phase1 : { n : ℕ }  (q : Fin n) (qs : List (Fin n) ) → Bool  -- find the first element
fin-phase1 q [] = false
fin-phase1 q (x ∷ qs) with <-fcmp q x
... | tri< a ¬b ¬c = fin-phase1 q qs
... | tri≈ ¬a b ¬c = fin-phase2 q qs
... | tri> ¬a ¬b c = fin-phase1 q qs

fin-dup-in-list : { n : ℕ}  (q : Fin n) (qs : List (Fin n) ) → Bool
fin-dup-in-list {n} q qs = fin-phase1 q qs

record FDup-in-list (n : ℕ ) (qs : List (Fin n))  : Set where
   field
      dup : Fin n
      is-dup : fin-dup-in-list dup qs ≡ true

list-less : {n : ℕ } → List (Fin (suc n)) → List (Fin n)
list-less [] = []
list-less {n} (i ∷ ls) with <-fcmp (fromℕ< a<sa) i
... | tri< a ¬b ¬c = ⊥-elim ( nat-≤> a (subst (λ k → toℕ i < suc k ) (sym fin<asa) (fin≤n _ )))
... | tri≈ ¬a b ¬c = list-less ls
... | tri> ¬a ¬b c = x<y→fin-1 c ∷ list-less ls

---
---  if List (Fin n) is longer than n, there is at most one duplication
---
fin-dup-in-list>n : {n : ℕ } → (qs : List (Fin n))  → (len> : length qs > n ) → FDup-in-list n qs
fin-dup-in-list>n {zero} [] ()
fin-dup-in-list>n {zero} (() ∷ qs) lt
fin-dup-in-list>n {suc n} qs lt = fdup-phase0 where
     open import Level using ( Level )
     --  make a dup from one level below
     fdup+1 : (qs : List (Fin (suc n))) (i : Fin n) →  fin-dup-in-list  (fromℕ< a<sa ) qs ≡ false
          → fin-dup-in-list i (list-less qs) ≡ true → FDup-in-list (suc n) qs
     fdup+1 qs i ne p = record { dup = fin+1 i ; is-dup = f1-phase1 qs p (case1 ne) } where
          -- we have two loops on the max element and the current level. The disjuction means the phases may differ.
          f1-phase2 : (qs : List (Fin (suc n)) ) → fin-phase2 i (list-less qs) ≡ true
              → (fin-phase1 (fromℕ< a<sa) qs ≡ false ) ∨ (fin-phase2 (fromℕ< a<sa) qs ≡ false)
              → fin-phase2 (fin+1 i) qs ≡ true
          f1-phase2 (x ∷ qs) p (case1 q1) with  <-fcmp (fromℕ< a<sa) x
          ... | tri< a ¬b ¬c = ⊥-elim ( nat-≤> a (subst (λ k → toℕ x < suc k ) (sym fin<asa) (fin≤n _ )))
          f1-phase2 (x ∷ qs) p (case1 q1) | tri≈ ¬a b ¬c with <-fcmp (fin+1 i) x
          ... | tri< a ¬b ¬c₁ = f1-phase2 qs p (case2 q1)
          ... | tri≈ ¬a₁ b₁ ¬c₁ = refl
          ... | tri> ¬a₁ ¬b c = f1-phase2 qs p (case2 q1)
          -- two fcmp is only different in the size of Fin, but to develop both f1-phase and list-less both fcmps are required
          f1-phase2 (x ∷ qs) p (case1 q1) | tri> ¬a ¬b c with <-fcmp i (fromℕ< (≤-trans c (fin≤n (fromℕ< a<sa)))) | <-fcmp (fin+1 i) x
          ... | tri< a ¬b₁ ¬c | tri< a₁ ¬b₂ ¬c₁ = f1-phase2 qs p (case1 q1)
          ... | tri< a ¬b₁ ¬c | tri≈ ¬a₁ b ¬c₁  = ⊥-elim ( ¬a₁ (subst₂ (λ j k → j < k) (sym fin+1-toℕ) (toℕ-fromℕ< _) a ))
          ... | tri< a ¬b₁ ¬c | tri> ¬a₁ ¬b₂ c₁ = ⊥-elim ( ¬a₁ (subst₂ (λ j k → j < k) (sym fin+1-toℕ) (toℕ-fromℕ< _) a ))
          ... | tri≈ ¬a₁ b ¬c | tri< a ¬b₁ ¬c₁  = ⊥-elim ( ¬a₁ (subst₂ (λ j k → j < k) fin+1-toℕ (sym (toℕ-fromℕ< _)) a ))
          ... | tri≈ ¬a₁ b ¬c | tri≈ ¬a₂ b₁ ¬c₁ = refl
          ... | tri≈ ¬a₁ b ¬c | tri> ¬a₂ ¬b₁ c₁ = ⊥-elim ( ¬c (subst₂ (λ j k → j > k) fin+1-toℕ (sym (toℕ-fromℕ< _)) c₁ ))
          ... | tri> ¬a₁ ¬b₁ c₁ | tri< a ¬b₂ ¬c = ⊥-elim ( ¬c (subst₂ (λ j k → j > k) (sym fin+1-toℕ) (toℕ-fromℕ< _) c₁ ))
          ... | tri> ¬a₁ ¬b₁ c₁ | tri≈ ¬a₂ b ¬c = ⊥-elim ( ¬c (subst₂ (λ j k → j > k) (sym fin+1-toℕ) (toℕ-fromℕ< _) c₁ ))
          ... | tri> ¬a₁ ¬b₁ c₁ | tri> ¬a₂ ¬b₂ c₂ = f1-phase2 qs p (case1 q1)
          f1-phase2 (x ∷ qs) p (case2 q1) with  <-fcmp (fromℕ< a<sa) x
          ... | tri< a ¬b ¬c = ⊥-elim ( nat-≤> a (subst (λ k → toℕ x < suc k ) (sym fin<asa) (fin≤n _ )))
          f1-phase2 (x ∷ qs) p (case2 q1) | tri≈ ¬a b ¬c with <-fcmp (fin+1 i) x
          ... | tri< a ¬b ¬c₁ = ⊥-elim ( ¬-bool q1 refl )
          ... | tri≈ ¬a₁ b₁ ¬c₁ = refl
          ... | tri> ¬a₁ ¬b c = ⊥-elim ( ¬-bool q1 refl )
          f1-phase2 (x ∷ qs) p (case2 q1) | tri> ¬a ¬b c with <-fcmp i (fromℕ< (≤-trans c (fin≤n (fromℕ< a<sa)))) | <-fcmp (fin+1 i) x
          ... | tri< a ¬b₁ ¬c | tri< a₁ ¬b₂ ¬c₁ = f1-phase2 qs p (case2 q1)
          ... | tri< a ¬b₁ ¬c | tri≈ ¬a₁ b ¬c₁  = ⊥-elim ( ¬a₁ (subst₂ (λ j k → j < k) (sym fin+1-toℕ) (toℕ-fromℕ< _) a ))
          ... | tri< a ¬b₁ ¬c | tri> ¬a₁ ¬b₂ c₁ = ⊥-elim ( ¬a₁ (subst₂ (λ j k → j < k) (sym fin+1-toℕ) (toℕ-fromℕ< _) a ))
          ... | tri≈ ¬a₁ b ¬c | tri< a ¬b₁ ¬c₁  = ⊥-elim ( ¬a₁ (subst₂ (λ j k → j < k) fin+1-toℕ (sym (toℕ-fromℕ< _)) a ))
          ... | tri≈ ¬a₁ b ¬c | tri≈ ¬a₂ b₁ ¬c₁ = refl
          ... | tri≈ ¬a₁ b ¬c | tri> ¬a₂ ¬b₁ c₁ = ⊥-elim ( ¬c (subst₂ (λ j k → j > k) fin+1-toℕ (sym (toℕ-fromℕ< _)) c₁ ))
          ... | tri> ¬a₁ ¬b₁ c₁ | tri< a ¬b₂ ¬c = ⊥-elim ( ¬c (subst₂ (λ j k → j > k) (sym fin+1-toℕ) (toℕ-fromℕ< _) c₁ ))
          ... | tri> ¬a₁ ¬b₁ c₁ | tri≈ ¬a₂ b ¬c = ⊥-elim ( ¬c (subst₂ (λ j k → j > k) (sym fin+1-toℕ) (toℕ-fromℕ< _) c₁ ))
          ... | tri> ¬a₁ ¬b₁ c₁ | tri> ¬a₂ ¬b₂ c₂ =  f1-phase2 qs p (case2 q1 )
          f1-phase1 : (qs : List (Fin (suc n)) ) → fin-phase1 i (list-less qs) ≡ true
              → (fin-phase1 (fromℕ< a<sa) qs ≡ false ) ∨ (fin-phase2 (fromℕ< a<sa) qs ≡ false)
              → fin-phase1 (fin+1 i) qs ≡ true
          f1-phase1 (x ∷ qs) p (case1 q1) with  <-fcmp (fromℕ< a<sa) x
          ... | tri< a ¬b ¬c = ⊥-elim ( nat-≤> a (subst (λ k → toℕ x < suc k ) (sym fin<asa) (fin≤n _ )))
          f1-phase1 (x ∷ qs) p (case1 q1) | tri≈ ¬a b ¬c with <-fcmp (fin+1 i) x
          ... | tri< a ¬b ¬c₁ = f1-phase1 qs p (case2 q1)
          ... | tri≈ ¬a₁ b₁ ¬c₁ = ⊥-elim (fdup-10 b b₁) where
               fdup-10 : fromℕ< a<sa ≡ x → fin+1 i ≡ x → ⊥
               fdup-10 eq eq1 = nat-≡< (cong toℕ (trans eq1 (sym eq))) (subst₂ (λ j k → j < k ) (sym fin+1-toℕ) (sym fin<asa) (fin<n _)) 
          ... | tri> ¬a₁ ¬b c = f1-phase1 qs p (case2 q1)
          f1-phase1 (x ∷ qs) p (case1 q1) | tri> ¬a ¬b c with <-fcmp i (fromℕ< (≤-trans c (fin≤n (fromℕ< a<sa)))) | <-fcmp (fin+1 i) x
          ... | tri< a ¬b₁ ¬c | tri< a₁ ¬b₂ ¬c₁ = f1-phase1 qs p (case1 q1)
          ... | tri< a ¬b₁ ¬c | tri≈ ¬a₁ b ¬c₁  = ⊥-elim ( ¬a₁ (subst₂ (λ j k → j < k) (sym fin+1-toℕ) (toℕ-fromℕ< _) a ))
          ... | tri< a ¬b₁ ¬c | tri> ¬a₁ ¬b₂ c₁ = ⊥-elim ( ¬a₁ (subst₂ (λ j k → j < k) (sym fin+1-toℕ) (toℕ-fromℕ< _) a ))
          ... | tri≈ ¬a₁ b ¬c | tri< a ¬b₁ ¬c₁  = ⊥-elim ( ¬a₁ (subst₂ (λ j k → j < k) fin+1-toℕ (sym (toℕ-fromℕ< _)) a ))
          ... | tri≈ ¬a₁ b ¬c | tri≈ ¬a₂ b₁ ¬c₁ = f1-phase2 qs p (case1 q1)
          ... | tri≈ ¬a₁ b ¬c | tri> ¬a₂ ¬b₁ c₁ = ⊥-elim ( ¬c (subst₂ (λ j k → j > k) fin+1-toℕ (sym (toℕ-fromℕ< _)) c₁ ))
          ... | tri> ¬a₁ ¬b₁ c₁ | tri< a ¬b₂ ¬c = ⊥-elim ( ¬c (subst₂ (λ j k → j > k) (sym fin+1-toℕ) (toℕ-fromℕ< _) c₁ ))
          ... | tri> ¬a₁ ¬b₁ c₁ | tri≈ ¬a₂ b ¬c = ⊥-elim ( ¬c (subst₂ (λ j k → j > k) (sym fin+1-toℕ) (toℕ-fromℕ< _) c₁ ))
          ... | tri> ¬a₁ ¬b₁ c₁ | tri> ¬a₂ ¬b₂ c₂ = f1-phase1 qs p (case1 q1)
          f1-phase1 (x ∷ qs) p (case2 q1) with  <-fcmp (fromℕ< a<sa) x
          ... | tri< a ¬b ¬c = ⊥-elim ( nat-≤> a (subst (λ k → toℕ x < suc k ) (sym fin<asa) (fin≤n _ )))
          f1-phase1 (x ∷ qs) p (case2 q1) | tri≈ ¬a b ¬c = ⊥-elim ( ¬-bool q1 refl )
          f1-phase1 (x ∷ qs) p (case2 q1) | tri> ¬a ¬b c with <-fcmp i (fromℕ< (≤-trans c (fin≤n (fromℕ< a<sa)))) | <-fcmp (fin+1 i) x
          ... | tri< a ¬b₁ ¬c | tri< a₁ ¬b₂ ¬c₁ = f1-phase1 qs p (case2 q1)
          ... | tri< a ¬b₁ ¬c | tri≈ ¬a₁ b ¬c₁  = ⊥-elim ( ¬a₁ (subst₂ (λ j k → j < k) (sym fin+1-toℕ) (toℕ-fromℕ< _) a ))
          ... | tri< a ¬b₁ ¬c | tri> ¬a₁ ¬b₂ c₁ = ⊥-elim ( ¬a₁ (subst₂ (λ j k → j < k) (sym fin+1-toℕ) (toℕ-fromℕ< _) a ))
          ... | tri≈ ¬a₁ b ¬c | tri< a ¬b₁ ¬c₁  = ⊥-elim ( ¬a₁ (subst₂ (λ j k → j < k) fin+1-toℕ (sym (toℕ-fromℕ< _)) a ))
          ... | tri≈ ¬a₁ b ¬c | tri≈ ¬a₂ b₁ ¬c₁ = f1-phase2 qs p (case2 q1)
          ... | tri≈ ¬a₁ b ¬c | tri> ¬a₂ ¬b₁ c₁ = ⊥-elim ( ¬c (subst₂ (λ j k → j > k) fin+1-toℕ (sym (toℕ-fromℕ< _)) c₁ ))
          ... | tri> ¬a₁ ¬b₁ c₁ | tri< a ¬b₂ ¬c = ⊥-elim ( ¬c (subst₂ (λ j k → j > k) (sym fin+1-toℕ) (toℕ-fromℕ< _) c₁ ))
          ... | tri> ¬a₁ ¬b₁ c₁ | tri≈ ¬a₂ b ¬c = ⊥-elim ( ¬c (subst₂ (λ j k → j > k) (sym fin+1-toℕ) (toℕ-fromℕ< _) c₁ ))
          ... | tri> ¬a₁ ¬b₁ c₁ | tri> ¬a₂ ¬b₂ c₂ = f1-phase1 qs p (case2 q1)
     fdup-phase0 : FDup-in-list (suc n) qs 
     fdup-phase0 with fin-dup-in-list (fromℕ< a<sa) qs | inspect (fin-dup-in-list (fromℕ< a<sa)) qs
     ... | true  | record { eq = eq } = record { dup = fromℕ< a<sa ; is-dup = eq }
     ... | false | record { eq = ne } = fdup+1 qs (FDup-in-list.dup fdup) ne (FDup-in-list.is-dup fdup)  where
           -- if no dup in the max element, the list without the element is only one length shorter
           fless : (qs : List (Fin (suc n))) → length qs > suc n  → fin-dup-in-list (fromℕ< a<sa) qs ≡ false → n < length (list-less qs) 
           fless qs lt p = fl-phase1 n qs lt p where
               fl-phase2 : (n1 : ℕ) (qs : List (Fin (suc n))) → length qs > n1  → fin-phase2 (fromℕ< a<sa) qs ≡ false → n1 < length (list-less qs) 
               fl-phase2 zero (x ∷ qs) (s≤s lt) p with  <-fcmp (fromℕ< a<sa) x
               ... | tri< a ¬b ¬c = ⊥-elim ( nat-≤> a (subst (λ k → toℕ x < suc k ) (sym fin<asa) (fin≤n _ )))
               ... | tri> ¬a ¬b c =  s≤s z≤n 
               fl-phase2 (suc n1) (x ∷ qs) (s≤s lt) p with  <-fcmp (fromℕ< a<sa) x
               ... | tri< a ¬b ¬c = ⊥-elim ( nat-≤> a (subst (λ k → toℕ x < suc k ) (sym fin<asa) (fin≤n _ )))
               ... | tri> ¬a ¬b c = s≤s ( fl-phase2 n1 qs lt p )
               fl-phase1 : (n1 : ℕ) (qs : List (Fin (suc n))) → length qs > suc n1  → fin-phase1 (fromℕ< a<sa) qs ≡ false → n1 < length (list-less qs) 
               fl-phase1 zero (x ∷ qs) (s≤s lt) p  with <-fcmp (fromℕ< a<sa) x
               ... | tri< a ¬b ¬c = ⊥-elim ( nat-≤> a (subst (λ k → toℕ x < suc k ) (sym fin<asa) (fin≤n _ )))
               ... | tri≈ ¬a b ¬c = fl-phase2 0 qs lt p
               ... | tri> ¬a ¬b c = s≤s z≤n
               fl-phase1 (suc n1) (x ∷ qs) (s≤s lt) p with <-fcmp (fromℕ< a<sa) x
               ... | tri< a ¬b ¬c = ⊥-elim ( nat-≤> a (subst (λ k → toℕ x < suc k ) (sym fin<asa) (fin≤n _ )))
               ... | tri≈ ¬a b ¬c = fl-phase2 (suc n1) qs lt p 
               ... | tri> ¬a ¬b c = s≤s ( fl-phase1 n1 qs lt p )
           -- if the list without the max element is only one length shorter, we can recurse
           fdup : FDup-in-list n (list-less qs)
           fdup = fin-dup-in-list>n (list-less qs) (fless qs lt ne)

--
