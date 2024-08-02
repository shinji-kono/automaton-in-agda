{-# OPTIONS --cubical-compatible  --safe #-}

module fin where

open import Data.Fin hiding (_<_ ; _≤_ ; _>_ ; _+_ )
open import Data.Fin.Properties as FP hiding (≤-trans ;  <-trans ;  ≤-refl  ) renaming ( <-cmp to <-fcmp )
open import Data.Nat
open import Data.Nat.Properties
open import logic
open import nat
open import Relation.Binary.PropositionalEquality
open import  Relation.Binary.Definitions
open import Data.Nat.Properties as NatP  hiding ( _≟_ )
open import Data.Empty
open import Relation.Nullary


-- toℕ<n
fin<n : {n : ℕ} (f : Fin n) → toℕ f < n
fin<n {_} zero = s≤s z≤n
fin<n {suc n} (suc f) = s≤s (fin<n {n} f)

-- toℕ≤n
fin≤n : {n : ℕ} (f : Fin (suc n)) → toℕ f ≤ n
fin≤n {n} f = px≤py (fin<n f)

pred<n : {n : ℕ} {f : Fin (suc n)} → n > 0  → Data.Nat.pred (toℕ f) < n
pred<n {n} {f} 0<n with toℕ f in eq
... | 0 = 0<n
... | suc m = ≤-trans (refl-≤≡ (sym eq)) (fin≤n f )

fin<asa : {n : ℕ} → toℕ (fromℕ< {n} a<sa) ≡ n
fin<asa = toℕ-fromℕ< nat.a<sa

-- fromℕ<-toℕ
-- toℕ→from : {n : ℕ} {x : Fin (suc n)} → toℕ x ≡ n → fromℕ n ≡ x
-- toℕ→from {n} {x} eq = ?

-- 0≤fmax : {n : ℕ } → (# 0) Data.Fin.≤ fromℕ< {n} a<sa
-- 0≤fmax {n} = ?

-- 0<fmax : {n : ℕ } → (# 0) Data.Fin.< fromℕ< {suc n} a<sa
-- 0<fmax {n} = subst (λ k → 0 < k ) (sym (toℕ-fromℕ< {suc n} {suc (suc n)} a<sa)) (s≤s z≤n)

-- toℕ-injective
-- i=j : {n : ℕ} (i j : Fin n) → toℕ i ≡ toℕ j → i ≡ j
-- i=j {n} i j i=j = toℕ-injective i=j

fin1≡0 : (f : Fin 1) → # 0 ≡ f
fin1≡0 f with ≤-∨ (fin<n f)
... | case1 eq = toℕ-injective (sym (cong Data.Nat.pred eq))
... | case2 lt = ⊥-elim (nat-≤> lt (s≤s (s≤s z≤n)))

-- raise 1
fin+1 :  { n : ℕ } → Fin n → Fin (suc n)
fin+1  zero = zero 
fin+1  (suc x) = suc (fin+1 x)


fin+1≤ : { i n : ℕ } → (a : i < n)  → fin+1 (fromℕ< a) ≡ fromℕ< (<-trans a a<sa)
fin+1≤ {zero} {suc n} a = refl
fin+1≤ {suc i} {suc n} a = cong suc (fin+1≤ {i} {n} (sx<py→x<y a)) 

fin+1-toℕ : { n : ℕ } → { x : Fin n} → toℕ (fin+1 x) ≡ toℕ x
fin+1-toℕ {.(suc _)} {zero} = refl
fin+1-toℕ {suc n} {suc x} = cong suc ( fin+1-toℕ {n} {x} )

fin-1 :  { n : ℕ } → (x : Fin (suc n)) → 0 < toℕ x   → Fin n
fin-1 {0} x 0<x = ⊥-elim (nat-≤> 0<x (fin<n x) )
fin-1 {suc n} x 0<x = fromℕ< lem where
    lem : Data.Nat.pred (toℕ x) < suc  n
    lem = sx<py→x<y (subst (λ k → k < suc (suc n)) (sym (sucprd 0<x)) (fin<n x))

-- we cannot use with toℕ x in eq here
-- because it is not allowed in fin-1-xsℕ

-- fromℕ<-cong 
lemma10 : {n i j  : ℕ } → ( i ≡ j ) → (i<n : i < n ) → (j<n : j < n )  → fromℕ< i<n ≡ fromℕ< j<n
lemma10 {n} {i} {j} eq i<n j<n = fromℕ<-cong _ _ eq i<n j<n

-- fromℕ<-toℕ 
toℕ→fromℕ< : {n m : ℕ } → (n<m : n < m ) → (f : Fin m )  → toℕ f ≡ n → f ≡ fromℕ< n<m 
toℕ→fromℕ< {n} {m} n<m f eq = toℕ-injective (trans eq (sym (toℕ-fromℕ< n<m ))) 

lemma12 = toℕ→fromℕ<

-- this is refl
fromℕ<=suc : {a b : ℕ } → (lt : a < b ) → fromℕ< (s≤s lt) ≡ suc (fromℕ< lt)
fromℕ<=suc {a} {b} lt = refl

fin-1-xs : { n : ℕ } → (x : Fin (suc n)) → (0<x : 0 < toℕ x )  → suc (fin-1 x 0<x  ) ≡   x
fin-1-xs {zero} x 0<x = ⊥-elim (nat-≤> 0<x (fin<n x)  )
fin-1-xs {suc n} x 0<x  = begin
    suc (fin-1 x 0<x)  ≡⟨ fromℕ<-cong _ _ (sucprd 0<x) (subst (λ k → k < suc (suc n)) (sym (sucprd 0<x)) (fin<n x)) (fin<n x) ⟩
    fromℕ< (fin<n x) ≡⟨ sym (toℕ→fromℕ< (fin<n x) x refl) ⟩
    x ∎ where open ≡-Reasoning

fin-1-sx : { n : ℕ } → (x : Fin n) → fin-1 (suc x) (s≤s z≤n)  ≡   x
fin-1-sx {zero} ()
fin-1-sx {suc n} x = sym (toℕ→fromℕ< (fin<n x) x refl )

fpred-comm : {n : ℕ } → (x : Fin n) → toℕ (Data.Fin.pred x) ≡ toℕ x ∸ 1
fpred-comm {.(suc _)} zero = refl
fpred-comm {.(suc _)} (suc x) = toℕ-inject₁ x 

-- toℕ-fromℕ<
lemma11 : {n m : ℕ } {x : Fin n } → (n<m : n < m ) → toℕ (fromℕ< (NatP.<-trans (toℕ<n x) n<m)) ≡ toℕ x
lemma11 {n} {m} {x} n<m  = begin
      toℕ (fromℕ< (NatP.<-trans (toℕ<n x) n<m)) ≡⟨ toℕ-fromℕ< _ ⟩
      toℕ x ∎  where open ≡-Reasoning

x<y→fin-1 : {n : ℕ } → { x y : Fin (suc n)} →  toℕ x < toℕ y  → Fin n
x<y→fin-1 {n} {x} {y} lt = fromℕ< (≤-trans lt (fin≤n _ ))

x<y→fin-1-eq : {n : ℕ } → { x y : Fin (suc n)} → (lt : toℕ x < toℕ y ) → toℕ x ≡ toℕ (x<y→fin-1 lt )
x<y→fin-1-eq {n} {x} {y} lt = sym ( begin
           toℕ (fromℕ< (≤-trans lt (fin≤n y)) ) ≡⟨ toℕ-fromℕ< _ ⟩
           toℕ x  ∎  ) where open ≡-Reasoning

f<→< : {n : ℕ } → { x y : Fin n} → x Data.Fin.< y  →  toℕ x < toℕ y  
f<→< x<y = x<y

f≡→≡ : {n : ℕ } → { x y : Fin n} → x ≡ y  →  toℕ x ≡ toℕ y  
f≡→≡ refl = refl

fin+1eq : {n : ℕ} → (x : Fin n ) → toℕ x < n → Fin (suc n)
fin+1eq {n} x x<n = fromℕ< (<-trans x<n a<sa)

fin+1eq< : {n : ℕ} → (x : Fin n ) → (x<n : toℕ x < n ) → toℕ (fin+1eq x x<n) < n
fin+1eq<  {n} x x<n = subst (λ k → k < n ) (sym (toℕ-fromℕ< (<-trans x<n a<sa) )) (fin<n x)

fin+1eq-≡ℕ : {n : ℕ} → (x : Fin n ) → (x<n : toℕ x < n ) → toℕ x ≡ toℕ (fin+1eq x x<n )
fin+1eq-≡ℕ {n} x x<n = sym ( begin
           toℕ (fromℕ< (<-trans x<n a<sa) ) ≡⟨ toℕ-fromℕ< _ ⟩
           toℕ x  ∎  ) where open ≡-Reasoning

open import Data.List
open import Relation.Binary.Definitions

-----
--
-- find duplicate element in a List (Fin n)
--
--    if the length is longer than n, we can find duplicate element as FDup-in-list 
--
--  How about do it in ℕ ?

-- fin-count : { n : ℕ }  (q : Fin n) (qs : List (Fin n) ) → ℕ
-- fin-count q p[ = 0
-- fin-count q (q0 ∷ qs ) with <-fcmp q q0 
-- ... | tri-e = suc (fin-count q qs)
-- ... | false = fin-count q qs

-- fin-not-dup-in-list : { n : ℕ}  (qs : List (Fin n) ) → Set
-- fin-not-dup-in-list {n} qs = (q : Fin n) → fin-count q ≤ 1

-- this is far easier
-- fin-not-dup-in-list→len<n : { n : ℕ}  (qs : List (Fin n) ) → ( (q : Fin n) → fin-not-dup-in-list qs q) → length qs ≤ n
-- fin-not-dup-in-list→len<n = ?

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

fin010 : {n m : ℕ } {x : Fin n} (c : suc (toℕ x) ≤ toℕ (fromℕ< {m} a<sa) ) → toℕ (fromℕ< (≤-trans c (fin≤n (fromℕ< a<sa)))) ≡ toℕ x
fin010 {_} {_} {x} c = begin 
           toℕ (fromℕ< (≤-trans c (fin≤n (fromℕ< a<sa))))  ≡⟨ toℕ-fromℕ< _ ⟩
           toℕ x  ∎   where open ≡-Reasoning

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
          f1-phase2 [] () q
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
          f1-phase1 [] () q
          f1-phase1 (x ∷ qs) p (case1 q1) with  <-fcmp (fromℕ< a<sa) x
          ... | tri< a ¬b ¬c = ⊥-elim ( nat-≤> a (subst (λ k → toℕ x < suc k ) (sym fin<asa) (fin≤n _ )))
          f1-phase1 (x ∷ qs) p (case1 q1) | tri≈ ¬a b ¬c with <-fcmp (fin+1 i) x
          ... | tri< a ¬b ¬c₁ = f1-phase1 qs p (case2 q1)
          ... | tri≈ ¬a₁ b₁ ¬c₁ = ⊥-elim (fdup-10 b b₁) where
               fdup-10 : fromℕ< a<sa ≡ x → fin+1 i ≡ x → ⊥
               fdup-10 eq eq1 = nat-≡< (cong toℕ (trans eq1 (sym eq))) (subst₂ (λ j k → j < k ) (sym fin+1-toℕ) (sym fin<asa) (fin<n _) ) 
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
     fdup-phase0 with fin-dup-in-list (fromℕ< a<sa) qs in eq 
     ... | true  = record { dup = fromℕ< a<sa ; is-dup = eq }
     ... | false = fdup+1 qs (FDup-in-list.dup fdup) eq (FDup-in-list.is-dup fdup)  where
           -- if no dup in the max element, the list without the element is only one length shorter
           fless : (qs : List (Fin (suc n))) → length qs > suc n  → fin-dup-in-list (fromℕ< a<sa) qs ≡ false → n < length (list-less qs) 
           fless qs lt p = fl-phase1 n qs lt p where
               fl-phase2 : (n1 : ℕ) (qs : List (Fin (suc n))) → length qs > n1  → fin-phase2 (fromℕ< a<sa) qs ≡ false → n1 < length (list-less qs) 
               fl-phase2 _ [] lt p = ⊥-elim (nat-≤> z≤n lt )
               fl-phase2 zero (x ∷ qs) lt p with  <-fcmp (fromℕ< a<sa) x
               ... | tri< a ¬b ¬c = ⊥-elim ( nat-≤> a (subst (λ k → toℕ x < suc k ) (sym fin<asa) (fin≤n _ )))
               ... | tri≈ ¬a b ¬c = ⊥-elim ( ¬-bool p refl )
               ... | tri> ¬a ¬b c =  s≤s z≤n 
               fl-phase2 (suc n1) (x ∷ qs) lt p with  <-fcmp (fromℕ< a<sa) x
               ... | tri< a ¬b ¬c = ⊥-elim ( nat-≤> a (subst (λ k → toℕ x < suc k ) (sym fin<asa) (fin≤n _ )))
               ... | tri≈ ¬a b ¬c = ⊥-elim ( ¬-bool p refl )
               ... | tri> ¬a ¬b c = s≤s ( fl-phase2 n1 qs (sx<py→x<y lt) p )
               fl-phase1 : (n1 : ℕ) (qs : List (Fin (suc n))) → length qs > suc n1  → fin-phase1 (fromℕ< a<sa) qs ≡ false → n1 < length (list-less qs) 
               fl-phase1 zero (x ∷ qs) lt p  with <-fcmp (fromℕ< a<sa) x
               ... | tri< a ¬b ¬c = ⊥-elim ( nat-≤> a (subst (λ k → toℕ x < suc k ) (sym fin<asa) (fin≤n _ )))
               ... | tri≈ ¬a b ¬c = fl-phase2 0 qs (sx<py→x<y lt) p
               ... | tri> ¬a ¬b c = s≤s z≤n
               fl-phase1 (suc n1) (x ∷ qs) lt p with <-fcmp (fromℕ< a<sa) x
               ... | tri< a ¬b ¬c = ⊥-elim ( nat-≤> a (subst (λ k → toℕ x < suc k ) (sym fin<asa) (fin≤n _ )))
               ... | tri≈ ¬a b ¬c = fl-phase2 (suc n1) qs (sx<py→x<y lt) p
               ... | tri> ¬a ¬b c = s≤s ( fl-phase1 n1 qs (sx<py→x<y lt) p )
           -- if the list without the max element is only one length shorter, we can recurse
           fdup : FDup-in-list n (list-less qs)
           fdup = fin-dup-in-list>n (list-less qs) (fless qs lt eq)

--
