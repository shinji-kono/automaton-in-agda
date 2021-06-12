{-# OPTIONS --allow-unsolved-metas #-}
module gcd where

open import Data.Nat 
open import Data.Nat.Properties
open import Data.Empty
open import Data.Unit using (⊤ ; tt)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Definitions
open import nat
open import logic

record Factor (n m : ℕ ) : Set where
   field 
      factor : ℕ
      remain : ℕ
      is-factor : factor * n + remain ≡ m

record Dividable (n m : ℕ ) : Set where
   field 
      factor : ℕ
      is-factor : factor * n + 0 ≡ m 

open Factor

open ≡-Reasoning

decf : { n k : ℕ } → ( x : Factor k (suc n) ) → Factor k n
decf {n} {k} x with remain x
... | zero = record { factor = factor x ; remain = k ; is-factor = {!!} }
... | suc r = record { factor = factor x ; remain = r ; is-factor = {!!} }

ifk0 : (  i0 k : ℕ ) → (i0f : Factor k i0 )  → ( i0=0 : remain i0f ≡ 0 )  → factor i0f * k + 0 ≡ i0
ifk0 i0 k i0f i0=0 = begin
   factor i0f * k + 0  ≡⟨ cong (λ m → factor i0f * k + m) (sym i0=0)  ⟩
   factor i0f * k + remain i0f  ≡⟨ is-factor i0f ⟩
   i0 ∎ 

ifzero : {k : ℕ } → (jf :  Factor k zero ) →  remain jf ≡ 0
ifzero = {!!}

gcd1 : ( i i0 j j0 : ℕ ) → ℕ
gcd1 zero i0 zero j0 with <-cmp i0 j0
... | tri< a ¬b ¬c = i0
... | tri≈ ¬a refl ¬c = i0
... | tri> ¬a ¬b c = j0
gcd1 zero i0 (suc zero) j0 = 1
gcd1 zero zero (suc (suc j)) j0 = j0
gcd1 zero (suc i0) (suc (suc j)) j0 = gcd1 i0 (suc i0) (suc j) (suc (suc j))
gcd1 (suc zero) i0 zero j0 = 1
gcd1 (suc (suc i)) i0 zero zero = i0
gcd1 (suc (suc i)) i0 zero (suc j0) = gcd1 (suc i) (suc (suc i))  j0 (suc j0)
gcd1 (suc i) i0 (suc j) j0 = gcd1 i i0 j j0  

gcd : ( i j : ℕ ) → ℕ
gcd i j = gcd1 i i j j 

gcd-gt : ( i i0 j j0 k : ℕ ) → (if : Factor k i) (i0f : Factor k i0 ) (jf : Factor k i ) (j0f : Factor k j0)
   → remain i0f ≡ 0 → remain j0f ≡  0
   → (remain if + i ) ≡ i0  → (remain jf + j ) ≡ j0
   → Dividable k ( gcd1 i i0 j j0 ) 
gcd-gt zero i0 zero j0 k if i0f jf j0f i0=0 j0=0 ir=i0 jr=j0 with <-cmp i0 j0
... | tri< a ¬b ¬c = record { factor = factor i0f ; is-factor = ifk0 i0 k i0f i0=0 } 
... | tri≈ ¬a refl ¬c = record { factor = factor i0f ;  is-factor = ifk0 i0 k i0f i0=0 } 
... | tri> ¬a ¬b c = record { factor = factor j0f ;  is-factor = ifk0 j0 k j0f j0=0 } 
gcd-gt zero i0 (suc zero) j0 k if i0f jf j0f i0=0 j0=0 ir=i0 jr=j0 = {!!} -- can't happen
gcd-gt zero zero (suc (suc j)) j0 k if i0f jf j0f i0=0 j0=0 ir=i0 jr=j0 = record { factor = factor j0f ; is-factor = ifk0 j0 k j0f j0=0 } 
gcd-gt zero (suc i0) (suc (suc j)) j0 k if i0f jf j0f i0=0 j0=0 ir=i0 jr=j0 =  
    gcd-gt i0 (suc i0) (suc j) (suc (suc j))  k (decf i0f)  i0f (decf i0f)
       record { factor = factor jf ; remain = remain jf ; is-factor = {!!} } i0=0 {!!} {!!} {!!}  
gcd-gt (suc zero) i0 zero j0 k if i0f jf j0f i0=0 j0=0 ir=i0 jr=j0 = {!!} -- can't happen
gcd-gt (suc (suc i)) i0 zero zero k if i0f jf j0f i0=0 j0=0 ir=i0 jr=j0 = {!!}
gcd-gt (suc (suc i)) i0 zero (suc j0) k if i0f jf j0f i0=0 j0=0 ir=i0 jr=j0 =
     gcd-gt (suc i) (suc (suc i)) j0 (suc j0) k (decf if) {!!} (decf jf) j0f j0=0 {!!} {!!} {!!} 
gcd-gt (suc zero) i0 (suc j) j0 k if i0f jf j0f i0=0 j0=0 ir=i0 jr=j0 = 
     gcd-gt zero i0 j j0 k (decf if) i0f (decf jf) j0f i0=0 j0=0 {!!} {!!}
gcd-gt (suc (suc i)) i0 (suc j) j0 k if i0f jf j0f i0=0 j0=0 ir=i0 jr=j0 = 
     gcd-gt (suc i) i0 j j0 k (decf if) i0f (decf jf) j0f i0=0 j0=0 {!!} {!!}

-- gcd26 : { n m : ℕ} → n > 1 → m > 1 → n - m > 0 → gcd n m ≡ gcd (n - m) m
-- gcd27 : { n m : ℕ} → n > 1 → m > 1 → n - m > 0 → gcd n k ≡ k → k ≤ n

gcd22 : ( i i0 o o0 : ℕ ) → gcd1 (suc i) i0 (suc o) o0 ≡ gcd1 i i0 o o0
gcd22 zero i0 zero o0 = refl
gcd22 zero i0 (suc o) o0 = refl
gcd22 (suc i) i0 zero o0 = refl
gcd22 (suc i) i0 (suc o) o0 = refl 

gcd20 : (i : ℕ) → gcd i 0 ≡ i
gcd20 zero = refl
gcd20 (suc i) = gcd201 (suc i) where
    gcd201 : (i : ℕ ) → gcd1 i i zero zero ≡ i
    gcd201 zero = refl
    gcd201 (suc zero) = refl
    gcd201 (suc (suc i)) = refl

gcdmm : (n m : ℕ) → gcd1 n m n m ≡ m
gcdmm zero m with <-cmp m m
... | tri< a ¬b ¬c = refl
... | tri≈ ¬a refl ¬c = refl
... | tri> ¬a ¬b c = refl
gcdmm (suc n) m  = subst (λ k → k ≡ m) (sym (gcd22 n m n m )) (gcdmm n m )

gcdsym2 : (i j : ℕ) → gcd1 zero i zero j ≡ gcd1 zero j zero i
gcdsym2 i j with <-cmp i j | <-cmp j i
... | tri< a ¬b ¬c | tri< a₁ ¬b₁ ¬c₁ = ⊥-elim (nat-<> a a₁) 
... | tri< a ¬b ¬c | tri≈ ¬a b ¬c₁ = ⊥-elim (nat-≡< (sym b) a) 
... | tri< a ¬b ¬c | tri> ¬a ¬b₁ c = refl
... | tri≈ ¬a b ¬c | tri< a ¬b ¬c₁ = ⊥-elim (nat-≡< (sym b) a) 
... | tri≈ ¬a refl ¬c | tri≈ ¬a₁ refl ¬c₁ = refl
... | tri≈ ¬a b ¬c | tri> ¬a₁ ¬b c = ⊥-elim (nat-≡< b c) 
... | tri> ¬a ¬b c | tri< a ¬b₁ ¬c = refl
... | tri> ¬a ¬b c | tri≈ ¬a₁ b ¬c = ⊥-elim (nat-≡< b c) 
... | tri> ¬a ¬b c | tri> ¬a₁ ¬b₁ c₁ = ⊥-elim (nat-<> c c₁) 
gcdsym1 : ( i i0 j j0 : ℕ ) → gcd1 i i0 j j0 ≡ gcd1 j j0 i i0
gcdsym1 zero zero zero zero = refl
gcdsym1 zero zero zero (suc j0) = refl
gcdsym1 zero (suc i0) zero zero = refl
gcdsym1 zero (suc i0) zero (suc j0) = gcdsym2 (suc i0) (suc j0)
gcdsym1 zero zero (suc zero) j0 = refl
gcdsym1 zero zero (suc (suc j)) j0 = refl
gcdsym1 zero (suc i0) (suc zero) j0 = refl
gcdsym1 zero (suc i0) (suc (suc j)) j0 = gcdsym1 i0 (suc i0) (suc j) (suc (suc j))
gcdsym1 (suc zero) i0 zero j0 = refl
gcdsym1 (suc (suc i)) i0 zero zero = refl
gcdsym1 (suc (suc i)) i0 zero (suc j0) = gcdsym1 (suc i) (suc (suc i))j0 (suc j0) 
gcdsym1 (suc i) i0 (suc j) j0 = subst₂ (λ j k → j ≡ k ) (sym (gcd22 i _ _ _)) (sym (gcd22 j _ _ _)) (gcdsym1 i i0 j j0 )

gcdsym : { n m : ℕ} → gcd n m ≡ gcd m n
gcdsym {n} {m} = gcdsym1 n n m m 

gcd11 : ( i  : ℕ ) → gcd i i ≡ i
gcd11 i = gcdmm i i 

gcd203 : (i : ℕ) → gcd1 (suc i) (suc i) i i ≡ 1
gcd203 zero = refl
gcd203 (suc i) = gcd205 (suc i) where
   gcd205 : (j : ℕ) → gcd1 (suc j) (suc (suc i)) j (suc i) ≡ 1
   gcd205 zero = refl
   gcd205 (suc j) = subst (λ k → k ≡ 1) (gcd22 (suc j)  (suc (suc i)) j (suc i)) (gcd205 j)
gcd204 : (i : ℕ) → gcd1 1 1 i i ≡ 1
gcd204 zero = refl
gcd204 (suc zero) = refl
gcd204 (suc (suc zero)) = refl
gcd204 (suc (suc (suc i))) = gcd204 (suc (suc i)) 

gcd2 : ( i j : ℕ ) → gcd (i + j) j ≡ gcd i j
gcd2 i j = gcd200 i i j j refl refl where
       gcd202 : (i j1 : ℕ) → (i + suc j1) ≡ suc (i + j1)
       gcd202 zero j1 = refl
       gcd202 (suc i) j1 = cong suc (gcd202 i j1)
       gcd201 : (i i0 j j0 j1 : ℕ) → gcd1 (i + j1) (i0 + suc j) j1 j0 ≡ gcd1 i (i0 + suc j) zero j0
       gcd201 i i0 j j0 zero = subst (λ k → gcd1 k (i0 + suc j) zero j0 ≡ gcd1 i (i0 + suc j) zero j0 ) (+-comm zero i) refl
       gcd201 i i0 j j0 (suc j1) = begin
          gcd1 (i + suc j1)   (i0 + suc j) (suc j1) j0 ≡⟨ cong (λ k → gcd1 k (i0 + suc j) (suc j1) j0 ) (gcd202 i j1) ⟩
          gcd1 (suc (i + j1)) (i0 + suc j) (suc j1) j0 ≡⟨ gcd22 (i + j1) (i0 + suc j) j1 j0 ⟩
          gcd1 (i + j1) (i0 + suc j) j1 j0 ≡⟨ gcd201 i i0 j j0 j1 ⟩
          gcd1 i (i0 + suc j) zero j0 ∎ where open ≡-Reasoning
       gcd200 : (i i0 j j0 : ℕ) → i ≡ i0 → j ≡ j0 → gcd1 (i + j) (i0 + j) j j0 ≡ gcd1 i i j0 j0
       gcd200 i .i zero .0 refl refl = subst (λ k → gcd1 k k zero zero ≡ gcd1 i i zero zero ) (+-comm zero i) refl 
       gcd200 (suc (suc i)) i0 (suc j) (suc j0) i=i0 j=j0 = gcd201 (suc (suc i)) i0 j (suc j0) (suc j)
       gcd200 zero zero (suc zero) .1 i=i0 refl = refl
       gcd200 zero zero (suc (suc j)) .(suc (suc j)) i=i0 refl = begin
          gcd1 (zero + suc (suc j)) (zero + suc (suc j)) (suc (suc j)) (suc (suc j)) ≡⟨ gcdmm (suc (suc j)) (suc (suc j)) ⟩
          suc (suc j) ≡⟨ sym (gcd20 (suc (suc j))) ⟩
          gcd1 zero zero (suc (suc j)) (suc (suc j)) ∎ where open ≡-Reasoning
       gcd200 zero (suc i0) (suc j) .(suc j) () refl
       gcd200 (suc zero) .1 (suc j) .(suc j) refl refl = begin
          gcd1 (1 + suc j) (1 + suc j) (suc j) (suc j) ≡⟨ gcd203 (suc j) ⟩
          1 ≡⟨ sym ( gcd204 (suc j)) ⟩
          gcd1 1 1 (suc j) (suc j) ∎ where open ≡-Reasoning
       gcd200 (suc (suc i)) i0 (suc j) zero i=i0 ()

gcd52 : {i : ℕ } → 1 < suc (suc i)
gcd52 {zero} = a<sa
gcd52 {suc i} = <-trans (gcd52 {i}) a<sa

gcd50 : (i i0 j j0 : ℕ) → 1 < i0 → i ≤ i0 → j ≤ j0 →  gcd1 i i0 j j0 ≤ i0 
gcd50 zero i0 zero j0 0<i i<i0 j<j0 with <-cmp i0 j0
... | tri< a ¬b ¬c = ≤-refl    
... | tri≈ ¬a refl ¬c =  ≤-refl 
... | tri> ¬a ¬b c = ≤-trans refl-≤s c  
gcd50 zero (suc i0) (suc zero) j0 0<i i<i0 j<j0 = gcd51 0<i where 
   gcd51 : 1 < suc i0 → gcd1 zero (suc i0) 1 j0 ≤ suc i0
   gcd51 1<i = ≤to< 1<i
gcd50 zero (suc i0) (suc (suc j)) j0 0<i i<i0 j<j0 = gcd50 i0 (suc i0) (suc j) (suc (suc j)) 0<i refl-≤s refl-≤s
gcd50 (suc zero) i0 zero j0 0<i i<i0 j<j0 = ≤to< 0<i
gcd50 (suc (suc i)) i0 zero zero 0<i i<i0 j<j0 = ≤-refl
gcd50 (suc (suc i)) i0 zero (suc j0) 0<i i<i0 j<j0 = ≤-trans (gcd50 (suc i) (suc (suc i))  j0 (suc j0) gcd52  refl-≤s refl-≤s) i<i0
gcd50 (suc i) i0 (suc j) j0 0<i i<i0 j<j0 = subst (λ k → k ≤ i0 ) (sym (gcd22 i i0 j j0))
   (gcd50 i i0 j j0 0<i (≤-trans refl-≤s i<i0) (≤-trans refl-≤s j<j0)) 

gcd5 : ( n k : ℕ ) → 1 < n → gcd n k ≤ n
gcd5 n k 0<n = gcd50 n n k k 0<n ≤-refl ≤-refl 

gcd6 : ( n k : ℕ ) → 1 < n → gcd k n ≤ n
gcd6 n k 1<n = subst (λ m → m ≤ n) (gcdsym {n} {k}) (gcd5 n k 1<n)

gcd4 : ( n k : ℕ ) → 1 < n  → gcd n k ≡ k → k ≤ n
gcd4 n k 1<n eq = subst (λ m → m ≤ n ) eq (gcd5 n k 1<n)

gcdmul+1 : ( m n : ℕ ) → gcd (m * n + 1) n ≡ 1
gcdmul+1 zero n = gcd204 n
gcdmul+1 (suc m) n = begin
      gcd (suc m * n + 1) n ≡⟨⟩
      gcd (n + m * n + 1) n ≡⟨ cong (λ k → gcd k n ) (begin
         n + m * n + 1 ≡⟨ cong (λ k → k + 1) (+-comm n _) ⟩
         m * n + n + 1 ≡⟨ +-assoc (m * n) _ _ ⟩
         m * n + (n + 1)  ≡⟨ cong (λ k → m * n + k) (+-comm n _) ⟩
         m * n + (1 + n)  ≡⟨ sym ( +-assoc (m * n) _ _ ) ⟩
         m * n + 1 + n ∎ 
       ) ⟩
      gcd (m * n + 1 + n) n ≡⟨ gcd2 (m * n + 1) n ⟩
      gcd (m * n + 1) n ≡⟨ gcdmul+1 m n ⟩
      1 ∎ where open ≡-Reasoning

