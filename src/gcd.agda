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

open Factor

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

gcd20 : (i : ℕ) → gcd i 0 ≡ i
gcd20 zero = refl
gcd20 (suc i) = gcd201 (suc i) where
    gcd201 : (i : ℕ ) → gcd1 i i zero zero ≡ i
    gcd201 zero = refl
    gcd201 (suc zero) = refl
    gcd201 (suc (suc i)) = refl

gcd22 : ( i i0 o o0 : ℕ ) → gcd1 (suc i) i0 (suc o) o0 ≡ gcd1 i i0 o o0
gcd22 zero i0 zero o0 = refl
gcd22 zero i0 (suc o) o0 = refl
gcd22 (suc i) i0 zero o0 = refl
gcd22 (suc i) i0 (suc o) o0 = refl 

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

gcd+j : ( i j : ℕ ) → gcd (i + j) j ≡ gcd i j
gcd+j i j = gcd200 i i j j refl refl where
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

open _∧_

gcd-gt : ( i i0 j j0 k : ℕ ) → k > 1 → (if : Factor k i) (i0f : Dividable k i0 ) (jf : Factor k j ) (j0f : Dividable k j0)
   → Dividable k (i - j) ∧ Dividable k (j - i)
   → Dividable k ( gcd1 i i0 j j0 ) 
gcd-gt zero i0 zero j0 k k>1 if i0f jf j0f i-j with <-cmp i0 j0
... | tri< a ¬b ¬c = i0f 
... | tri≈ ¬a refl ¬c = i0f
... | tri> ¬a ¬b c = j0f
gcd-gt zero i0 (suc zero) j0 k k>1 if i0f jf j0f i-j = ⊥-elim (div1 k>1 (proj2 i-j)) -- can't happen
gcd-gt zero zero (suc (suc j)) j0 k k>1 if i0f jf j0f i-j = j0f
gcd-gt zero (suc i0) (suc (suc j)) j0 k k>1 if i0f jf j0f i-j =   
    gcd-gt i0 (suc i0) (suc j) (suc (suc j))  k k>1 (decf (DtoF i0f)) i0f (decf jf) (proj2 i-j) (div-div k>1 i0f (proj2 i-j))
gcd-gt (suc zero) i0 zero j0 k k>1 if i0f jf j0f i-j  = ⊥-elim (div1 k>1 (proj1 i-j)) -- can't happen
gcd-gt (suc (suc i)) i0 zero zero k k>1 if i0f jf j0f i-j  = i0f
gcd-gt (suc (suc i)) i0 zero (suc j0) k k>1 if i0f jf j0f i-j  = --   
     gcd-gt (suc i) (suc (suc i)) j0 (suc j0) k k>1 (decf if) (proj1 i-j) (decf (DtoF j0f)) j0f (div-div k>1 (proj1 i-j) j0f )
gcd-gt (suc zero) i0 (suc j) j0 k k>1 if i0f jf j0f i-j  =  
     gcd-gt zero i0 j j0 k k>1 (decf if) i0f (decf jf) j0f i-j
gcd-gt (suc (suc i)) i0 (suc j) j0 k k>1 if i0f jf j0f i-j  = 
     gcd-gt (suc i) i0 j j0 k k>1 (decf if) i0f (decf jf) j0f i-j 

gcd-div : ( i j k : ℕ ) → k > 1 → (if : Dividable k i) (jf : Dividable k j ) 
   → Dividable k ( gcd i  j ) 
gcd-div i j k k>1 if jf = gcd-gt i i j j k k>1 (DtoF if) if (DtoF jf) jf (div-div k>1 if jf)

di-next : {i i0 j j0 : ℕ} → Dividable i0  ((j0 + suc i) - suc j ) ∧ Dividable j0 ((i0 + suc j) - suc i) →
           Dividable i0  ((j0 + i) - j ) ∧ Dividable j0 ((i0 + j) - i) 
di-next {i} {i0} {j} {j0} x =
      ⟪ ( subst (λ k → Dividable i0 (k - suc j)) ( begin
               j0 + suc i ≡⟨ sym (+-assoc j0 1 i ) ⟩ 
               (j0 + 1) + i ≡⟨ cong (λ k → k + i) (+-comm j0 _ ) ⟩ 
               suc (j0 + i) ∎ ) (proj1 x) ) ,
       ( subst (λ k → Dividable j0 (k - suc i)) ( begin
               i0 + suc j ≡⟨ sym (+-assoc i0 1 j ) ⟩ 
               (i0 + 1) + j ≡⟨ cong (λ k → k + j) (+-comm i0 _ ) ⟩ 
               suc (i0 + j) ∎ ) (proj2 x) ) ⟫    
           where open ≡-Reasoning

di-next1 : {i0 j j0 : ℕ} →  Dividable (suc i0) ((j0 + 0) - (suc (suc j))) ∧ Dividable j0 (suc (i0 + suc (suc j)))
       →    Dividable (suc i0) ((suc (suc j) + i0) - suc j) ∧ Dividable (suc (suc j)) ((suc i0 + suc j) - i0)
di-next1 {i0} {j} {j0} x = 
      ⟪ record { factor = 1 ; is-factor = begin
           1 * suc i0 + 0 ≡⟨ cong suc ( trans (+-comm _ 0)  (+-comm _ 0) ) ⟩
           suc i0  ≡⟨ sym (minus+y-y {suc i0} {j})  ⟩
           (suc i0 + j) - j ≡⟨ cong (λ k → k - j ) (+-comm (suc i0) _ ) ⟩
           (suc j + suc i0 ) - suc j ≡⟨ cong (λ k → k - suc j) (sym (+-assoc (suc j) 1 i0 ))  ⟩
           ((suc j + 1) + i0) - suc j ≡⟨ cong (λ k → (k + i0) - suc j) (+-comm _ 1) ⟩
           (suc (suc j) + i0) - suc j ∎ }  , 
        subst (λ k → Dividable (suc (suc j)) k) ( begin
               suc (suc j) ≡⟨ sym ( minus+y-y {suc (suc j)}{i0} ) ⟩ 
               (suc (suc j) + i0 ) - i0  ≡⟨ cong (λ k → (k + i0) - i0) (cong suc (+-comm 1 _ )) ⟩ 
               ((suc j + 1) + i0 ) - i0  ≡⟨ cong (λ k → k - i0) (+-assoc (suc j) 1  _ ) ⟩ 
               (suc j + suc i0 ) - i0  ≡⟨ cong (λ k → k - i0) (+-comm (suc j) _) ⟩ 
               ((suc i0 + suc j)   - i0) ∎ ) div= ⟫    
           where open ≡-Reasoning

gcd>0 : ( i j : ℕ ) → 0 < i → 0 < j → 0 < gcd i j  
gcd>0 i j 0<i 0<j = gcd>01 i i j j 0<i 0<j where
     gcd>01 : ( i i0 j j0 : ℕ ) → 0 < i0 → 0 < j0  → gcd1 i i0 j j0 > 0
     gcd>01 zero i0 zero j0 0<i 0<j with <-cmp i0 j0
     ... | tri< a ¬b ¬c = 0<i
     ... | tri≈ ¬a refl ¬c = 0<i
     ... | tri> ¬a ¬b c = 0<j
     gcd>01 zero i0 (suc zero) j0 0<i 0<j = s≤s z≤n
     gcd>01 zero zero (suc (suc j)) j0 0<i 0<j = 0<j 
     gcd>01 zero (suc i0) (suc (suc j)) j0 0<i 0<j = gcd>01 i0 (suc i0) (suc j) (suc (suc j)) 0<i (s≤s z≤n) -- 0 < suc (suc j)
     gcd>01 (suc zero) i0 zero j0 0<i 0<j =  s≤s z≤n
     gcd>01 (suc (suc i)) i0 zero zero 0<i 0<j = 0<i 
     gcd>01 (suc (suc i)) i0 zero (suc j0) 0<i 0<j = gcd>01 (suc i) (suc (suc i))  j0 (suc j0) (s≤s z≤n) 0<j 
     gcd>01 (suc i) i0 (suc j) j0 0<i 0<j = subst (λ k → 0 < k ) (sym (gcd033 i i0 j j0 )) (gcd>01 i i0 j j0 0<i 0<j ) where
         gcd033 : (i i0 j j0  : ℕ) → gcd1 (suc i) i0 (suc j) j0 ≡  gcd1 i i0 j j0
         gcd033 zero zero zero zero = refl
         gcd033 zero zero (suc j) zero = refl
         gcd033 (suc i) zero j zero = refl
         gcd033 zero zero zero (suc j0) = refl
         gcd033 (suc i) zero zero (suc j0) = refl
         gcd033 zero zero (suc j) (suc j0) = refl
         gcd033 (suc i) zero (suc j) (suc j0) = refl
         gcd033 zero (suc i0) j j0 = refl
         gcd033 (suc i) (suc i0) j j0 = refl

-- gcd loop invariant
--
record GCD ( i i0 j j0 : ℕ ) : Set where
   field
     i<i0  : i ≤ i0
     j<j0  : j ≤ j0
     div-i : Dividable i0 ((j0 + i) - j)
     div-j : Dividable j0 ((i0 + j) - i)

div-11 : {i j : ℕ } → Dividable i ((j + i) - j)
div-11 {i} {j} = record { factor = 1 ; is-factor = begin 
   1 * i + 0 ≡⟨ +-comm _ 0  ⟩
   i + 0  ≡⟨  +-comm _ 0 ⟩
   i  ≡⟨ sym (minus+y-y {i} {j}) ⟩
   (i + j ) - j  ≡⟨ cong (λ k → k  - j ) (+-comm i j )  ⟩
   (j + i) - j ∎ } where open ≡-Reasoning

div→gcd : {n k : ℕ } → k > 1 → Dividable k n → gcd n k ≡ k
div→gcd {n} {k} k>1 = n-induction {_} {_} {ℕ} {λ m → Dividable k m → gcd m k ≡ k } (λ x → x) I n where
        decl : {m  : ℕ } → 0 < m → m - k < m
        decl {m} 0<m = y-x<y (<-trans a<sa k>1 ) 0<m 
        ind : (m : ℕ ) → (Dividable k (m - k) → gcd (m - k) k ≡ k) → Dividable k m → gcd m k ≡ k
        ind m prev d with <-cmp (suc m) k
        ... | tri≈ ¬a refl ¬c = ⊥-elim ( div+1 k>1 d div= )
        ... | tri>  ¬a ¬b c = subst (λ g → g ≡ k) ind1 ( prev (proj2 (div-div k>1 div= d))) where
           ind1 : gcd (m - k) k ≡ gcd m k
           ind1 = begin
               gcd (m - k) k  ≡⟨ sym (gcd+j (m - k)  _) ⟩
               gcd (m - k + k) k ≡⟨ cong (λ g → gcd g k) (minus+n {m} {k} c) ⟩
               gcd m k ∎ where open ≡-Reasoning
        ... | tri< a ¬b ¬c with <-cmp 0 m 
        ... | tri< a₁ ¬b₁ ¬c₁ = ⊥-elim ( div<k k>1 a₁ (<-trans a<sa a) d )
        ... | tri≈ ¬a refl ¬c₁ = subst (λ g → g ≡ k ) (gcdsym {k} {0} ) (gcd20 k)
        fzero : (m : ℕ) → (m - k) ≡ zero → Dividable k m → gcd m k ≡ k 
        fzero 0 eq d = trans  (gcdsym {0} {k} ) (gcd20 k) 
        fzero (suc m) eq d with <-cmp (suc m) k
        ... | tri< a ¬b ¬c = ⊥-elim ( div<k k>1 (s≤s z≤n) a d )
        ... | tri≈ ¬a refl ¬c = gcdmm k k
        ... | tri> ¬a ¬b c = ⊥-elim ( nat-≡< (sym eq) (minus>0 c) )
        I : Ninduction ℕ  _  (λ x → x)
        I = record {
              pnext = λ p → p - k
            ; fzero = λ {m} eq → fzero m eq
            ; decline = λ {m} lt → decl lt 
            ; ind = λ {p} prev → ind p prev
          } 

GCDi : {i j : ℕ } → GCD i i j j
GCDi {i} {j} = record { i<i0 = refl-≤ ; j<j0 = refl-≤ ; div-i = div-11 {i} {j} ; div-j = div-11 {j} {i} }

GCD-sym : {i i0 j j0 : ℕ} → GCD i i0 j j0 → GCD j j0 i i0
GCD-sym g = record { i<i0 = GCD.j<j0 g ; j<j0 = GCD.i<i0 g ; div-i = GCD.div-j g ; div-j = GCD.div-i g }

pred-≤ : {i i0 : ℕ } → suc i ≤ suc i0 → i ≤ suc i0
pred-≤ {i} {i0} (s≤s lt) = ≤-trans lt refl-≤s

gcd-next : {i i0 j j0 : ℕ} → GCD (suc i) i0 (suc j) j0 → GCD i i0 j j0
gcd-next {i} {0} {j} {0} ()
gcd-next {i} {suc i0} {j} {suc j0} g = record { i<i0 = pred-≤ (GCD.i<i0 g) ; j<j0 = pred-≤ (GCD.j<j0 g)
  ; div-i = proj1 (di-next {i} {suc i0} {j} {suc j0} ⟪ GCD.div-i g , GCD.div-j g ⟫ )
  ; div-j = proj2 (di-next {i} {suc i0} {j} {suc j0} ⟪ GCD.div-i g , GCD.div-j g ⟫ ) }

gcd-next1 : {i0 j j0 : ℕ} → GCD 0 (suc i0) (suc (suc j)) j0 → GCD i0 (suc i0) (suc j) (suc (suc j)) 
gcd-next1 {i0} {j} {j0} g = record { i<i0 = refl-≤s ; j<j0 = refl-≤s
  ; div-i = proj1 (di-next1 ⟪ GCD.div-i g , GCD.div-j g ⟫ ) ; div-j = proj2 (di-next1 ⟪ GCD.div-i g , GCD.div-j g ⟫ ) }


-- gcd-dividable1 : ( i i0 j j0 : ℕ )
--      → Dividable i0  (j0 + i - j ) ∨ Dividable j0 (i0 + j - i)
--      → Dividable ( gcd1 i i0 j j0  ) i0 ∧ Dividable ( gcd1 i i0 j j0  ) j0
-- gcd-dividable1  zero i0 zero j0 with <-cmp i0 j0
-- ... | tri< a ¬b ¬c = ⟪ div= , {!!} ⟫ -- Dividable i0  (j0 + i - j ) ∧ Dividable j0 (i0 + j - i)
-- ... | tri≈ ¬a refl ¬c = {!!}
-- ... | tri> ¬a ¬b c = {!!}
-- gcd-dividable1 zero i0 (suc zero) j0 = {!!}
-- gcd-dividable1 i i0 j j0 = {!!}

gcd-dividable : ( i j  : ℕ )
      → Dividable ( gcd i j ) i ∧ Dividable ( gcd i j ) j
gcd-dividable i j  = f-induction {_} {_} {ℕ ∧ ℕ}
   {λ p  → Dividable ( gcd (proj1 p) (proj2 p) ) (proj1 p) ∧ Dividable ( gcd (proj1 p)  (proj2 p) ) (proj2 p)} F I ⟪ i , j ⟫ where
        F : ℕ ∧ ℕ → ℕ
        F ⟪ 0 , 0 ⟫ = 0
        F ⟪ 0 , suc j ⟫ = 0
        F ⟪ suc i , 0 ⟫ = 0
        F ⟪ suc i , suc j ⟫ with <-cmp i j
        ... | tri< a ¬b ¬c = suc j
        ... | tri≈ ¬a b ¬c = 0
        ... | tri> ¬a ¬b c = suc i
        F0 : { i j : ℕ } → F ⟪ i , j ⟫ ≡ 0 → (i ≡ j) ∨ (i ≡ 0 ) ∨ (j ≡ 0)
        F0 {zero} {zero} p = case1 refl
        F0 {zero} {suc j} p =  case2 (case1 refl)
        F0 {suc i} {zero} p =  case2 (case2 refl)
        F0 {suc i} {suc j} p with <-cmp i j
        ... | tri< a ¬b ¬c = ⊥-elim ( nat-≡< (sym p) (s≤s z≤n ))
        ... | tri≈ ¬a refl ¬c =  case1 refl
        ... | tri> ¬a ¬b c = ⊥-elim ( nat-≡< (sym p) (s≤s z≤n ))
        F00 :  {p : ℕ ∧ ℕ} → F p ≡ zero → Dividable (gcd (proj1 p) (proj2 p)) (proj1 p) ∧ Dividable (gcd (proj1 p) (proj2 p)) (proj2 p)
        F00 {⟪ i , j ⟫} eq with F0 {i} {j} eq
        ... | case1 refl = ⟪  subst (λ k → Dividable k i) (sym (gcdmm i i)) div= , subst (λ k → Dividable k i) (sym (gcdmm i i)) div= ⟫
        ... | case2 (case1 refl) = ⟪  subst (λ k → Dividable k i) (sym (trans (gcdsym {0} {j} ) (gcd20 j)))div0
                                    , subst (λ k → Dividable k j) (sym (trans (gcdsym {0} {j}) (gcd20 j))) div= ⟫
        ... | case2 (case2 refl) = ⟪  subst (λ k → Dividable k i) (sym (gcd20 i)) div=
                                    , subst (λ k → Dividable k j) (sym (gcd20 i)) div0 ⟫
        Fsym :  {i j : ℕ } → F ⟪ i , j ⟫ ≡ F ⟪ j , i ⟫
        Fsym {0} {0} = refl
        Fsym {0} {suc j} = refl
        Fsym {suc i} {0} = refl
        Fsym {suc i} {suc j} with <-cmp i j | <-cmp j i
        ... | tri< a ¬b ¬c | tri< a₁ ¬b₁ ¬c₁ = ⊥-elim (nat-<> a a₁)
        ... | tri< a ¬b ¬c | tri≈ ¬a b ¬c₁ = ⊥-elim (¬b (sym b))
        ... | tri< a ¬b ¬c | tri> ¬a ¬b₁ c = refl
        ... | tri≈ ¬a refl ¬c | tri< a ¬b ¬c₁ = ⊥-elim (¬b refl)
        ... | tri≈ ¬a refl ¬c | tri≈ ¬a₁ refl ¬c₁ = refl
        ... | tri≈ ¬a refl ¬c | tri> ¬a₁ ¬b c = ⊥-elim (¬b refl)
        ... | tri> ¬a ¬b c | tri< a ¬b₁ ¬c = refl
        ... | tri> ¬a ¬b c | tri≈ ¬a₁ b ¬c = ⊥-elim (¬b (sym b))
        ... | tri> ¬a ¬b c | tri> ¬a₁ ¬b₁ c₁ = ⊥-elim (nat-<> c c₁)

        record Fdec ( i j : ℕ ) : Set where
           field
               ni : ℕ 
               nj : ℕ 
               fdec :  0 < F ⟪ i , j ⟫  → F ⟪ ni , nj ⟫  < F ⟪ i , j ⟫

        fd1 : ( i j k : ℕ ) → i < j  → k ≡ j - i →  F ⟪ suc i , k ⟫ < F ⟪ suc i , suc j ⟫
        fd1 i j 0 i<j eq = ⊥-elim ( nat-≡< eq (minus>0 {i} {j} i<j )) 
        fd1 i j (suc k) i<j eq = fd2 i j k i<j eq where
               fd2 : ( i j k : ℕ ) → i < j → suc k ≡ j - i  →  F ⟪ suc i , suc k ⟫ < F ⟪ suc i , suc j ⟫
               fd2 i j k i<j eq with <-cmp i k | <-cmp i j
               ... | tri< a ¬b ¬c | tri< a₁ ¬b₁ ¬c₁ = fd3 where
                    fd3 : suc k < suc j  -- suc j - suc i < suc j
                    fd3 = subst (λ g → g < suc j) (sym eq) (y-x<y {suc i} {suc j} (s≤s z≤n) (s≤s z≤n))
               ... | tri< a ¬b ¬c | tri≈ ¬a b ¬c₁ = ⊥-elim (⊥-elim (¬a i<j))
               ... | tri< a ¬b ¬c | tri> ¬a ¬b₁ c = ⊥-elim (⊥-elim (¬a i<j))
               ... | tri≈ ¬a b ¬c | tri< a ¬b ¬c₁ = s≤s z≤n
               ... | tri≈ ¬a b ¬c | tri≈ ¬a₁ b₁ ¬c₁ = ⊥-elim (¬a₁ i<j)
               ... | tri≈ ¬a b ¬c | tri> ¬a₁ ¬b c =  s≤s z≤n -- i > j
               ... | tri> ¬a ¬b c | tri< a ¬b₁ ¬c = fd4 where
                    fd4 : suc i < suc j
                    fd4 = s≤s a
               ... | tri> ¬a ¬b c | tri≈ ¬a₁ b ¬c =  ⊥-elim (¬a₁ i<j)
               ... | tri> ¬a ¬b c | tri> ¬a₁ ¬b₁ c₁ =  ⊥-elim (¬a₁ i<j)

        fedc0 : (i j : ℕ ) → Fdec i j
        fedc0 0 0 = record { ni =  0 ; nj = 0 ; fdec = λ ()  } 
        fedc0 (suc i) 0 = record { ni =  suc i ; nj = 0 ; fdec = λ ()  } 
        fedc0 0 (suc j)  = record { ni =  0 ; nj = suc j ; fdec = λ ()  } 
        fedc0 (suc i) (suc j) with <-cmp i j
        ... | tri< i<j ¬b ¬c = record { ni =  suc i ; nj = j - i ; fdec = λ lt → fd1 i j (j - i) i<j refl  } 
        ... | tri≈ ¬a refl ¬c = record { ni =  suc i ; nj = suc j     ; fdec = λ lt → ⊥-elim (nat-≡< fd0 lt) } where
              fd0 : {i : ℕ } → 0 ≡ F ⟪ suc i , suc i ⟫
              fd0 {i} with <-cmp i i
              ... | tri< a ¬b ¬c = ⊥-elim ( ¬b refl )
              ... | tri≈ ¬a b ¬c = refl
              ... | tri> ¬a ¬b c =  ⊥-elim ( ¬b refl )
        ... | tri> ¬a ¬b c = record { ni =  i - j ; nj = suc j ; fdec = λ lt →
            subst₂ (λ s t → s < t) (Fsym {suc j} {i - j}) (Fsym {suc j} {suc i}) (fd1 j i (i - j) c refl ) } 

        ind3 : {i j : ℕ } → i < j 
               → Dividable (gcd (suc i) (j - i)) (suc i) 
               → Dividable (gcd (suc i) (suc j)) (suc i) 
        ind3 {i} {j} a prev = 
               subst (λ k → Dividable k (suc i)) ( begin
                 gcd (suc i) (j - i)  ≡⟨ gcdsym {suc i} {j - i} ⟩
                 gcd (j - i ) (suc i)   ≡⟨ sym (gcd+j (j - i) (suc i)) ⟩
                 gcd ((j - i) + suc i) (suc i)  ≡⟨ cong (λ k → gcd k (suc i)) ( begin
                  (suc j - suc i) + suc i ≡⟨ minus+n {suc j} {suc i} (<-trans ( s≤s a) a<sa ) ⟩ -- i ≤ n →  suc (suc i) ≤ suc (suc (suc n)) 
                  suc j ∎ ) ⟩
                 gcd (suc j) (suc i)  ≡⟨ gcdsym {suc j} {suc i} ⟩
                 gcd (suc i) (suc j)  ∎ ) prev where open ≡-Reasoning 
        ind7 : {i j : ℕ } → (i < j ) → (j - i) + suc i ≡ suc j
        ind7 {i} {j} a = begin (suc j - suc i) + suc i ≡⟨ minus+n {suc j} {suc i} (<-trans (s≤s a) a<sa)  ⟩
                        suc j ∎  where open ≡-Reasoning 
        ind6 : {i j k : ℕ } → i < j
               → Dividable k (j - i)
               → Dividable k (suc i) 
               → Dividable k (suc j)
        ind6 {i} {j} {k} i<j dj di = subst (λ g → Dividable k g ) (ind7 i<j) (proj1 (div+div dj di)) 
        ind4 : {i j : ℕ } → i < j
               → Dividable (gcd (suc i) (j - i)) (j - i)
               → Dividable (gcd (suc i) (suc j)) (j - i)
        ind4 {i} {j} i<j prev = subst (λ k → k) ( begin
                 Dividable (gcd (suc i) (j - i)) (j - i)  ≡⟨ cong  (λ k → Dividable k (j - i)) (gcdsym {suc i}  ) ⟩
                 Dividable (gcd (j - i ) (suc i) ) (j - i)  ≡⟨ cong  (λ k → Dividable k (j - i)) ( sym (gcd+j  (j - i) (suc i))) ⟩
                 Dividable (gcd ((j - i) + suc i) (suc i)) (j - i)  ≡⟨ cong  (λ k → Dividable (gcd k (suc i)) (j - i)) (ind7 i<j ) ⟩
                 Dividable (gcd (suc j) (suc i)) (j - i)    ≡⟨ cong  (λ k → Dividable k (j - i)) (gcdsym {suc j} ) ⟩
                 Dividable (gcd (suc i) (suc j)) (j - i)   ∎ ) prev where open ≡-Reasoning 

        ind :   ( i j : ℕ ) →
              Dividable (gcd (Fdec.ni (fedc0 i j)) (Fdec.nj (fedc0 i j))) (Fdec.ni (fedc0 i j))
            ∧ Dividable (gcd (Fdec.ni (fedc0 i j)) (Fdec.nj (fedc0 i j))) (Fdec.nj (fedc0 i j))
            → Dividable (gcd i j) i ∧ Dividable (gcd i j) j
        ind zero zero prev = ind0 where
           ind0 : Dividable (gcd zero zero) zero ∧ Dividable (gcd zero zero) zero
           ind0 = ⟪ div0 , div0 ⟫
        ind zero (suc j) prev = ind1 where
           ind1 : Dividable (gcd zero (suc j)) zero ∧ Dividable (gcd zero (suc j)) (suc j)
           ind1 = ⟪ div0 , subst (λ k → Dividable k (suc j)) (sym (trans (gcdsym {zero} {suc j}) (gcd20 (suc j)))) div=  ⟫
        ind (suc i) zero prev = ind2 where
           ind2 : Dividable (gcd (suc i) zero) (suc i) ∧ Dividable (gcd (suc i) zero) zero
           ind2 = ⟪  subst (λ k → Dividable k (suc i)) (sym (trans refl (gcd20 (suc i)))) div= , div0 ⟫
        ind (suc i) (suc j) prev with <-cmp i j
        ... | tri< a ¬b ¬c = ⟪ ind3 a (proj1 prev)  , ind6 a (ind4 a (proj2 prev)) (ind3 a (proj1 prev) ) ⟫ 
        ... | tri≈ ¬a refl ¬c = ⟪ ind5 , ind5 ⟫ where
           ind5 : Dividable (gcd (suc i) (suc i)) (suc i) 
           ind5 = subst (λ k → Dividable k (suc j)) (sym (gcdmm (suc i) (suc i))) div=  
        ... | tri> ¬a ¬b c = ⟪ ind8 c (proj1 prev) (proj2 prev) , ind10 c  (proj2 prev) ⟫ where
           ind9 : {i j : ℕ} → i < j → gcd (j - i) (suc i) ≡ gcd (suc j) (suc i)
           ind9 {i} {j} i<j = begin
                 gcd (j - i ) (suc i)    ≡⟨ sym (gcd+j (j - i ) (suc i)  ) ⟩
                 gcd (j - i + suc i) (suc i)    ≡⟨ cong (λ k → gcd k (suc i)) (ind7 i<j ) ⟩
                 gcd (suc j) (suc i)   ∎  where open ≡-Reasoning 
           ind8 :  { i j : ℕ } → i < j
               → Dividable (gcd (j - i) (suc i)) (j - i) 
               → Dividable (gcd (j - i) (suc i)) (suc i)
               → Dividable (gcd (suc j) (suc i)) (suc j)
           ind8 {i} {j} i<j dji di = ind6 i<j (subst (λ k → Dividable k (j - i)) (ind9 i<j) dji)  (subst (λ k → Dividable k (suc i)) (ind9 i<j) di) 
           ind10 :  { i j : ℕ } → j < i
               → Dividable (gcd (i - j) (suc j)) (suc j)
               → Dividable (gcd (suc i) (suc j)) (suc j)
           ind10 {i} {j} j<i dji = subst (λ g → Dividable g (suc j) ) (begin
             gcd (i - j) (suc j)  ≡⟨ sym (gcd+j (i - j) (suc j)) ⟩
             gcd (i - j + suc j) (suc j)  ≡⟨ cong (λ k → gcd k (suc j)) (ind7 j<i ) ⟩
             gcd (suc i) (suc j) ∎ ) dji where open ≡-Reasoning 

        I : Finduction (ℕ ∧ ℕ) _ F
        I = record {
              fzero = F00 
            ; pnext = λ p → ⟪ Fdec.ni (fedc0 (proj1 p) (proj2 p)) ,  Fdec.nj (fedc0 (proj1 p) (proj2 p)) ⟫ 
            ; decline = λ {p} lt → Fdec.fdec (fedc0 (proj1 p) (proj2 p))  lt
            ; ind = λ {p} prev → ind (proj1 p ) ( proj2 p ) prev
          } 

f-div>0 :  { k i  : ℕ } → (d : Dividable k i ) → 0 < i → 0 < Dividable.factor d 
f-div>0 {k} {i} d 0<i with <-cmp 0 (Dividable.factor d)
... | tri< a ¬b ¬c = a
... | tri≈ ¬a b ¬c = ⊥-elim ( nat-≡< (begin
      0 * k + 0  ≡⟨ cong (λ g → g * k + 0) b  ⟩
      Dividable.factor d * k + 0  ≡⟨ Dividable.is-factor d ⟩
      i  ∎ ) 0<i ) where open ≡-Reasoning

gcd-≤i : ( i j  : ℕ ) → 0 < i → i ≤ j → gcd i j ≤ i
gcd-≤i zero _ () z≤n 
gcd-≤i (suc i) (suc j) _ (s≤s i<j) = begin
      gcd (suc i) (suc j)   ≡⟨ sym m*1=m ⟩
      gcd (suc i) (suc j) * 1  ≤⟨ *-monoʳ-≤ (gcd (suc i) (suc j)) (f-div>0 d (s≤s z≤n)) ⟩
      gcd (suc i) (suc j) * f  ≡⟨ +-comm 0 _ ⟩
      gcd (suc i) (suc j) * f  + 0  ≡⟨ cong (λ k → k + 0) (*-comm (gcd (suc i) (suc j)) _  ) ⟩
      Dividable.factor (proj1 (gcd-dividable (suc i) (suc j))) * gcd (suc i) (suc j) + 0 ≡⟨ Dividable.is-factor (proj1 (gcd-dividable (suc i) (suc j)))  ⟩
      suc i  ∎ where
          d = proj1 (gcd-dividable (suc i) (suc j))
          f = Dividable.factor (proj1 (gcd-dividable (suc i) (suc j)))
          open ≤-Reasoning

gcd-≤ : { i j  : ℕ } → 0 < i → 0 < j  →  gcd i j ≤ i
gcd-≤ {i} {j} 0<i 0<j with <-cmp i j
... | tri< a ¬b ¬c = gcd-≤i i j 0<i (<to≤ a)
... | tri≈ ¬a refl ¬c = gcd-≤i i j 0<i refl-≤
... | tri> ¬a ¬b c = ≤-trans (subst (λ k → k ≤ j) (gcdsym {j} {i}) (gcd-≤i j i 0<j (<to≤ c))) (<to≤ c)

record Euclid (i j gcd : ℕ ) : Set where
  field
    eqa : ℕ
    eqb : ℕ
    is-equ< : eqa * i > eqb * j → (eqa * i) - (eqb * j) ≡ gcd  
    is-equ> : eqb * j > eqa * i → (eqb * j) - (eqa * i) ≡ gcd  
    is-equ= : eqa * i ≡ eqb * j → 0 ≡ gcd  

ge3 : {a b c d : ℕ } → b > a → b - a ≡ d - c → d > c
ge3 {a} {b} {c} {d} b>a eq = minus>0→x<y (subst (λ k → 0 < k ) eq (minus>0 b>a))

ge01 : ( i0 j j0 ea eb : ℕ )  
   → ( di : GCD 0 (suc i0) (suc (suc j)) j0 )
  →  (((ea + eb * (Dividable.factor (GCD.div-i di))) * suc i0)  ≡ (ea * suc i0) + (eb * (Dividable.factor (GCD.div-i di)) ) * suc i0 )
        ∧ (  (eb * j0) ≡ (eb * suc (suc j) +  (eb * (Dividable.factor (GCD.div-i di)) ) * suc i0) )
ge01 i0 j j0 ea eb di  = ⟪ ge011 , ge012 ⟫ where
   f = Dividable.factor (GCD.div-i di)
   ge4 :  suc (j0 + 0) > suc (suc j)
   ge4 = subst (λ k → k > suc (suc j)) (+-comm 0 _ ) ( s≤s (GCD.j<j0  di ))
   ge011 :   (ea + eb * f) * suc i0 ≡ ea * suc i0 + eb * f * suc i0
   ge011 = begin
      (ea + eb * f) * suc i0 ≡⟨ *-distribʳ-+ (suc i0)  ea  _ ⟩ 
      ea * suc i0 + eb * f * suc i0 ∎ where open ≡-Reasoning
   ge012 :  eb * j0 ≡ eb * suc (suc j) + eb * f * suc i0
   ge012 = begin
      eb * j0  ≡⟨ cong (λ k → eb * k) ( begin
        j0 ≡⟨ +-comm 0 _ ⟩ 
        j0 + 0 ≡⟨ sym (minus+n {j0 + 0} {suc (suc j)} ge4)  ⟩ 
        ((j0 + 0) - (suc (suc j))) + suc (suc j) ≡⟨  +-comm _ (suc (suc j)) ⟩ 
        suc (suc j) + ((j0 + 0) -  suc (suc j)) ≡⟨ cong (λ k → suc (suc j) + k ) (sym (Dividable.is-factor (GCD.div-i di))) ⟩ 
        suc (suc j) + (f * suc i0 + 0) ≡⟨  cong (λ k → suc (suc j) + k )  ( +-comm _ 0  ) ⟩ 
        suc (suc j) + (f * suc i0 )  ∎  ) ⟩ 
      eb * (suc (suc j) + (f * suc i0 ) ) ≡⟨ *-distribˡ-+  eb (suc (suc j)) (f * suc i0) ⟩ 
      eb * suc (suc j) + eb * (f * suc i0) ≡⟨ cong (λ k → eb * suc (suc j) + k ) ((sym (*-assoc eb _ _ )) ) ⟩ 
      eb * suc (suc j) + eb * f * suc i0 ∎ where open ≡-Reasoning

ge20 : {i0 j0 : ℕ } →  i0 ≡ 0 → 0 ≡ gcd1 zero i0 zero j0 
ge20 {i0} {zero} refl = refl
ge20 {i0} {suc j0} refl = refl

gcd-euclid1 : ( i i0 j j0 : ℕ )  → GCD i i0 j j0  → Euclid i0 j0 (gcd1 i i0 j j0)
gcd-euclid1 zero i0 zero j0 di with <-cmp i0 j0
... | tri< a' ¬b ¬c = record { eqa = 1 ; eqb = 0 ; is-equ< = λ _ → +-comm _ 0 ; is-equ> = λ () ; is-equ= = ge21 }  where
   ge21 : 1 * i0 ≡ 0 * j0 → 0 ≡ i0
   ge21 eq = trans (sym eq) (+-comm i0 0) 
... | tri≈ ¬a refl ¬c = record { eqa = 1 ; eqb = 0 ; is-equ< = λ _ → +-comm _ 0 ; is-equ> = λ () ; is-equ= = λ eq →  trans (sym eq) (+-comm i0 0) } 
... | tri> ¬a ¬b c = record { eqa = 0 ; eqb = 1 ;  is-equ< = λ () ; is-equ> = λ _ → +-comm _ 0 ; is-equ= = ge22 }  where
   ge22 : 0 * i0 ≡ 1 * j0 → 0 ≡ j0
   ge22 eq = trans eq (+-comm j0 0) 
-- i<i0  : zero ≤ i0
-- j<j0  : 1 ≤ j0
-- div-i : Dividable i0 ((j0 + zero) - 1)  -- fi * i0 ≡ (j0 + zero) - 1
-- div-j : Dividable j0 ((i0 + 1) - zero) --  fj * j0 ≡ (i0 + 1) - zero
gcd-euclid1 zero i0 (suc zero) j0 di = record { eqa = 1 ; eqb = Dividable.factor (GCD.div-j di) ; is-equ< = λ lt → ⊥-elim ( ge7 lt) ; is-equ> = λ _ → ge6
      ; is-equ= = λ eq → ⊥-elim (nat-≡< (sym (minus<=0 (subst (λ k → k ≤ 1 * i0) eq refl-≤ ))) (subst (λ k → 0 < k) (sym ge6) a<sa )) } where
   ge6 :  (Dividable.factor (GCD.div-j di) * j0) - (1 * i0) ≡ gcd1 zero i0 1 j0
   ge6  =  begin
        (Dividable.factor (GCD.div-j di) * j0) - (1 * i0)   ≡⟨  cong (λ k → k  - (1 * i0)) (+-comm 0 _)  ⟩
        (Dividable.factor (GCD.div-j di) * j0 + 0) - (1 * i0)   ≡⟨ cong (λ k → k  - (1 * i0)) (Dividable.is-factor (GCD.div-j di) )  ⟩
        ((i0 + 1) - zero) - (1 * i0)   ≡⟨ refl  ⟩
        (i0 + 1) - (i0 + 0)   ≡⟨ minus+yx-yz {_} {i0} {0}  ⟩
       1   ∎ where open ≡-Reasoning
   ge7 : ¬ ( 1 * i0 > Dividable.factor (GCD.div-j di) * j0 )
   ge7 lt = ⊥-elim ( nat-≡< (sym ( minus<=0 (<to≤ lt))) (subst (λ k → 0 < k) (sym ge6) (s≤s z≤n)))
gcd-euclid1 zero zero (suc (suc j)) j0 di = record { eqa = 0 ; eqb = 1 ; is-equ< = λ () ; is-equ> = λ _ → +-comm _ 0
    ; is-equ= = λ eq → subst (λ k → 0 ≡ k) (+-comm _ 0) eq } 
gcd-euclid1 zero (suc i0) (suc (suc j)) j0 di with gcd-euclid1 i0 (suc i0) (suc j) (suc (suc j)) ( gcd-next1 di )
... | e = record { eqa = ea + eb * f ; eqb =  eb 
      ;  is-equ= =  λ eq → Euclid.is-equ= e (ge23 eq) 
      ;  is-equ< =  λ lt → subst (λ k → ((ea + eb * f) * suc i0) - (eb * j0) ≡ k ) (Euclid.is-equ< e (ge3 lt (ge1 ))) (ge1 )
      ;  is-equ> =  λ lt → subst (λ k → (eb * j0) - ((ea + eb * f) * suc i0) ≡ k ) (Euclid.is-equ> e (ge3 lt (ge2 ))) (ge2 ) } where
   ea = Euclid.eqa e 
   eb = Euclid.eqb e
   f = Dividable.factor (GCD.div-i di)
   ge1 : ((ea + eb * f) * suc i0) - (eb * j0)  ≡ (ea * suc i0) - (eb * suc (suc j))       
   ge1 = begin
      ((ea + eb * f) * suc i0) - (eb * j0) ≡⟨ cong₂ (λ j k → j - k ) (proj1 (ge01  i0 j j0 ea eb di)) (proj2 (ge01  i0 j j0 ea eb di))  ⟩
      (ea * suc i0 + (eb * f ) * suc i0 ) - ( eb * suc (suc j) + ((eb * f) * (suc i0)) )  ≡⟨ minus+xy-zy {ea * suc i0} {(eb * f ) * suc i0} {eb * suc (suc j)}  ⟩
      (ea * suc i0) - (eb * suc (suc j)) ∎ where open ≡-Reasoning
   ge2 : (eb * j0) - ((ea + eb * f) * suc i0)  ≡  (eb * suc (suc j)) - (ea * suc i0)
   ge2 = begin
      (eb * j0) - ((ea + eb * f) * suc i0)  ≡⟨ cong₂ (λ j k → j - k ) (proj2 (ge01  i0 j j0 ea eb di)) (proj1 (ge01  i0 j j0 ea eb di))  ⟩
      ( eb * suc (suc j) + ((eb * f) * (suc i0)) ) - (ea * suc i0 + (eb * f ) * suc i0 )   ≡⟨  minus+xy-zy {eb * suc (suc j)}{(eb * f ) * suc i0} {ea * suc i0}  ⟩
      (eb * suc (suc j)) - (ea * suc i0)   ∎ where open ≡-Reasoning
   ge23 : (ea + eb * f) * suc i0 ≡ eb * j0 → ea * suc i0 ≡ eb * suc (suc j)
   ge23 eq = begin
       ea * suc i0     ≡⟨ sym (minus+y-y {_} {(eb * f ) * suc i0} ) ⟩
       (ea * suc i0 +  ((eb * f ) * suc i0 )) -  ((eb * f ) * suc i0 )  ≡⟨ cong (λ k → k - ((eb * f ) * suc i0 )) (sym ( proj1 (ge01  i0 j j0 ea eb di)))  ⟩
       ((ea + eb * f) * suc i0)  -  ((eb * f ) * suc i0 )  ≡⟨ cong (λ k → k - ((eb * f ) * suc i0 ))  eq ⟩
        (eb * j0) -  ((eb * f ) * suc i0 )  ≡⟨  cong (λ k → k - ((eb * f ) * suc i0 )) ( proj2 (ge01  i0 j j0 ea eb di)) ⟩
       (eb * suc (suc j) +  ((eb * f ) * suc i0 )) -  ((eb * f ) * suc i0 )  ≡⟨ minus+y-y {_} {(eb * f ) * suc i0 }  ⟩
       eb * suc (suc j)   ∎ where open ≡-Reasoning
gcd-euclid1 (suc zero) i0 zero j0 di = record { eqb = 1 ; eqa = Dividable.factor (GCD.div-i di) ; is-equ> = λ lt → ⊥-elim ( ge7' lt) ; is-equ< = λ _ → ge6'
       ; is-equ= = λ eq → ⊥-elim (nat-≡< (sym (minus<=0 (subst (λ k → k ≤ 1 * j0) (sym eq) refl-≤ ))) (subst (λ k → 0 < k) (sym ge6') a<sa )) } where
   ge6' :  (Dividable.factor (GCD.div-i di) * i0) - (1 * j0) ≡ gcd1 (suc zero) i0 zero j0 
   ge6'  =  begin
        (Dividable.factor (GCD.div-i di) * i0) - (1 * j0)   ≡⟨  cong (λ k → k  - (1 * j0)) (+-comm 0 _)  ⟩
        (Dividable.factor (GCD.div-i di) * i0 + 0) - (1 * j0)   ≡⟨ cong (λ k → k  - (1 * j0)) (Dividable.is-factor (GCD.div-i di) )  ⟩
        ((j0 + 1) - zero) - (1 * j0)   ≡⟨ refl  ⟩
        (j0 + 1) - (j0 + 0)   ≡⟨ minus+yx-yz {_} {j0} {0}  ⟩
       1   ∎ where open ≡-Reasoning
   ge7' : ¬ ( 1 * j0 > Dividable.factor (GCD.div-i di) * i0 )
   ge7' lt = ⊥-elim ( nat-≡< (sym ( minus<=0 (<to≤ lt))) (subst (λ k → 0 < k) (sym ge6') (s≤s z≤n)))
gcd-euclid1 (suc (suc i)) i0 zero zero di = record { eqb = 0 ; eqa = 1 ; is-equ> = λ () ; is-equ< = λ _ → +-comm _ 0
    ; is-equ= =  λ eq → subst (λ k → 0 ≡ k) (+-comm _ 0) (sym eq) }
gcd-euclid1 (suc (suc i)) i0 zero (suc j0) di with gcd-euclid1 (suc i) (suc (suc i)) j0 (suc j0) (GCD-sym (gcd-next1 (GCD-sym di)))
... | e =  record { eqa = ea ; eqb =  eb + ea * f
      ; is-equ= = λ eq → Euclid.is-equ= e (ge24 eq)
      ;  is-equ< =  λ lt → subst (λ k → ((ea * i0) - ((eb + ea * f) * suc j0))  ≡ k ) (Euclid.is-equ< e (ge3 lt ge4)) ge4 
      ;  is-equ> =  λ lt → subst (λ k →  (((eb + ea * f) * suc j0) - (ea * i0)) ≡ k ) (Euclid.is-equ> e (ge3 lt ge5)) ge5 } where
   ea = Euclid.eqa e 
   eb = Euclid.eqb e
   f = Dividable.factor (GCD.div-j di)
   ge5 : (((eb + ea * f) * suc j0) - (ea * i0)) ≡ ((eb * suc j0) - (ea * suc (suc i)))
   ge5 = begin
       ((eb + ea * f) * suc j0) - (ea * i0) ≡⟨ cong₂ (λ j k → j - k ) (proj1 (ge01 j0 i i0 eb ea (GCD-sym di) )) (proj2 (ge01 j0 i i0 eb ea (GCD-sym di) )) ⟩
      ( eb * suc j0 + (ea * f )* suc j0) - (ea * suc (suc i) + (ea * f )* suc j0) ≡⟨ minus+xy-zy {_} {(ea * f )* suc j0} {ea * suc (suc i)}   ⟩
       (eb * suc j0) - (ea * suc (suc i)) ∎ where open ≡-Reasoning
   ge4 : ((ea * i0) - ((eb + ea * f) * suc j0)) ≡ ((ea * suc (suc i)) - (eb * suc j0))
   ge4 = begin
        (ea * i0) - ((eb + ea * f) * suc j0) ≡⟨ cong₂ (λ j k → j - k ) (proj2 (ge01 j0 i i0 eb ea (GCD-sym di) )) (proj1 (ge01 j0 i i0 eb ea (GCD-sym di) )) ⟩
        (ea * suc (suc i) + (ea * f )* suc j0) - ( eb * suc j0 + (ea * f )* suc j0)  ≡⟨ minus+xy-zy {ea * suc (suc i)} {(ea * f )* suc j0} { eb * suc j0}   ⟩
        (ea * suc (suc i)) - (eb * suc j0) ∎ where open ≡-Reasoning
   ge24 : ea * i0 ≡ (eb + ea * f) * suc j0 → ea * suc (suc i) ≡ eb * suc j0
   ge24 eq = begin
       ea * suc (suc i)   ≡⟨ sym ( minus+y-y {_} {(ea * f ) * suc j0 })  ⟩
       (ea * suc (suc i) + (ea * f ) * suc j0 ) - ((ea * f ) * suc j0) ≡⟨  cong (λ k → k - ((ea * f ) * suc j0 )) (sym (proj2 (ge01 j0 i i0 eb ea (GCD-sym di) )))  ⟩
        (ea * i0) - ((ea * f ) * suc j0)  ≡⟨  cong (λ k → k - ((ea * f ) * suc j0 )) eq  ⟩
       ((eb + ea * f) * suc j0) - ((ea * f ) * suc j0) ≡⟨   cong (λ k → k - ((ea * f ) * suc j0 )) ((proj1 (ge01 j0 i i0 eb ea (GCD-sym di)))) ⟩
       ( eb * suc j0 + (ea * f ) * suc j0 ) - ((ea * f ) * suc j0) ≡⟨  minus+y-y {_} {(ea * f ) * suc j0 }  ⟩
       eb * suc j0   ∎ where open ≡-Reasoning
gcd-euclid1 (suc zero) i0 (suc j) j0 di =
     gcd-euclid1 zero i0 j j0  (gcd-next di)
gcd-euclid1 (suc (suc i)) i0 (suc j) j0  di = 
     gcd-euclid1 (suc i) i0 j j0 (gcd-next di)

ge12 : (p x : ℕ) → 0 < x → 1 < p → ((i : ℕ ) → i < p → 0 < i   → gcd p i ≡ 1)  →  ( gcd p x ≡ 1 ) ∨ ( Dividable p x )
ge12 p x 0<x 1<p prime with decD {p} {x} 1<p 
... | yes y = case2 y
... | no nx with <-cmp (gcd p x ) 1
... | tri< a ¬b ¬c = ⊥-elim ( nat-≤> a (s≤s (gcd>0 p x (<-trans a<sa 1<p)  0<x) ) )
... | tri≈ ¬a b ¬c = case1 b
... | tri> ¬a ¬b c = ⊥-elim ( nat-≡< (sym (prime (gcd p x) ge13 (<to≤ c) )) ge18 ) where
        --  1 < gcd p x 
        ge13 :  gcd p x < p -- gcd p x ≡ p → ¬ nx
        ge13 with <-cmp (gcd p x ) p
        ... | tri< a ¬b ¬c = a
        ... | tri≈ ¬a b ¬c = ⊥-elim ( nx (subst (λ k → Dividable k x) b (proj2 (gcd-dividable p x ))))
        ... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> (gcd-≤ (<-trans a<sa 1<p) 0<x) c )
        ge19 : Dividable (gcd p x) p
        ge19 = proj1 (gcd-dividable p x )
        ge18 :   1 < gcd p  (gcd p x) --  Dividable p  (gcd p x) → gcd p  (gcd p x) ≡  (gcd p x) > 1
        ge18 = subst (λ k → 1 < k ) (sym (div→gcd {p} {gcd p x} c ge19 )) c

gcd-euclid : ( p a b : ℕ )  → 1 < p  → 0 < a → 0 < b → ((i : ℕ ) → i < p → 0 < i   → gcd p i ≡ 1)  →  Dividable p (a * b)  → Dividable p a ∨ Dividable p b
gcd-euclid p a b 1<p 0<a 0<b prime div-ab with decD {p} {a} 1<p
... | yes y = case1 y
... | no np = case2 ge16  where
    f = Dividable.factor div-ab
    ge10 : gcd p a ≡ 1
    ge10 with ge12 p a 0<a 1<p prime
    ... | case1 x = x
    ... | case2 x = ⊥-elim ( np x )
    ge11 : Euclid p a (gcd p a)
    ge11 = gcd-euclid1 p p a a GCDi
    ea = Euclid.eqa ge11
    eb = Euclid.eqb ge11
    ge18 : (f * eb) * p ≡  b * (a * eb )
    ge18 = begin
         (f * eb) * p  ≡⟨ *-assoc (f) (eb) p ⟩
         f * (eb * p)  ≡⟨ cong (λ k →  f  * k)  (*-comm _ p) ⟩
          f * (p * eb )  ≡⟨ sym (*-assoc  (f) p (eb) ) ⟩
         (f * p ) * eb   ≡⟨ cong (λ k → k * eb ) (+-comm 0  (f * p )) ⟩
         (f * p + 0) * eb   ≡⟨ cong (λ k → k *  eb) (((Dividable.is-factor div-ab))) ⟩
         (a * b) * eb   ≡⟨ cong (λ k → k *  eb) (*-comm a b) ⟩
         (b * a) * eb   ≡⟨ *-assoc b a (eb ) ⟩
         b * (a * eb ) ∎ where open ≡-Reasoning
    ge19 : ( ea * p ) ≡ (  eb * a ) → ((b * ea) - (f * eb)) * p + 0 ≡ b
    ge19 eq = ⊥-elim ( nat-≡< (Euclid.is-equ= ge11 eq) (subst (λ k → 0 < k ) (sym ge10) a<sa ) )
    ge14 : ( ea * p ) > (  eb * a ) → ((b * ea) - (f * eb)) * p + 0 ≡ b
    ge14 lt = begin
         (((b * ea) - (f * eb)) * p) + 0 ≡⟨ +-comm _ 0 ⟩
         ((b * ea) - ((f * eb)) * p) ≡⟨ distr-minus-* {_} {f * eb} {p} ⟩
         ((b * ea) * p) - (((f * eb) * p))  ≡⟨ cong (λ k → ((b * ea) * p)  - k  ) ge18 ⟩
         ((b * ea) * p) - (b * (a * eb ))  ≡⟨ cong (λ k → k - (b * (a * eb)) ) (*-assoc b _ p) ⟩
         (b * (ea * p)) - (b * (a * eb ))  ≡⟨ sym ( distr-minus-*' {b} {ea * p} {a * eb} )  ⟩
         b * (( ea * p) - (a * eb) )  ≡⟨ cong (λ k → b * ( ( ea * p) - k)) (*-comm a (eb)) ⟩
         (b * ( (ea * p)) -  (eb * a) )  ≡⟨ cong (b *_) (Euclid.is-equ< ge11 lt )⟩
         b * gcd p a  ≡⟨ cong (b *_) ge10 ⟩
         b * 1  ≡⟨ m*1=m ⟩
         b ∎ where open ≡-Reasoning
    ge15 : ( ea * p ) < (  eb * a ) →  ((f * eb) - (b * ea ) ) * p + 0 ≡ b
    ge15 lt = begin
         ((f * eb) - (b * ea)  ) * p + 0  ≡⟨  +-comm _ 0 ⟩
         ((f * eb) - (b * ea)  ) * p   ≡⟨ distr-minus-* {_} {b * ea} {p} ⟩
         ((f * eb) * p) - ((b * ea) * p)    ≡⟨ cong (λ k → k - ((b * ea) * p)   ) ge18 ⟩
         (b * (a * eb )) - ((b * ea) * p )   ≡⟨   cong (λ k → (b * (a * eb)) - k ) (*-assoc b _ p) ⟩
         (b * (a * eb )) - (b * (ea * p) )   ≡⟨  sym ( distr-minus-*' {b} {a * eb} {ea * p}  ) ⟩
         b * ( (a * eb) - (ea * p) )  ≡⟨  cong (λ k → b * ( k - ( ea * p) )) (*-comm a (eb))  ⟩
         b * ( (eb * a) - (ea * p)  )  ≡⟨ cong (b *_) (Euclid.is-equ> ge11 lt) ⟩
         b * gcd p a  ≡⟨ cong (b *_) ge10 ⟩
         b * 1  ≡⟨ m*1=m ⟩
         b ∎ where open ≡-Reasoning
    ge17 : (x  y : ℕ ) → x ≡ y → x ≤ y
    ge17 x x refl = refl-≤
    ge16 : Dividable p b
    ge16 with <-cmp ( ea * p ) (  eb * a )
    ... | tri< a ¬b ¬c = record { factor = (f * eb)  - (b * ea) ; is-factor = ge15 a }
    ... | tri≈ ¬a eq ¬c = record { factor = (b * ea) - ( f * eb) ; is-factor = ge19 eq }
    ... | tri> ¬a ¬b c = record { factor = (b * ea) -  (f * eb) ; is-factor = ge14 c }  



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
      gcd (m * n + 1 + n) n ≡⟨ gcd+j (m * n + 1) n ⟩
      gcd (m * n + 1) n ≡⟨ gcdmul+1 m n ⟩
      1 ∎ where open ≡-Reasoning

m*n=m→n : {m n : ℕ } → 0 < m → m * n ≡ m * 1 → n ≡ 1
m*n=m→n {suc m} {n} (s≤s lt) eq = *-cancelˡ-≡ m eq 

gcd-is-gratest :  { i j  k : ℕ } → i > 0 → j > 0 → k > 1 → Dividable k i → Dividable k j → k ≤ gcd i j 
gcd-is-gratest {i} {j} {k} i>0 j>0 k>1 ki kj = div→k≤m k>1 (gcd>0 i j i>0 j>0 ) gcd001 where
    gcd001 :  Dividable k ( gcd i  j ) 
    gcd001 = gcd-div _ _ _ k>1 ki kj

gcd-div-1 : {i j : ℕ } → i > 0 → j > 0  → gcd (Dividable.factor (proj1 (gcd-dividable i j))) (Dividable.factor (proj2 (gcd-dividable i j))) ≡ 1
gcd-div-1 {suc i} {suc j} i>0 j>0 = cop where
   d : ℕ
   d = gcd (suc i) (suc j)
   d>0 : gcd (suc i) (suc j) > 0
   d>0 = gcd>0 (suc i) (suc j)  (s≤s z≤n ) (s≤s z≤n )
   id  : Dividable d (suc i)
   id  = proj1 (gcd-dividable (suc i) (suc j))
   jd  : Dividable d (suc j)
   jd  = proj2 (gcd-dividable (suc i) (suc j))
   cop : gcd (Dividable.factor id) (Dividable.factor jd) ≡ 1
   cop with (gcd (Dividable.factor id) (Dividable.factor jd)) | inspect (gcd (Dividable.factor id)) (Dividable.factor jd)
   ... | zero | record { eq  = eq1 } = ⊥-elim ( nat-≡< (sym eq1) (gcd>0 (Dividable.factor id) (Dividable.factor jd)
       (0<factor d>0 (s≤s z≤n) id) (0<factor d>0 (s≤s z≤n) jd) ))
   ... | suc zero | record { eq  = eq1 } = refl
   ... | suc (suc t) | record { eq  = eq1 } = ⊥-elim ( nat-≤> (gcd-is-gratest {suc i} {(suc j)} (s≤s z≤n) (s≤s z≤n) co1 d1id d1jd ) gcd<d1 ) where
        -- gcd-is-gratest :  { i j  k : ℕ } → i > 0 → j > 0 → k > 1 → Dividable k i → Dividable k j → k ≤ gcd i j
        d1 : ℕ
        d1 = gcd (Dividable.factor id) (Dividable.factor jd)
        d1>1 : gcd (Dividable.factor id) (Dividable.factor jd) > 1
        d1>1 = subst (λ k → 1 < k ) (sym eq1) (s≤s (s≤s z≤n))
        mul1 :  {x : ℕ} → 1 * x ≡ x
        mul1 {zero} = refl
        mul1 {suc x} = begin
              1 * suc x  ≡⟨ cong suc (+-comm x _ ) ⟩
              suc x ∎   where open ≡-Reasoning
        co1  : gcd (suc i) (suc j) * d1 > 1
        co1  = begin
              2 ≤⟨ d1>1 ⟩
              d1  ≡⟨ sym mul1 ⟩
              1 * d1  ≤⟨ *≤ {1} {gcd (suc i) (suc j) } {d1} d>0 ⟩
              gcd (suc i) (suc j) * d1 ∎   where open ≤-Reasoning
        gcdd1 = gcd-dividable (Dividable.factor id) (Dividable.factor jd)
        gcdf1 = Dividable.factor (proj1 gcdd1)
        gcdf2 = Dividable.factor (proj2 gcdd1)
        d1id :  Dividable (gcd (suc i) (suc j) * d1) (suc i)
        d1id = record { factor = gcdf1 ; is-factor = begin
              gcdf1 * (d * d1) + 0 ≡⟨ +-comm _ 0 ⟩
              gcdf1 * (d * d1) ≡⟨ cong (λ k1 → gcdf1 * k1) (*-comm d d1) ⟩
              gcdf1 * (d1 * d) ≡⟨ sym (*-assoc gcdf1 d1 d) ⟩
              gcdf1 * d1 * d ≡⟨ sym ( +-comm _ 0) ⟩
              (gcdf1 * d1) * d + 0 ≡⟨ cong (λ k1 → k1 * d + 0 ) (sym (+-comm (gcdf1 * d1) 0)) ⟩
              (gcdf1 * d1 + 0  ) * d + 0 ≡⟨ cong (λ k1 → k1 * d + 0 ) ( Dividable.is-factor (proj1 gcdd1) ) ⟩
              Dividable.factor id * d + 0 ≡⟨ Dividable.is-factor id ⟩
              suc i ∎ }  where open ≡-Reasoning
        d1jd :  Dividable (gcd (suc i) (suc j) * d1) (suc j)
        d1jd = record { factor = gcdf2 ; is-factor = begin
              gcdf2 * (d * d1) + 0 ≡⟨ +-comm _ 0 ⟩
              gcdf2 * (d * d1) ≡⟨ cong (λ k1 → gcdf2 * k1) (*-comm d d1) ⟩
              gcdf2 * (d1 * d) ≡⟨ sym (*-assoc gcdf2 d1 d) ⟩
              gcdf2 * d1 * d ≡⟨ sym ( +-comm _ 0) ⟩
              (gcdf2 * d1) * d + 0 ≡⟨ cong (λ k1 → k1 * d + 0 ) (sym (+-comm (gcdf2 * d1) 0)) ⟩
              (gcdf2 * d1 + 0  ) * d + 0 ≡⟨ cong (λ k1 → k1 * d + 0 ) ( Dividable.is-factor (proj2 gcdd1) ) ⟩
              Dividable.factor jd * d + 0 ≡⟨ Dividable.is-factor jd ⟩
              (suc j) ∎ }  where open ≡-Reasoning
        mul2 : {g d1 : ℕ } → g > 0 → d1 > 1 → g < g * d1
        mul2 {suc g} {suc zero} g>0 (s≤s ())
        mul2 {suc g} {suc (suc d2)} g>0 d1>1 = begin
              suc (suc g) ≡⟨ cong suc (+-comm 0 _ ) ⟩
              suc (suc g + 0) ≤⟨ s≤s (≤-plus-0  z≤n) ⟩
              suc (suc g + (g + d2 * suc g)) ≡⟨ cong suc (sym (+-assoc  1 g _) ) ⟩
              suc ((1 + g) + (g + d2 * suc g)) ≡⟨  cong (λ k → suc (k + (g + d2 * suc g) )) (+-comm 1 g) ⟩
              suc ((g + 1) + (g + d2 * suc g)) ≡⟨ cong suc (+-assoc g 1 _ )  ⟩
              suc (g + (1 + (g + d2 * suc g))) ≡⟨⟩
              suc (g + suc (g + d2 * suc g)) ≡⟨⟩
              suc (suc d2) * suc g  ≡⟨ *-comm (suc (suc d2)) _ ⟩
              suc g * suc (suc d2) ∎   where open ≤-Reasoning
        gcd<d1 : gcd (suc i) (suc j) < gcd (suc i ) (suc j) * d1
        gcd<d1 = mul2 (gcd>0 (suc i) (suc j) (s≤s z≤n) (s≤s z≤n) ) d1>1


