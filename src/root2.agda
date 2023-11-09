{-# OPTIONS --cubical-compatible --safe #-}

module root2 where

open import Data.Nat 
open import Data.Nat.Properties
open import Data.Empty
open import Data.Unit using (⊤ ; tt)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Definitions

import gcd as GCD
open import even
open import nat
open import logic

record Rational : Set where
  field
    i j : ℕ
    0<j : j > 0
    coprime : GCD.gcd i j ≡ 1

-- record Dividable (n m : ℕ ) : Set where
--    field 
--       factor : ℕ
--       is-factor : factor * n + 0 ≡ m 

gcd : (i j : ℕ) → ℕ
gcd = GCD.gcd

gcd-euclid : ( p a b : ℕ )  → 1 < p  → 0 < a → 0 < b → ((i : ℕ ) → i < p → 0 < i   → gcd p i ≡ 1)
   →  Dividable p (a * b)  → Dividable p a ∨ Dividable p b
gcd-euclid = GCD.gcd-euclid

gcd-div1 : ( i j k : ℕ ) → k > 1 → (if : Dividable k i) (jf : Dividable k j ) 
   → Dividable k ( gcd i  j ) 
gcd-div1 = GCD.gcd-div

open _∧_

open import prime

divdable^2 : ( n k : ℕ ) → 1 < k → 1 < n → Prime k → Dividable k ( n * n ) → Dividable k n
divdable^2 zero zero () 1<n pk dn2
divdable^2 (suc n) (suc k) 1<k 1<n pk dn2 with decD {suc k} {suc n} 1<k
... | yes y = y
... | no non with gcd-euclid (suc k) (suc n) (suc n) 1<k (<-trans a<sa 1<n) (<-trans a<sa 1<n) (Prime.isPrime pk) dn2 
... | case1 dn = dn
... | case2 dm = dm

-- divdable-n*m : { n m k : ℕ } → 1 < k → 1 < n → Prime k → Dividable k ( n * m ) → Dividable k n ∨ Dividable k n
-- divdable-n*m = ?

-- 2^2 : { n k : ℕ } → 1 < n → Dividable 2 ( n * n ) → Dividable 2 n
-- 2^2 = ?

-- p * n * n ≡ m * m means (m/n)^2 = p
-- rational m/n requires m and n is comprime each other which contradicts the condition

root-prime-irrational : ( n m p : ℕ ) → n > 1 → Prime p → m > 1  →  p * n * n ≡ m * m  → ¬ (gcd n m ≡ 1)
root-prime-irrational n m 0 n>1 pn m>1 pnm = ⊥-elim ( nat-≡< refl (<-trans a<sa (Prime.p>1 pn))) 
root-prime-irrational n m (suc p0) n>1 pn m>1 pnm = rot13 ( gcd-div1 n m (suc p0) 1<sp dn dm ) where 
    p = suc p0
    1<sp : 1 < p
    1<sp = Prime.p>1 pn
    rot13 : {m : ℕ } → Dividable (suc p0) m →  m ≡ 1 → ⊥
    rot13 d refl with Dividable.factor d | Dividable.is-factor d
    ... | zero | ()   -- gcd 0 m ≡ 1
    ... | suc n | x = ⊥-elim ( nat-≡< (sym x) rot17 ) where -- x : (suc n * p + 0) ≡ 1 
        rot17 : suc n * (suc p0) + 0 > 1
        rot17 = begin
           2 ≡⟨ refl ⟩
           suc (1 * 1 ) ≤⟨ 1<sp  ⟩
           suc p0  ≡⟨ cong suc (+-comm 0 _) ⟩ 
           suc (p0 + 0) ≤⟨ s≤s (+-monoʳ-≤ p0 z≤n) ⟩ 
           suc (p0 + n * p )  ≡⟨ +-comm 0 _ ⟩
           suc n * p + 0 ∎   where open ≤-Reasoning
    dm : Dividable p m
    dm = divdable^2 m p 1<sp m>1 pn record { factor = n * n ; is-factor = begin
       (n * n) * p + 0 ≡⟨  +-comm _ 0 ⟩
       (n * n) * p  ≡⟨ *-comm (n * n) p ⟩
       p * (n * n)  ≡⟨ sym (*-assoc p n n)  ⟩
       (p * n) * n ≡⟨ pnm ⟩
       m * m ∎ }  where open ≡-Reasoning
     -- p * n * n = 2m' 2m'
     --  n * n = m' 2m'
    df = Dividable.factor dm
    dn : Dividable p n
    dn = divdable^2 n p 1<sp n>1 pn record { factor = df * df  ; is-factor = begin
        df * df * p + 0  ≡⟨ *-cancelʳ-≡ _ _ (suc p0) ( begin 
          (df * df * p + 0) * p ≡⟨  cong (λ k → k * p)  (+-comm (df * df * p) 0)  ⟩
          ((df * df) * p  ) * p ≡⟨ cong (λ k → k * p) (*-assoc df df p ) ⟩
            (df * (df * p)) * p ≡⟨ cong (λ k → (df * k ) * p) (*-comm df p)  ⟩
            (df * (p * df)) * p ≡⟨ sym ( cong (λ k → k * p) (*-assoc df p df ) ) ⟩
            ((df * p) * df) * p ≡⟨ *-assoc (df * p) df p  ⟩
            (df * p) * (df * p) ≡⟨ cong₂ (λ j k → j * k ) (+-comm 0 (df * p)) (+-comm 0 _) ⟩
          (df * p + 0) * (df * p + 0)   ≡⟨ cong₂ (λ j k → j * k) (Dividable.is-factor dm ) (Dividable.is-factor dm )⟩
          m * m   ≡⟨ sym pnm ⟩
          p * n * n     ≡⟨ cong (λ k → k * n) (*-comm p n) ⟩
          n * p * n     ≡⟨ *-assoc n p n ⟩
          n * (p * n)   ≡⟨ cong (λ k → n * k) (*-comm p n) ⟩
          n * (n * p)   ≡⟨ sym (*-assoc n n p) ⟩
          n * n * p ∎  ) ⟩
       n * n ∎ }  where open ≡-Reasoning

mkRational : ( i j : ℕ ) → 0 < j → Rational
mkRational zero j 0<j = record { i = 0 ; j = 1 ; coprime = refl  ; 0<j = s≤s z≤n } 
mkRational (suc i) (suc j) (s≤s 0<j) = record { i = Dividable.factor id ; j = Dividable.factor jd ; coprime = cop ; 0<j = 0<fj } where
   d : ℕ
   d = gcd (suc i) (suc j)
   d>0 : gcd (suc i) (suc j) > 0
   d>0 = GCD.gcd>0 (suc i) (suc j) (s≤s z≤n) (s≤s z≤n )
   id  : Dividable d (suc i)
   id  = proj1 (GCD.gcd-dividable (suc i) (suc j))
   jd  : Dividable d (suc j) 
   jd  = proj2 (GCD.gcd-dividable (suc i) (suc j))
   0<fj : Dividable.factor jd > 0
   0<fj = 0<factor d>0  (s≤s z≤n ) jd
   cop : gcd (Dividable.factor id) (Dividable.factor jd) ≡ 1
   cop = GCD.gcd-div-1 {suc i} {suc j} (s≤s z≤n) (s≤s z≤n )

r1 : {x y : ℕ} → x > 0 → y > 0 → x * y > 0
r1 {x} {y} x>0 y>0 = begin
        1 * 1 ≤⟨ *≤ {1} {x} {1} x>0 ⟩
        x * 1 ≡⟨ *-comm x 1  ⟩
        1 * x ≤⟨ *≤ {1} {y} {x} y>0 ⟩
        y * x ≡⟨ *-comm y x ⟩
        x * y ∎ where open ≤-Reasoning

Rational* : (r s : Rational) → Rational
Rational* r s = mkRational (Rational.i r * Rational.i s) (Rational.j r * Rational.j s) (r1 (Rational.0<j r) (Rational.0<j s) ) 

_r=_ : Rational → ℕ → Set
r r= p  = p * Rational.j r ≡ Rational.i r 

r3 : ( p : ℕ ) → p > 0 → ( r  : Rational ) →  Rational* r r r= p →  p * Rational.j r * Rational.j r ≡ Rational.i r * Rational.i r
r3 p p>0 r rr = r4 where
    i : ℕ
    i = Rational.i r * Rational.i r
    j : ℕ
    j = Rational.j r * Rational.j r
    0<j : 0 < j
    0<j = r1 (Rational.0<j r) (Rational.0<j r)
    d1 = Dividable.factor (proj1 (GCD.gcd-dividable i j)) 
    d2 = Dividable.factor (proj2 (GCD.gcd-dividable i j)) 
    ri=id :  ( i j : ℕ) → (0<i : 0 < i ) → (0<j : 0 < j)  
        →  Rational.i (mkRational i j 0<j) ≡ Dividable.factor (proj1 (GCD.gcd-dividable i j))
    ri=id (suc i₁) (suc j₁) 0<i (s≤s 0<j₁) = refl
    ri=jd :  ( i j : ℕ) → (0<i : 0 < i ) → (0<j : 0 < j)  
        →  Rational.j (mkRational i j 0<j) ≡ Dividable.factor (proj2 (GCD.gcd-dividable i j))
    ri=jd (suc i₁) (suc j₁) 0<i (s≤s 0<j₁) = refl
    r0=id :  ( i j : ℕ) → (0=i : 0 ≡ i ) → (0<j : 0 < j)  
        →  Rational.i (mkRational i j 0<j) ≡ 0
    r0=id  0 j refl 0<j = refl
    r0=jd :  ( i j : ℕ) → (0=i : 0 ≡ i ) → (0<j : 0 < j)  
        →  Rational.j (mkRational i j 0<j) ≡ 1
    r0=jd  0 j refl 0<j = refl
    d : ℕ
    d = gcd i j
    r7 : i > 0 → d > 0
    r7 0<i = GCD.gcd>0 _ _ 0<i 0<j
    r6 :  i > 0 → d2 > 0
    r6 0<i = 0<factor (r7 0<i ) 0<j (proj2 (GCD.gcd-dividable i j)) 
    r8 : 0 < i → d2 * p ≡ d1
    r8 0<i = begin
      d2 * p ≡⟨ *-comm d2 p ⟩
      p * d2  ≡⟨ cong (λ k → p * k ) (sym (ri=jd i j 0<i 0<j ))  ⟩
      p *  Rational.j (mkRational i j  _ ) ≡⟨ rr ⟩
      Rational.i (Rational* r r) ≡⟨ ri=id i j 0<i 0<j ⟩
      d1 ∎ where open ≡-Reasoning
    r4 : p * Rational.j r * Rational.j r ≡ Rational.i r * Rational.i r
    r4 with <-cmp (Rational.i r * Rational.i r) 0
    ... | tri≈ ¬a b ¬c = ⊥-elim (nat-≡< (begin
        0 ≡⟨ sym (r0=id i j (sym b) 0<j ) ⟩
        Rational.i (mkRational (Rational.i r * Rational.i r) (Rational.j r * Rational.j r) _ ) ≡⟨ sym rr ⟩
        p *  Rational.j (mkRational (Rational.i r * Rational.i r) (Rational.j r * Rational.j r) _ ) ≡⟨ cong (λ k → p * k ) (r0=jd i j (sym b) 0<j ) ⟩
        p *  1  ≡⟨ m*1=m  ⟩
        p ∎ ) p>0 ) where open ≡-Reasoning
    ... | tri> ¬a ¬b c = begin
      p * Rational.j r * Rational.j r  ≡⟨ *-cancel-left (r6 c) ( begin
      d2 * ((p * Rational.j r) * Rational.j r)  ≡⟨ sym (*-assoc d2 _ _) ⟩
      (d2 * ( p *  Rational.j r )) * Rational.j r ≡⟨ cong (λ k → k *  Rational.j r) (sym (*-assoc d2 _ _ )) ⟩
      (d2 * p) * Rational.j r * Rational.j r ≡⟨ cong (λ k → k *  Rational.j r * Rational.j r) (r8 c) ⟩
      d1 * Rational.j r * Rational.j r  ≡⟨ *-cancel-left (r7 c) ( begin 
      d * ((d1 * Rational.j r) * Rational.j r)  ≡⟨ cong (λ k → d * k ) (*-assoc d1 _ _ )⟩
      d * (d1 * (Rational.j r * Rational.j r))  ≡⟨ sym (*-assoc d _ _) ⟩
      (d * d1) * (Rational.j r * Rational.j r)  ≡⟨ cong (λ k → k * j) (*-comm d _ ) ⟩
      (d1 * d) * j  ≡⟨  cong (λ k → k * j) (+-comm 0 (d1 * d)  ) ⟩
      (d1 * d + 0) * j  ≡⟨ cong (λ k → k * j ) (Dividable.is-factor  (proj1 (GCD.gcd-dividable i j)) ) ⟩
      i * j ≡⟨ *-comm i j ⟩
      j * i ≡⟨ cong (λ k → k * i ) (sym (Dividable.is-factor (proj2 (GCD.gcd-dividable i j))) ) ⟩
      (d2 * GCD.gcd i j + 0) * i ≡⟨  cong (λ k → k * i ) (+-comm (d2 * d )  0) ⟩
      (d2 * d) * i ≡⟨ cong (λ k → k * i ) (*-comm d2 _ ) ⟩
      (d * d2) * i ≡⟨ *-assoc d _ _ ⟩
      d * (d2 * (Rational.i r * Rational.i r)) ∎ )  ⟩
      d2 * (Rational.i r * Rational.i r) ∎ ) ⟩
      Rational.i r * Rational.i r  ∎ where open ≡-Reasoning

-- data _≤_ : (i j : ℕ) → Set where
--    z≤n : {n : ℕ} → zero ≤ n
--    s≤s : {i j : ℕ} → i ≤ j → (suc i) ≤ (suc j)

*<-2 : {x y z : ℕ} → z > 0  → x < y → z * x < z * y   
*<-2 {zero} {suc y} {suc z} (s≤s z>0) x<y = begin
   suc (z * zero) ≡⟨ cong suc (*-comm z _) ⟩ 
   suc (zero * z) ≡⟨ refl ⟩ 
   suc zero ≤⟨ s≤s z≤n ⟩ 
   suc (y + z * suc y) ∎ where open ≤-Reasoning
*<-2 {x} {y} {suc zero} (s≤s z>0) x<y = begin
   suc (x + zero) ≡⟨ cong suc (+-comm x _) ⟩
   suc x  ≤⟨ x<y ⟩
   y  ≡⟨ +-comm zero _ ⟩
   y + zero  ∎ where open ≤-Reasoning
*<-2 {x} {y} {suc (suc z)} (s≤s z>0) x<y = begin
   suc (x + (x + z * x))  <⟨ +-mono-≤-< x<y (*<-2 {x} {y} {suc z} (s≤s z≤n) x<y) ⟩
   y + (y + z * y)  ∎ where open ≤-Reasoning

r15 : {p : ℕ} → p > 1 → p < p * p
r15 {p} p>1 = subst (λ k → k < p * p ) m*1=m (*<-2 (<-trans a<sa p>1) p>1 )

root-prime-irrational1 : ( p : ℕ ) → Prime p → ( r  : Rational ) → ¬ ( Rational* r r r= p )
root-prime-irrational1 p pr r div  with <-cmp (Rational.j r) 1
... | tri> ¬a ¬b c with <-cmp (Rational.i r) 1
... | tri> ¬a₁ ¬b₁ c₁ = root-prime-irrational (Rational.j r) (Rational.i r) p c pr c₁ (r3 p (<-trans a<sa (Prime.p>1 pr ) ) r div)
    (trans (GCD.gcdsym {Rational.j r} {_} ) (Rational.coprime r) )
... | tri< a ¬b₁ ¬c = ⊥-elim ( nat-≡< (sym r05) r08) where
     i = Rational.i r
     j = Rational.j r
     r00 : p * j * j ≡ i * i
     r00 = r3 p (<-trans a<sa (Prime.p>1 pr )) r div
     r06 : i ≡ 0
     r06 with <-cmp i 0
     ... | tri≈ ¬a b ¬c = b
     ... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> c a )
     r05 : p * j * j ≡ 0 
     r05 with r06
     ... | refl = r00
     r09 : p * j  > 0
     r09 = begin
        suc zero ≤⟨ <-trans a<sa (Prime.p>1 pr)  ⟩
        p ≡⟨ sym m*1=m ⟩
        p * 1 <⟨ *<-2 (<-trans a<sa (Prime.p>1 pr)) c ⟩
        p * j  ∎ where open ≤-Reasoning
     r08 : p * j * j > 0
     r08 = begin
        suc zero ≤⟨ r09  ⟩
        p * j ≡⟨ sym m*1=m ⟩
        (p * j) * 1 <⟨ *<-2 r09 c ⟩
        (p * j) * j ∎ where open ≤-Reasoning
... | tri≈ ¬a₁ b ¬c = ⊥-elim ( nat-≡< (sym r07) r09) where
     i = Rational.i r
     j = Rational.j r
     r00 : p * j * j ≡ i * i
     r00 = r3 p (<-trans a<sa (Prime.p>1 pr )) r div
     r07 : p * j * j ≡ 1  
     r07 = begin
        p * j * j ≡⟨ r00 ⟩
        i * i  ≡⟨ cong (λ k → k * k) b ⟩
        1 * 1 ≡⟨⟩
        1 ∎ where open ≡-Reasoning
     r19 : 1 < p * j  
     r19 = begin 
        suc 1 ≤⟨ Prime.p>1 pr ⟩
        p ≡⟨ sym m*1=m ⟩
        p * 1 <⟨  *<-2 (<-trans a<sa (Prime.p>1 pr)) c ⟩
        p * j ∎ where open ≤-Reasoning
     r09 : 1 < p * j * j 
     r09 = begin 
        suc 1 ≤⟨ r19  ⟩
        p * j ≡⟨ sym  m*1=m ⟩
        p * j * 1 <⟨  *<-2  (<-trans a<sa r19 )  c ⟩
        (p * j) * j ∎ where open ≤-Reasoning
root-prime-irrational1 p pr r div | tri< a ¬b ¬c = ⊥-elim (nat-≤> (Rational.0<j r) a )
root-prime-irrational1 p pr r div | tri≈ ¬a b ¬c = ⊥-elim (nat-≡< r04 (r03 r01)) where
     i = Rational.i r
     j = Rational.j r
     p>0 : p > 0
     p>0 = <-trans a<sa (Prime.p>1 pr)
     r00 : p * j * j ≡ i * i
     r00 = r3 p p>0 r div
     r01 : p ≡ i * i
     r01 = begin
       p  ≡⟨ sym m*1=m  ⟩
       p * 1  ≡⟨ sym m*1=m ⟩
       p * 1 * 1   ≡⟨ cong (λ k → p * k * k ) (sym b) ⟩
       p * j * j   ≡⟨ r00 ⟩
       i * i  ∎ where open ≡-Reasoning
     r03 : p ≡ i * i → i > 1
     r03 eq with <-cmp i 1
     ... | tri< a ¬b ¬c = ⊥-elim ( nat-≡< (sym r11) p>0 ) where
          r10 : i ≡ 0
          r10 with <-cmp i 0
          ... | tri≈ ¬a b ¬c = b
          ... | tri> ¬a ¬b c = ⊥-elim (nat-≤> c a )
          r11 : p ≡ 0
          r11 = begin
             p   ≡⟨ r01 ⟩
             i * i   ≡⟨ cong (λ k → k * k ) r10 ⟩
             0 * 0   ≡⟨⟩
             0  ∎ where open ≡-Reasoning
     ... | tri≈ ¬a refl ¬c = ⊥-elim (  nat-≡< (sym r01 ) (Prime.p>1 pr)) 
     ... | tri> ¬a ¬b c = c
     r02 : p ≡ i * i → gcd p i ≡ i 
     r02 eq = GCD.div→gcd (r03 r01) record { factor = i ; is-factor = trans  (+-comm _ 0 ) (sym r01) }
     r14 : i < p 
     r14 with <-cmp i p
     ... | tri< a ¬b ¬c = a
     ... | tri≈ ¬a b ¬c = ⊥-elim ( nat-≡< r01 (begin
             suc p ≤⟨ r15 (Prime.p>1 pr) ⟩
             p * p  ≡⟨ cong (λ k → k * k ) (sym b) ⟩
             i * i ∎ )) where open ≤-Reasoning
     ... | tri> ¬a ¬b c = ⊥-elim (nat-≡< r01 (<-trans c (r15 (r03 r01 )))) 
     r04 :  1 ≡ i
     r04 = begin
        1 ≡⟨ sym (Prime.isPrime pr _ r14 (<-trans a<sa (r03 r01 ))) ⟩
        gcd p i   ≡⟨ r02 r01 ⟩
        i ∎ where open ≡-Reasoning
