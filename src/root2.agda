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
        df * df * p + 0  ≡⟨ *-cancelʳ-≡ _ _ {p0} ( begin 
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

Rational* : (r s : Rational) → Rational
Rational* r s = record  { i = {!!} ; j = {!!} ; coprime = {!!} }

_r=_ : Rational → ℕ → Set
r r= n  = (Rational.i r ≡ n) ∧ (Rational.j r ≡ 1)

root-prime-irrational1 : ( p : ℕ ) → Prime p → ¬ ( ( r  : Rational ) → Rational* r r r= p )
root-prime-irrational1 = {!!}
