module root2 where

open import Data.Nat 
open import Data.Nat.Properties
open import Data.Empty
open import Data.Unit using (⊤ ; tt)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Definitions

open import gcd
open import even
open import nat
open import logic

record Rational : Set where
  field
    i j : ℕ
    coprime : gcd i j ≡ 1

open _∧_

open import prime

-- equlid : ( n m k : ℕ ) → 1 < k → 1 < n → Prime k → Dividable k ( n * m ) → Dividable k n ∨ Dividable k m
-- equlid = {!!}

divdable^2 : ( n k : ℕ ) → 1 < k → 1 < n → Prime k → Dividable k ( n * n ) → Dividable k n
divdable^2 zero zero () 1<n pk dn2
divdable^2 (suc n) (suc k) 1<k 1<n pk dn2 with decD {suc k} {suc n} 1<k
... | yes y = y
... | no non with gcd-euclid (suc k) (suc n) (suc n) 1<k (<-trans a<sa 1<n) (<-trans a<sa 1<n) (Prime.isPrime pk) dn2 
... | case1 dn = dn
... | case2 dm = dm

p2 : Prime 2
p2 = record { p>1 = a<sa ; isPrime = p22 } where
   p22 : (j : ℕ) → j < 2 → 0 < j → gcd 2 j ≡ 1
   p22 1 (s≤s (s≤s z≤n)) (s≤s 0<j) = refl

-- gcd-div : ( i j k : ℕ ) → (if : Dividable k i) (jf : Dividable k j )
--    → Dividable k ( gcd i  j )

root2-irrational : ( n m : ℕ ) → n > 1 → m > 1  →  2 * n * n ≡ m * m  → ¬ (gcd n m ≡ 1)
root2-irrational n m n>1 m>1 2nm = rot13 ( gcd-div n m 2 (s≤s (s≤s z≤n)) dn dm ) where 
    rot13 : {m : ℕ } → Dividable 2 m →  m ≡ 1 → ⊥
    rot13 d refl with Dividable.factor d | Dividable.is-factor d
    ... | zero | ()
    ... | suc n | ()
    dm : Dividable 2 m
    dm = divdable^2 m 2 a<sa m>1 p2 record { factor = n * n ; is-factor = begin
       (n * n) * 2 + 0 ≡⟨  +-comm _ 0 ⟩
       (n * n) * 2  ≡⟨ *-comm (n * n) 2 ⟩
       2 * (n * n)  ≡⟨ sym (*-assoc 2 n n)  ⟩
       (2 * n) * n ≡⟨ 2nm  ⟩
       m * m ∎ }  where open ≡-Reasoning
     -- 2 * n * n = 2m' 2m'
     --  n * n = m' 2m'
    df = Dividable.factor dm
    dn : Dividable 2 n
    dn = divdable^2 n 2 a<sa n>1 p2 record { factor = df * df  ; is-factor = begin
        df * df * 2 + 0  ≡⟨ *-cancelʳ-≡ _ _ {1} ( begin 
          (df * df * 2 + 0) * 2 ≡⟨  cong (λ k → k * 2)  (+-comm (df * df * 2) 0)  ⟩
          ((df * df) * 2) * 2 ≡⟨ cong (λ k → k * 2) (*-assoc df df 2 ) ⟩
          (df * (df * 2)) * 2 ≡⟨ cong (λ k → (df * k ) * 2) (*-comm df 2)  ⟩
          (df * (2 * df)) * 2 ≡⟨ sym ( cong (λ k → k * 2) (*-assoc df 2 df ) ) ⟩
          ((df * 2) * df) * 2 ≡⟨ *-assoc (df * 2) df 2  ⟩
          (df * 2) * (df * 2) ≡⟨ cong₂ (λ j k → j * k ) (+-comm 0 (df * 2)) (+-comm 0 _) ⟩
          (df * 2 + 0) * (df * 2 + 0)   ≡⟨ cong₂ (λ j k → j * k) (Dividable.is-factor dm ) (Dividable.is-factor dm )⟩
          m * m   ≡⟨ sym 2nm ⟩
          2 * n * n   ≡⟨ cong (λ k → k * n) (*-comm 2 n) ⟩
          n * 2 * n   ≡⟨ *-assoc n 2 n ⟩
          n * (2 * n)   ≡⟨ cong (λ k → n * k) (*-comm 2 n) ⟩
          n * (n * 2)   ≡⟨ sym (*-assoc n n 2) ⟩
          n * n * 2 ∎  ) ⟩
       n * n ∎ }  where open ≡-Reasoning


