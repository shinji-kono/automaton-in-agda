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

record Rational : Set where
  field
    i j : ℕ
    coprime : gcd i j ≡ 1

even→gcd=2 : {n : ℕ} → even n → n > 0 → gcd n 2 ≡ 2
even→gcd=2 {suc (suc zero)} en (s≤s z≤n) = refl
even→gcd=2 {suc (suc (suc (suc n)))} en (s≤s z≤n) = begin
       gcd (suc (suc (suc (suc n)))) 2 ≡⟨⟩
       gcd (suc (suc n)) 2 ≡⟨ even→gcd=2 {suc (suc n)} en (s≤s z≤n) ⟩
       2 ∎ where open ≡-Reasoning

even^2 : {n : ℕ} → even ( n * n ) → even n
even^2 {n} en with even? n
... | yes y = y
... | no ne = ⊥-elim ( odd4 ((2 * m) + 2 * m * suc (2 * m)) (n+even {2 * m} {2 * m * suc (2 * m)} ee3 ee4) (subst (λ k → even k) ee2 en )) where
    m : ℕ
    m = Odd.j ( odd3 n ne )
    ee3 : even (2 * m)
    ee3 = subst (λ k → even k ) (*-comm m 2) (n*even {m} {2} tt )
    ee4 : even ((2 * m) * suc (2 * m))
    ee4 = even*n {(2 * m)} {suc (2 * m)} (even*n {2} {m} tt )
    ee2 : n * n ≡ suc (2 * m) + ((2 * m) * (suc (2 * m) ))
    ee2 = begin n * n ≡⟨ cong ( λ k → k * k) (Odd.is-twice (odd3 n ne)) ⟩
       suc (2 * m) * suc (2 * m) ≡⟨ *-distribʳ-+ (suc (2 * m)) 1 ((2 * m) ) ⟩
        (1 * suc (2 * m)) + 2 * m * suc (2 * m) ≡⟨ cong (λ k → k + 2 * m * suc (2 * m)) (begin
        suc m + 1 * m + 0 * (suc m + 1 * m ) ≡⟨ +-comm (suc m + 1 * m) 0 ⟩
        suc m + 1 * m  ≡⟨⟩
        suc (2 * m)
        ∎) ⟩ suc (2 * m)  + 2 * m * suc (2 * m) ∎ where open ≡-Reasoning

e3 : {i j : ℕ } → 2 * i ≡ 2 * j →  i ≡ j
e3 {zero} {zero} refl = refl
e3 {suc x} {suc y} eq with <-cmp x y
... | tri< a ¬b ¬c = ⊥-elim ( nat-≡< eq (s≤s (<-trans (<-plus a) (<-plus-0 (s≤s (<-plus a ))))))
... | tri≈ ¬a b ¬c = cong suc b
... | tri> ¬a ¬b c = ⊥-elim ( nat-≡< (sym eq) (s≤s (<-trans (<-plus c) (<-plus-0 (s≤s (<-plus c ))))))

open Factor

root2-irrational : ( n m : ℕ ) → n > 1 → m > 1  →  2 * n * n ≡ m * m  → ¬ (gcd n m ≡ 1)
root2-irrational n m n>1 m>1 2nm = rot13 ( gcd-gt n n m m 2 f2 f2 f2 fm {!!} {!!} {!!} {!!}) where 
    rot13 : {m : ℕ } → Dividable 2 m →  m ≡ 1 → ⊥
    rot13 d refl with Dividable.is-factor d
    ... | t = {!!}
    rot11 : {m : ℕ } → even m → Factor 2 m 
    rot11 {zero} em = record { factor = 0 ; remain = 0 ; is-factor = refl }
    rot11 {suc zero} ()
    rot11 {suc (suc m) } em = record { factor = suc (factor fc ) ; remain = remain fc ; is-factor = isfc } where
       fc : Factor 2 m
       fc = rot11 {m} em
       isfc : suc (factor fc) * 2 + remain fc ≡ suc (suc m)
       isfc = begin
          suc (factor fc) * 2 + remain fc ≡⟨ cong (λ k →  k + remain fc) (*-distribʳ-+ 2 1 (factor fc)) ⟩
          ((1 * 2) +  (factor fc)* 2 ) + remain fc ≡⟨⟩
          ((1 + 1) +  (factor fc)* 2 ) + remain fc ≡⟨ cong (λ k → k + remain fc) (+-assoc 1  1 _ ) ⟩
          (1 + (1 +  (factor fc)* 2 )) + remain fc ≡⟨⟩
          suc (suc ((factor fc * 2) + remain fc )) ≡⟨ cong (λ x → suc (suc x)) (is-factor fc) ⟩
          suc (suc m) ∎ where open ≡-Reasoning
    rot5 : {n : ℕ} → n > 1 → n > 0
    rot5 {n} lt = <-trans a<sa lt 
    rot1 : even ( m * m )
    rot1 = subst (λ k → even k ) rot4 (n*even {n * n} {2} tt ) where
       rot4 : (n * n) * 2 ≡ m * m  
       rot4 = begin
          (n * n) * 2     ≡⟨ *-comm (n * n) 2 ⟩
          2 * ( n * n )   ≡⟨ sym (*-assoc 2 n n) ⟩
          2 *  n * n      ≡⟨ 2nm ⟩
          m * m           ∎ where open ≡-Reasoning
    E : Even m
    E = e2 m ( even^2 {m} ( rot1 ))
    rot2 : 2 * n * n ≡ 2 * Even.j E * m
    rot2 = subst (λ k → 2 * n * n ≡ k * m ) (Even.is-twice E) 2nm
    rot3 : n * n ≡ Even.j E * m
    rot3 = e3 ( begin
          2 * (n * n)   ≡⟨ sym (*-assoc 2 n _) ⟩
          2 *  n * n    ≡⟨ rot2 ⟩
          2 * Even.j E * m ≡⟨  *-assoc 2 (Even.j E)  m  ⟩
          2 * (Even.j E * m)  ∎ ) where open ≡-Reasoning
    rot7 : even n  
    rot7 =  even^2 {n} (subst (λ k → even k) (sym rot3) ((n*even {Even.j E} {m} ( even^2 {m} ( rot1 )))))
    f2 : Factor 2 n
    f2 = rot11 rot7
    fm : Factor 2 m
    fm = record { factor = Even.j E ; remain = 0 ; is-factor = {!!} }

