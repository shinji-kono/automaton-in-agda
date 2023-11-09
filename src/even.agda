{-# OPTIONS --cubical-compatible --safe #-}

module even where

open import Data.Nat 
open import Data.Nat.Properties
open import Data.Empty
open import Data.Unit using (⊤ ; tt)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Definitions
open import nat
open import logic

even : (n : ℕ ) → Set
even zero = ⊤
even (suc zero) = ⊥
even (suc (suc n)) = even n

even? : (n : ℕ ) → Dec ( even n )
even? zero = yes tt
even? (suc zero) = no (λ ())
even? (suc (suc n)) = even? n

n+even : {n m : ℕ } → even n → even m  → even ( n + m )
n+even {zero} {zero} tt tt = tt
n+even {zero} {suc m} tt em = em
n+even {suc (suc n)} {m} en em = n+even {n} {m} en em

n*even : {m n : ℕ } → even n → even ( m * n )
n*even {zero} {n} en = tt
n*even {suc m} {n} en = n+even {n} {m * n} en (n*even {m} {n} en) 

even*n : {n m : ℕ } → even n → even ( n * m )
even*n {n} {m} en = subst even (*-comm m n) (n*even {m} {n} en)


record Even (i : ℕ) : Set where
  field
     j : ℕ
     is-twice : i ≡ 2 * j

e2 : (i : ℕ) → even i → Even i
e2 zero en = record { j = 0 ; is-twice = refl }
e2 (suc (suc i)) en = record { j = suc (Even.j (e2 i en )) ; is-twice = e21 } where
   e21 : suc (suc i) ≡ 2 * suc (Even.j (e2 i en))
   e21 = begin
    suc (suc i)  ≡⟨ cong (λ k → suc (suc k)) (Even.is-twice (e2 i en))  ⟩
    suc (suc (2 * Even.j (e2 i en)))  ≡⟨ sym (*-distribˡ-+ 2 1 _) ⟩
    2 * suc (Even.j (e2 i en))      ∎ where open ≡-Reasoning

record Odd (i : ℕ) : Set where
  field
     j : ℕ
     is-twice : i ≡ suc (2 * j )

odd2 : (i : ℕ) → ¬ even i → even (suc i) 
odd2 zero ne = ⊥-elim ( ne tt )
odd2 (suc zero) ne = tt
odd2 (suc (suc i)) ne = odd2 i ne 

odd3 : (i : ℕ) → ¬ even i →  Odd i
odd3 zero ne = ⊥-elim ( ne tt )
odd3 (suc zero) ne = record { j = 0 ; is-twice = refl }
odd3 (suc (suc i))  ne = record { j = Even.j (e2 (suc i) (odd2 i ne)) ; is-twice = odd31 } where
  odd31 : suc (suc i) ≡ suc (2 * Even.j (e2 (suc i) (odd2 i ne)))
  odd31 = begin
    suc (suc i) ≡⟨  cong suc (Even.is-twice (e2 (suc i) (odd2 i ne)))  ⟩
    suc (2 * (Even.j (e2 (suc i) (odd2 i ne))))      ∎ where open ≡-Reasoning

odd4 : (i : ℕ) → even i → ¬ even ( suc i )
odd4 (suc (suc i)) en en1 = odd4 i en en1 

