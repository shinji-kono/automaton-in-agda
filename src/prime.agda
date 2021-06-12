module prime where

open import Data.Nat 
open import Data.Nat.Properties
open import Data.Empty
open import Data.Unit using (⊤ ; tt)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Definitions

open import gcd
open import nat

record Prime (i : ℕ ) : Set where
   field
      isPrime : ( j : ℕ ) → j < i → gcd i j ≡ 1

open ≡-Reasoning

record NonPrime ( n : ℕ ) : Set where
   field
      factor : ℕ
      prime : Prime factor
      dividable : Dividable factor n

isPrime : ( n : ℕ ) → Dec ( Prime n )
isPrime = {!!}

nonPrime : ( n : ℕ ) → ¬ Prime n → NonPrime n
nonPrime n np = np1 n (λ j n≤j j<n → ⊥-elim (nat-≤>  n≤j j<n ) ) where
    np1 : ( m : ℕ ) → ( (j : ℕ ) → m ≤ j → j < n → gcd n j ≡ 1  ) → NonPrime n
    np1 zero mg = ⊥-elim ( np record { isPrime = λ j lt → mg j z≤n lt } ) -- zero < j , j < n
    np1 (suc m) mg with <-cmp ( gcd n (suc m) ) 1
    ... | tri< a ¬b ¬c = {!!}
    ... | tri≈ ¬a b ¬c = np1 m {!!}
    ... | tri> ¬a ¬b c = record { factor = gcd n (suc m) ; prime = {!!} ; dividable = record { factor = {!!} ; is-factor = {!!} } }

prime-is-infinite : (max-prime : ℕ ) → ¬ ( (j : ℕ) → max-prime < j → ¬ Prime j ) 
prime-is-infinite zero pmax = pmax 1 {!!} record { isPrime = λ n lt → {!!} }
prime-is-infinite (suc m) pmax = pmax (suc (factorial (suc m))) f>m record { isPrime = λ n lt → fact n lt } where
  factorial : (n : ℕ) → ℕ
  factorial zero = 1
  factorial (suc n) = (suc n) * (factorial n)
  f>m :  suc m < suc (factorial (suc m))
  f>m = {!!}
  factm : (n m : ℕ ) → n < (suc m) →  Dividable n (factorial m )
  factm = {!!}
  fact : (n : ℕ ) → n < (suc (factorial (suc m))) →   gcd (suc (factorial (suc m))) n ≡ 1
  fact n lt = fact12  (nonPrime (factorial (suc m )) ( pmax (factorial (suc m )) {!!} )) where
       fact12 : NonPrime (factorial (suc m)) → gcd (suc (factorial (suc m))) n ≡ 1
       fact12 np = {!!}
