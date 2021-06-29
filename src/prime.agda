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
      p>1 : i > 1
      isPrime : ( j : ℕ ) → j < i → 0 < j → gcd i j ≡ 1


record NonPrime ( n : ℕ ) : Set where
   field
      factor : ℕ
      prime : Prime factor
      dividable : Dividable factor n

PrimeP : ( n : ℕ ) → Dec ( Prime n )
PrimeP 0 = no (λ p → ⊥-elim ( nat-<> (Prime.p>1 p) (s≤s z≤n))) 
PrimeP 1 = no (λ p → ⊥-elim ( nat-≤> (Prime.p>1 p) (s≤s (≤-refl))))
PrimeP (suc (suc n)) = isPrime1 (suc (suc n)) (suc n) (s≤s (s≤s z≤n)) a<sa (λ i m<i i<n → isp0 (suc n) i (<to≤ m<i) i<n ) where  
   isp0 : (n : ℕ) (i : ℕ) ( n<i : n ≤ i) ( i<n : i < suc n ) →  gcd (suc n) i ≡ 1
   isp0  n i n<i i<n with <-cmp i n
   ... | tri< a ¬b ¬c = ⊥-elim ( nat-≤> n<i a) 
   ... | tri≈ ¬a refl ¬c = gcd203 i
   ... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> c i<n )
   isPrime1 : ( n m : ℕ ) → n > 1 → m < n → ( (i : ℕ) → m < i → i < n  →  gcd n i ≡ 1 )  → Dec ( Prime n )
   isPrime1 n zero n>1 m<n lt = yes record { isPrime = λ j j<i 0<j → lt j 0<j j<i ; p>1 = n>1 } 
   isPrime1 n (suc m) n>1 m<n lt with <-cmp (gcd n (suc m)) 1
   ... | tri< a ¬b ¬c = ⊥-elim ( nat-≤> ( gcd>0 n (suc m) (<-trans (s≤s z≤n) n>1) (s≤s z≤n)) a )
   ... | tri≈ ¬a b ¬c = isPrime1 n m n>1 (<-trans a<sa m<n) isp1 where
    --  lt : (i : ℕ) → suc m ≤ i → suc i ≤ n → gcd1 n n i i ≡ 1
        isp1 :  (i : ℕ) → m < i → i < n → gcd n i ≡ 1
        isp1 i m<i i<n with <-cmp (suc m) i
        ... | tri< a ¬b ¬c = lt i a i<n
        ... | tri≈ ¬a m=i  ¬c = subst (λ k → gcd n k ≡ 1) m=i b -- gcd n (suc m) ≡ 1 →  gcd n i ≡ 1
        ... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> m<i c) -- suc i ≤ suc m →  i < m
   ... | tri> ¬a ¬b c = no ( λ p → nat-≡< (sym (Prime.isPrime p (suc m) m<n (s≤s z≤n) )) c )

open import logic
open _∧_

data Factoring (m : ℕ ) : (n : ℕ) → Set where
     findFactor : (n : ℕ) → m ≤ n → ( (j : ℕ ) → m ≤ j → j < n → gcd n j ≡ 1  ) → Factoring m n
     skipFactor : (n : ℕ) → n < m →  Factoring m n

nonPrime : { n : ℕ } → 1 < n → ¬ Prime n → NonPrime n
nonPrime {n} 1<n np = np1 n n np 1<n (findFactor n ≤-refl (λ j n≤j j<n → ⊥-elim (nat-≤>  n≤j j<n ) )) where
    mg1 :  (n m : ℕ )→ ( (j : ℕ ) → m < j → j < n → gcd n j ≡ 1  ) →  gcd n m ≡ 1 → (j : ℕ) → m ≤ j → j < n → gcd n j ≡ 1
    mg1 n m mg gcd j m<j j<n with <-cmp m j
    ... | tri< a ¬b ¬c = mg j a j<n  
    ... | tri≈ ¬a refl ¬c = gcd
    ... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> m<j c)
    np1 : ( n m : ℕ ) → ¬ Prime n → 1 < n → Factoring m n → NonPrime n
    np1 n zero np 1<n (findFactor n m≤n mg ) = ⊥-elim ( np record { isPrime = λ j lt _ → mg j z≤n lt ; p>1 = 1<n } ) -- zero < j , j < n
    np1 n (suc m) np 1<n (findFactor n m≤n mg) with <-cmp ( gcd n m ) 1
    ... | tri< a ¬b ¬c = ⊥-elim ( nat-≤> ( gcd>0 n m (<-trans (s≤s z≤n) 1<n) 0<m ) a ) where
         0<m : 0 < m
         0<m with <-cmp 0 m
         ... | tri< a ¬b ¬c = a
         ... | tri≈ ¬a refl ¬c = ⊥-elim ( nat-<> a (subst (λ k → 1 < k) (sym (gcd20 n)) 1<n ))
    ... | tri≈ ¬a b ¬c = np1 n m np 1<n (findFactor n (≤-trans refl-≤s m≤n) (mg1 n m mg b ) )
    ... | tri> ¬a ¬b c with PrimeP ( gcd n m )
    ... | yes y = record { factor = gcd n m ; prime = y ;  dividable = proj1 (gcd-dividable n m ) }
    ... | no ngcd = np2 where
         skip-case : NonPrime (gcd n m) → NonPrime n
         skip-case  cc = record { factor = NonPrime.factor cc ; prime = NonPrime.prime cc ; dividable =
                          record { factor = (Dividable.factor (proj1 (gcd-dividable n m))) * (Dividable.factor (NonPrime.dividable cc))
                              ; is-factor = begin
             Dividable.factor (proj1 (gcd-dividable n m)) * Dividable.factor (NonPrime.dividable cc) * NonPrime.factor cc + 0 ≡⟨ refl ⟩
             g * d * p + 0 ≡⟨ +-comm _ 0 ⟩
             g * d * p  ≡⟨ *-assoc g d p  ⟩
             g * (d * p)  ≡⟨ cong (λ k → g * k ) (+-comm 0 _) ⟩
             g * (d * p + 0)  ≡⟨ cong (λ k → g * k ) (Dividable.is-factor (NonPrime.dividable cc) ) ⟩
             g * gcd n m  ≡⟨ +-comm 0 _ ⟩
             g * gcd n m + 0 ≡⟨ Dividable.is-factor (proj1 (gcd-dividable n m)) ⟩
             n ∎  }} where
                open ≡-Reasoning
                g =  Dividable.factor (proj1 (gcd-dividable n m))
                d =  Dividable.factor (NonPrime.dividable cc)
                p = NonPrime.factor cc
         np2 :  NonPrime n
         np2 with <-cmp (gcd n m) m
         ... | tri< a ¬b ¬c = skip-case (np1 (gcd n m) m ngcd c (skipFactor (gcd n m) a ))
         ... | tri≈ ¬a b ¬c = skip-case (np1 (gcd n m) m ngcd c
              (subst (λ k → Factoring m k) (sym b) (findFactor m ≤-refl (λ j n≤j j<n → ⊥-elim (nat-≤>  n≤j j<n) ))))
         ... | tri> ¬a ¬b' c with <-cmp 0 m
         ... | tri< a ¬b ¬c = ⊥-elim ( nat-≤> (subst (λ k → k ≤ m) (gcdsym {m} {n}) (gcd-≤ a (<-trans a m≤n))) c ) 
         ... | tri≈ ¬a' b' ¬c = ⊥-elim ( np record { isPrime = λ j lt 0<j → mg j (subst (λ k → k < j) b' 0<j) lt ; p>1 = 1<n } ) -- suc m ≤ j
    np1 n zero np 1<n (skipFactor n ())
    np1 n (suc m) np 1<n  (skipFactor n n<m) with <-cmp m n
    ... | tri< a ¬b ¬c = ⊥-elim ( nat-≤> a n<m) 
    ... | tri> ¬a ¬b c    = np1 n m np 1<n (skipFactor n c) 
    ... | tri≈ ¬a refl ¬c = np1 n m np 1<n (findFactor m ≤-refl (λ j n≤j j<n → ⊥-elim (nat-≤>  n≤j j<n) ))

factorial : (n : ℕ) → ℕ
factorial zero = 1
factorial (suc n) = (suc n) * (factorial n)
factorial-mono : (n : ℕ) → factorial n ≤ factorial (suc n)
factorial-mono n = begin
     factorial n  ≤⟨ x≤x+y ⟩
     factorial n + n * factorial n ≡⟨ refl ⟩
     (suc n) * factorial n  ≡⟨ refl ⟩
     factorial (suc n)  ∎  where open ≤-Reasoning
factorial≥1 : {m : ℕ} → 1 ≤ factorial m
factorial≥1 {zero} = ≤-refl
factorial≥1 {suc m} = begin
     1 ≤⟨ s≤s z≤n ⟩
     (suc m) * 1 ≤⟨  *-monoʳ-≤ (suc m) (factorial≥1 {m}) ⟩
     (suc m) * factorial m ≡⟨ refl ⟩
     factorial (suc m)  ∎  where open ≤-Reasoning
m<factorial : (m : ℕ) → m ≤ factorial m
m<factorial zero = z≤n
m<factorial (suc m) = begin
     suc m ≡⟨ cong suc (+-comm 0 _) ⟩
     1 * suc m ≡⟨ *-comm 1 _ ⟩
     (suc m) * 1 ≤⟨  *-monoʳ-≤ (suc m) (factorial≥1 {m}) ⟩
     (suc m) * factorial m  ≡⟨ refl ⟩
     factorial (suc m)  ∎  where open ≤-Reasoning
-- *-monoˡ-≤ (suc m) {!!}
fact< : (m n : ℕ) → 0 < n → n < suc (suc m) → Dividable n ( factorial (suc m) )
fact< zero 1 0<n (s≤s (s≤s z≤n)) = record { factor = 1 ; is-factor = refl }
fact< (suc m) (suc zero) 0<n n<m = record { factor = factorial (suc (suc m)) ; is-factor = begin
     factorial (suc (suc m)) * 1 + 0  ≡⟨ +-comm _ 0 ⟩
     factorial (suc (suc m)) * 1   ≡⟨ m*1=m  ⟩
     (suc (suc m)) * factorial (suc m)  ≡⟨ refl ⟩
     factorial (suc (suc m))  ∎  } where open ≡-Reasoning
fact< (suc m) (suc (suc n)) 0<n n<m with <-cmp (suc (suc n)) (suc (suc m))
... | tri< a ¬b ¬c = record { factor = suc (suc m) * Dividable.factor fact1 ; is-factor = fact2 } where
      fact1 : Dividable (suc (suc n))  (factorial (suc m ))
      fact1 = fact< m (suc (suc n)) 0<n a 
      d =  (fact< m (suc (suc n)) 0<n a)
      fact2 : suc (suc m) * Dividable.factor d * suc (suc n) + 0 ≡ factorial (suc (suc m))
      fact2 = begin
        suc (suc m) * Dividable.factor d * suc (suc n) + 0  ≡⟨ +-comm _ 0 ⟩
        suc (suc m) * Dividable.factor d * suc (suc n)   ≡⟨ *-assoc (suc (suc m)) (Dividable.factor d) ( suc (suc n)) ⟩
        suc (suc m) * (Dividable.factor d * suc (suc n))   ≡⟨ cong (λ k →  suc (suc m) * k ) ( +-comm 0 (Dividable.factor d * suc (suc n)) ) ⟩
        suc (suc m) * (Dividable.factor d * suc (suc n) + 0)   ≡⟨ cong (λ k → suc (suc m) * k ) (Dividable.is-factor d)  ⟩
        suc (suc m) * factorial (suc m)  ≡⟨ refl ⟩
        factorial (suc (suc m))  ∎   where open ≡-Reasoning
... | tri≈ ¬a b ¬c = record { factor = factorial (suc m)  ; is-factor = begin
     factorial (suc m) * suc (suc n) + 0 ≡⟨ +-comm _ 0 ⟩
     factorial (suc m) * suc (suc n)  ≡⟨ *-comm (factorial (suc m)) (suc (suc n))  ⟩
     (suc (suc n)) * factorial (suc m)  ≡⟨ cong (λ k → k * factorial (suc m) ) b ⟩
     (suc (suc m)) * factorial (suc m)  ≡⟨ refl ⟩
     factorial (suc (suc m))  ∎  } where open ≡-Reasoning
... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> c n<m) 

f>m :  {m : ℕ} → suc m < suc (factorial (suc m))
f>m {m} = begin
     suc (suc m)  ≡⟨ cong (λ k → 1 + suc k ) (+-comm _ m) ⟩
     suc (1 + 1 * m)  ≡⟨ cong (λ k → suc (1 + k )) (*-comm 1 m)  ⟩
     suc (1 + m * 1)  ≤⟨ s≤s (s≤s (*-monoʳ-≤ m  (factorial≥1 {m}) )) ⟩
     suc (1 + m * factorial m) ≤⟨ s≤s  (+-monoˡ-≤ _ (factorial≥1 {m})) ⟩
     suc (factorial m + m * factorial m)  ≡⟨ refl ⟩
     suc (factorial (suc m)) ∎  where open ≤-Reasoning

prime-is-infinite : (max-prime : ℕ ) → ¬ ( (j : ℕ) → max-prime < j → ¬ Prime j ) 
prime-is-infinite zero pmax = pmax 3 (s≤s z≤n) record { isPrime = λ n lt 0<j → pif3 n lt 0<j  ; p>1 = s≤s (s≤s z≤n) } where
  pif3 : (n : ℕ) →  n < 3 →  0 < n → gcd 3 n ≡ 1
  pif3 .1 (s≤s (s≤s z≤n)) _ = refl
  pif3 .2 (s≤s (s≤s (s≤s z≤n))) _ = refl
prime-is-infinite (suc m) pmax = newPrime where 
  prime<max : (n : ℕ ) → Prime n → n < suc (suc m)
  prime<max n p with <-cmp n (suc m) 
  ... | tri< a ¬b ¬c = ≤-trans a refl-≤s 
  ... | tri≈ ¬a refl ¬c = ≤-refl 
  ... | tri> ¬a ¬b c = ⊥-elim ( pmax n c p ) 
  fact : (n : ℕ) → Prime n → Dividable n ( factorial (suc m) )
  fact n p = fact< m n (<-trans (s≤s z≤n) (Prime.p>1 p)) ( prime<max n p )
  -- div+1 : { i k : ℕ } → k > 1 →  Dividable k i →  ¬ Dividable k (suc i)
  newPrime : ⊥
  newPrime with PrimeP ( suc (factorial (suc m)) )
  ... | yes p = pmax _ f>m p   -- yes, we found a prime not in list
  ... | no np = div+1 (Prime.p>1 (NonPrime.prime p1)) (fact (NonPrime.factor p1) (NonPrime.prime p1) ) (NonPrime.dividable p1) where
      -- n!+1 cannot be dividable, because n! is dividable
      -- the factor need not be a prime, but anyway we prove that there is a prime factor in NonPrime
      p1 : NonPrime  ( suc (factorial (suc m)) )
      p1 = nonPrime (begin
       2 ≤⟨ s≤s ( s≤s z≤n) ⟩
       suc (suc m) ≤⟨ s≤s (m<factorial (suc m))  ⟩
       suc (factorial (suc m)) ∎ ) np where open ≤-Reasoning 
