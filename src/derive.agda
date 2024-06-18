{-# OPTIONS --allow-unsolved-metas #-}

open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.List hiding ( [_] )
open import Data.Empty 
open import finiteSet
open import finiteFunc
open import fin

module derive ( Σ : Set) ( fin : FiniteSet Σ ) ( eq? : (x y : Σ) → Dec (x ≡ y)) where

open import automaton
open import logic
open import regex
open import regular-language

-- whether a regex accepts empty input
--
empty? : Regex  Σ → Bool
empty?  ε       = true
empty?  φ       = false
empty? (x *)    = true
empty? (x & y)  = empty? x /\ empty? y
empty? (x || y) = empty? x \/ empty? y
empty? < x >    = false

derivative :  Regex  Σ → Σ → Regex  Σ
derivative ε s = φ
derivative φ s = φ
derivative (x *) s with derivative x s
... | ε = x *
... | φ = φ
... | t = t & (x *)
derivative (x & y) s with empty? x
... | true with derivative x s | derivative y s
... | ε | φ = φ
... | ε | t = t || y
... | φ | t = t
... | x1 | φ = x1 & y
... | x1 | y1 = (x1 & y) || y1
derivative (x & y) s | false with derivative x s 
... | ε = y
... | φ = φ
... | t = t & y
derivative (x || y) s with derivative x s | derivative y s
... | φ | y1 = y1
... | x1 | φ = x1
... | x1 | y1 = x1 || y1
derivative < x > s with eq? x s
... | yes _ = ε
... | no  _ = φ

data regex-states (x : Regex  Σ ) : Regex  Σ → Set where
    unit   : { z : Regex Σ} → z ≡ x → regex-states x z
    derive : { y z : Regex  Σ } → regex-states x y → (s : Σ) → z ≡  derivative y s → regex-states x z 

record Derivative (x : Regex  Σ ) : Set where
    field
       state : Regex  Σ
       is-derived : regex-states x state

open Derivative

derive-step : (r : Regex   Σ) (d0 : Derivative r) → (s : Σ) → regex-states r (derivative (state d0) s)
derive-step r d0 s = derive (is-derived d0) s refl

regex→automaton : (r : Regex   Σ) → Automaton (Derivative r) Σ
regex→automaton r = record { δ = λ d s → 
        record { state = derivative (state d) s ; is-derived = derive (is-derived d) s refl } 
   ; aend = λ d → empty? (state d) }  

regex-match : (r : Regex   Σ) →  (List Σ) → Bool
regex-match ex is = accept ( regex→automaton ex ) record { state =  ex ; is-derived = unit refl } is 

-- open import Relation.Binary.HeterogeneousEquality as HE using (_≅_ ) 

-- open import nfa
open import Data.Nat hiding (eq?)
open import Data.Nat.Properties hiding ( eq? )
open import nat
open import finiteSetUtil
open FiniteSet
open import Data.Fin hiding (_<_ ; _≤_ ; pred )

-- finiteness of derivative 
--    term generate   x & y   for each * and & only once
--      rank : Regex → ℕ 
--   r₀ & r₁ ... r
--   generated state is a subset of the term set

open import Relation.Binary.Definitions

open _∧_ 

fb20 : {r s r₁ s₁ : Regex Σ} → r & r₁ ≡ s & s₁ → (r ≡ s ) ∧  (r₁ ≡ s₁ )
fb20  refl = ⟪ refl , refl ⟫

fb21 : {r s r₁ s₁ : Regex Σ} → r || r₁ ≡ s || s₁ → (r ≡ s ) ∧  (r₁ ≡ s₁ )
fb21  refl = ⟪ refl , refl ⟫

rg-eq? : (r s : Regex Σ) → Dec ( r ≡ s )
rg-eq? ε ε = yes refl
rg-eq? ε φ = no (λ ())
rg-eq? ε (s *) = no (λ ())
rg-eq? ε (s & s₁) = no (λ ())
rg-eq? ε (s || s₁) = no (λ ())
rg-eq? ε < x > = no (λ ())
rg-eq? φ ε = no (λ ())
rg-eq? φ φ = yes refl
rg-eq? φ (s *) = no (λ ())
rg-eq? φ (s & s₁) = no (λ ())
rg-eq? φ (s || s₁) = no (λ ())
rg-eq? φ < x > = no (λ ())
rg-eq? (r *) ε = no (λ ())
rg-eq? (r *) φ = no (λ ())
rg-eq? (r *) (s *) with rg-eq? r s
... | yes eq = yes ( cong (_*) eq)
... | no ne = no (λ eq → ne (fb10 eq) ) where
     fb10 : {r s : Regex Σ} → (r *) ≡ (s *) → r ≡ s 
     fb10  refl = refl
rg-eq? (r *) (s & s₁) = no (λ ())
rg-eq? (r *) (s || s₁) = no (λ ())
rg-eq? (r *) < x > = no (λ ())
rg-eq? (r & r₁) ε = no (λ ())
rg-eq? (r & r₁) φ = no (λ ())
rg-eq? (r & r₁) (s *) = no (λ ())
rg-eq? (r & r₁) (s & s₁) with rg-eq? r s | rg-eq? r₁ s₁
... | yes y | yes y₁ = yes ( cong₂ _&_ y y₁)
... | yes y | no n  = no (λ eq → n (proj2 (fb20 eq) ))
... | no n  | yes y = no (λ eq → n (proj1 (fb20 eq) ))
... | no n  | no n₁ = no (λ eq → n (proj1 (fb20 eq) ))
rg-eq? (r & r₁) (s || s₁) = no (λ ())
rg-eq? (r & r₁) < x > = no (λ ())
rg-eq? (r || r₁) ε = no (λ ())
rg-eq? (r || r₁) φ = no (λ ())
rg-eq? (r || r₁) (s *) = no (λ ())
rg-eq? (r || r₁) (s & s₁) = no (λ ())
rg-eq? (r || r₁) (s || s₁) with rg-eq? r s | rg-eq? r₁ s₁
... | yes y | yes y₁ = yes ( cong₂ _||_ y y₁)
... | yes y | no n  = no (λ eq → n (proj2 (fb21 eq) ))
... | no n  | yes y = no (λ eq → n (proj1 (fb21 eq) ))
... | no n  | no n₁ = no (λ eq → n (proj1 (fb21 eq) ))
rg-eq? (r || r₁) < x > = no (λ ())
rg-eq? < x > ε = no (λ ())
rg-eq? < x > φ = no (λ ())
rg-eq? < x > (s *) = no (λ ())
rg-eq? < x > (s & s₁) = no (λ ())
rg-eq? < x > (s || s₁) = no (λ ())
rg-eq? < x > < x₁ > with eq? x x₁
... | yes y = yes (cong <_> y)
... | no n = no (λ eq → n (fb11 eq))   where
     fb11 : < x > ≡ < x₁ > → x ≡ x₁
     fb11 refl = refl

rank : (r : Regex Σ) → ℕ
rank ε = 0
rank φ = 0
rank (r *) = suc (rank r)
rank (r & r₁) = suc (max (rank r) (rank r₁))
rank (r || r₁) = max (rank r) (rank r₁)
rank < x > = 0

--
-- s is subterm of r
--
data SB : (r s : Regex Σ) → Set where
    sε  : SB ε ε
    sφ  : SB φ φ
    s<> : {s : Σ} → SB < s >  < s > 
    sub|1  : {x y z : Regex Σ} → SB x z → SB (x || y) z
    sub|2  : {x y z : Regex Σ} → SB y z → SB (x || y) z
    sub*   : {x y : Regex Σ} → SB x y  → SB (x *) y
    sub&1  : (x y z : Regex Σ) → SB x z → SB (x & y) z
    sub&2  : (x y z : Regex Σ) → SB y z → SB (x & y) z
    sub*&  : (x y : Regex Σ)   → rank x < rank y  → SB y x       → SB (y *)   (x & (y *)) 
    sub&&  : (x y z : Regex Σ) → rank z < rank x  → SB (x & y) z → SB (x & y) (z & y) 

--
-- set of subterm of s
--
record ISB (r : Regex Σ) : Set where
    field
        s : Regex Σ
        is-sub : SB r s

SubtermS : (x : Regex Σ ) → Set
SubtermS x =  (y : Regex Σ) → SB x y → Bool

nderivative :  (x : Regex  Σ) → SubtermS x → Σ → SubtermS x
nderivative = ?

open import nfa

regex→nautomaton : (r : Regex   Σ) → NAutomaton ? Σ
regex→nautomaton r = record { δ = λ d s → record { state = derivative (state d) s ; is-derived = derive (is-derived d) s refl } 
   ; aend = λ d → empty? (state d) }  

regex-nmatch : (r : Regex   Σ) →  (List Σ) → Bool
regex-nmatch ex is = ? -- accept ( regex→nautomaton ex ) record { state =  ex ; is-derived = unit refl } is 

open import bijection using ( InjectiveF ; Is )  

finISB : (r : Regex Σ) → FiniteSet (ISB r)
finISB ε = record { finite = 1 ;  Q←F = λ _ → record { s = ε ; is-sub = sε } ; F←Q = λ _ → # 0 ; finiso→ = fb01 ; finiso← = fin1≡0  } where
    fb00 : (q : ISB ε) → record { s = ε ; is-sub = sε } ≡ q
    fb00 record { s = .ε ; is-sub = sε } = refl
    fb01 : (q : ISB ε) → record { s = ε ; is-sub = sε } ≡ q
    fb01 record { s = .ε ; is-sub = sε } = refl
finISB φ = record { finite = 1 ;  Q←F = λ _ → record { s = φ ; is-sub = sφ } ; F←Q = λ _ → # 0 ; finiso→ = fb01 ; finiso← = fin1≡0  } where
    fb00 : (q : ISB φ) → record { s = φ ; is-sub = sφ } ≡ q
    fb00 record { s = .φ ; is-sub = sφ } = refl
    fb01 : (q : ISB φ) → record { s = φ ; is-sub = sφ } ≡ q
    fb01 record { s = .φ ; is-sub = sφ } = refl
finISB < s > = record { finite = 1 ;  Q←F = λ _ → record { s = < s > ; is-sub = s<> } ; F←Q = λ _ → # 0 ; finiso→ = fb01 ; finiso← = fin1≡0  } where
    fb00 : (q : ISB < s >) → record { s = < s > ; is-sub = s<> } ≡ q
    fb00 record { s = < s > ; is-sub = s<> } = refl
    fb01 : (q : ISB < s >) → record { s = < s > ; is-sub = s<> } ≡ q
    fb01 record { s = < s > ; is-sub = s<> } = refl
finISB (x || y) = iso-fin (fin-∨ (finISB x) (finISB y)) record { fun← = fb00 ; fun→ = fb01 ; fiso← = {!!} ; fiso→ = {!!} } where
     fb00 : ISB (x || y) → ISB x ∨ ISB y
     fb00 record { s = s ; is-sub = (sub|1 is-sub) } = case1 record { s = s ; is-sub = is-sub } 
     fb00 record { s = s ; is-sub = (sub|2 is-sub) } = case2 record { s = s ; is-sub = is-sub } 
     fb01 : ISB x ∨ ISB y → ISB (x || y)
     fb01 (case1 record { s = s ; is-sub = is-sub }) = record { s = s ; is-sub = sub|1 is-sub  }
     fb01 (case2 record { s = s ; is-sub = is-sub }) = record { s = s ; is-sub = sub|2 is-sub  }
     fb02 : (x : ISB x ∨ ISB y) → fb00 (fb01 x) ≡ x
     fb02 (case1 record { s = s ; is-sub = is-sub }) = refl
     fb02 (case2 record { s = s ; is-sub = is-sub }) = refl
finISB (x & y) = iso-fin (fin-∨ (inject-fin (fin-∧ (finISB x) (finISB y)) fi {!!}) (fin-∨1 (fin-∨ (finISB x) (finISB y)))) {!!} where
     record Z : Set where
        field 
          x1 y1 z : Regex Σ
          lt : rank z < suc (max (rank x1) (rank z))
          is-sub : SB x1 z
     fb00 : ISB (x & y) → {!!}
     fb00 record { s = s ; is-sub = (sub&1 .x .y .s is-sub) } = {!!}
     fb00 record { s = s ; is-sub = (sub&2 .x .y .s is-sub) } = {!!}
     fb00 record { s = (z & y) ; is-sub = (sub&& x y z lt is-sub) } = {!!}
     fi : InjectiveF Z (ISB x ∧ ISB y)
     fi = record { f = f ; inject = {!!} } where
        f : Z → ISB x ∧ ISB y
        f z = ⟪ record { s = Z.x1 z ; is-sub = {!!} }  , {!!} ⟫
finISB (x *) = iso-fin (fin-∨ (inject-fin (finISB x) fi {!!} ) (fin-∨1 (finISB x) )) record { fun← = fb00 } where
     record Z : Set where
        field 
          z : Regex Σ
          lt : rank z < rank x
          is-sub : SB x z
     fi : InjectiveF Z (ISB x) 
     fi = record { f = f ; inject = {!!} } where
        f : Z → ISB x
        f z = record { s = Z.z z ; is-sub = Z.is-sub z }
     fb00 : ISB (x *) → {!!}
     fb00 record { s = s ; is-sub = (sub* is-sub) } = {!!}
     fb00 record { s = (z & (x *)) ; is-sub = (sub*& z x lt is-sub) } = case1 record { z = z ; is-sub = is-sub ; lt = lt }

d-ISB : (r : Regex Σ) → ISB r → (s : Σ) → ISB r → Bool
d-ISB r x s y = ?

toSB : (r : Regex   Σ) →  ISB r → Bool
toSB r record { s = s ; is-sub = is-sub } with rg-eq? r s
... | yes _ = true
... | no _ = false

-- whether one of subset of subterm accepts empty input
-- in case of empty set, return true
--
sbempty? : (r : Regex Σ) → (ISB r → Bool) → Bool
sbempty? ε f with f record { s = ε ; is-sub = sε  }
... | true = true
... | false = true
sbempty? φ f with f record { s = φ ; is-sub = sφ  }
... | true = false
... | false = true
sbempty? (r *) f = true
sbempty? (r & r₁) f = ? where
   sb01 : (isb : ISB (r & r₁)) → ( ISB.is-sub isb ≡ sub&1 _ _ _ ? ) 
        ∨ ( ISB.is-sub isb ≡ sub&2 _ _ _ ? )
        ∨ ( ISB.is-sub isb ≡ subst (λ k → SB ? ?) ? (sub&& _ _ _ ? ? ))
   sb01 isb with ISB.is-sub isb in eq
   ... | sub&1 .r .r₁ .(ISB.s isb) t = case1 ?
   ... | sub&2 .r .r₁ .(ISB.s isb) t = case2 (case1 ?)
   ... | sub&& .r .r₁ z x t = case2 (case2 ?)
   sb00 : ISB r → Bool
   sb00 record { s = s ; is-sub = is-sub } = f record { s = s ; is-sub = sub&1 _ _ _ is-sub }
sbempty? (r || r₁) f with f record { s = r ; is-sub = sub|1 ? } | f record { s = r₁ ; is-sub = sub|2 ? }
... | false | t = true
... | true | t = empty? r \/ empty? r₁ 
sbempty? < x > f with f record { s = < x > ; is-sub = s<> }
... | false = true
... | true = false

sbderive : (r : Regex Σ) →  (ISB r → Bool) → Σ → ISB r → Bool
sbderive ε f s record { s = .ε ; is-sub = sε } = false
sbderive φ f s record { s = t ; is-sub = sφ } = false
sbderive (r *) f s record { s = t ; is-sub = sub* is-sub } = ?
sbderive (r *) f s record { s = .(x & (r *)) ; is-sub = sub*& x .r x₁ is-sub } = ?
sbderive (r & r₁) f s record { s = t ; is-sub = sub&1 .r .r₁ .t is-sub } with f record { s = t ; is-sub = sub&1 r r₁ t is-sub } 
... | false = true
... | true = false
sbderive (r & r₁) f s record { s = t ; is-sub = sub&2 .r .r₁ .t is-sub } with f record { s = t ; is-sub = sub&2 r r₁ t is-sub } 
... | false = true
... | true with derivative r s | derivative r₁ s
... | ε | φ = false
... | ε | y = true
... | φ | y = false
... | x1 | φ = false
... | x1 | y1 = false
sbderive (r & r₁) f s record { s = .(z & r₁) ; is-sub = (sub&& .r .r₁ z x is-sub) } with f record { s = z & r₁ ; is-sub = sub&& r r₁ z x is-sub } 
... | false = true
... | true with derivative r s | derivative r₁ s
... | ε | φ = false
... | ε | y = true
... | φ | y = false
... | x1 | φ = false
... | x1 | y1 = false
sbderive (r || r₁) f s₁ record { s = s ; is-sub = (sub|1 is-sub) } = sbderive r sb00 s₁  record { s = s ; is-sub = is-sub } where
    sb00 : ISB r → Bool 
    sb00 record { s = s ; is-sub = is-sub } = f record { s = s ; is-sub = sub|1 is-sub } 
sbderive (r || r₁) f s₁ record { s = s ; is-sub = (sub|2 is-sub) } = sbderive r₁ sb00 s₁  record { s = s ; is-sub = is-sub } where
    sb00 : ISB r₁ → Bool 
    sb00 record { s = s ; is-sub = is-sub } = f record { s = s ; is-sub = sub|2 is-sub } 
sbderive < x > f s record { s = .(< x >) ; is-sub = s<> } with eq? x s
... | yes _  = false    -- because there is no next state
... | no _  = true      -- because this term set is empty

-- finDerive : (r : Regex Σ) → FiniteSet (Derived r)
--    this is not correct because it contains s || s || s || .....

finSBTA : (r : Regex Σ) → FiniteSet (ISB r → Bool)
finSBTA r = fin→ ( finISB r )

regex→automaton1 : (r : Regex   Σ) → Automaton (ISB r  → Bool) Σ
regex→automaton1 r = record { δ = sbderive r ; aend = sbempty? r }

regex-match1 : (r : Regex   Σ) →  (List Σ) → Bool
regex-match1 r is = accept ( regex→automaton1 r ) (λ sb → toSB r sb) is

rg00 : (x : Σ) (y : List Σ) → {r : Regex Σ} → (d : Derivative r) → state d ≡ φ  → accept (regex→automaton r) d y ≡ false
rg00 x [] d refl = refl
rg00 x (z ∷ y) record { state = φ ; is-derived = isd } refl = rg00 z y record { state = φ ; is-derived = derive isd z refl } refl 

derive-ε : (r : Regex Σ) → (s : Σ) → r ≡ ε → derivative r s ≡ φ
derive-ε r s refl = refl

rg03-or : (x s : Σ) → {r r₁ : Regex Σ} → (derivative (r || r₁) s ≡ derivative r s ) ∨ (derivative (r || r₁) s ≡ derivative r₁ s ) 
    ∨ (derivative (r || r₁) s ≡ derivative r s ||  derivative r₁ s )
rg03-or x s {r} {r₁} with derivative r s | derivative r₁ s 
... | φ | rr = case2 (case1 refl)
... | ε | φ = case1 refl
... | rr * | φ = case1 refl
... | rr & rr₁ | φ = case1 refl
... | rr || rr₁ | φ = case1 refl
... | < x₁ > | φ = case1 refl
... | ε | ε = case2 (case2 refl)
... | rr * | ε = case2 (case2 refl)
... | rr & rr₁ | ε = case2 (case2 refl)
... | rr || rr₁ | ε = case2 (case2 refl)
... | < x₁ > | ε = case2 (case2 refl)
... | ε | rr₁ * = case2 (case2 refl)
... | rr * | rr₁ * = case2 (case2 refl)
... | rr & rr₂ | rr₁ * = case2 (case2 refl)
... | rr || rr₂ | rr₁ * = case2 (case2 refl)
... | < x₁ > | rr₁ * = case2 (case2 refl)
... | rr | rr₁ & rr₂ = case2 (case2 ?)
... | rr | rr₁ || rr₂ = case2 (case2 ?)
... | rr | < x₁ > = case2 (case2 ?)

derive-is-regex-language : (r : Regex Σ) → (x : List Σ )→ regex-language r eq? x ≡  regex-match r x
derive-is-regex-language ε [] = refl
derive-is-regex-language ε (x ∷ x₁) = sym (rg00 x x₁ record { state = φ ; is-derived = derive (unit refl) _ refl} refl) 
derive-is-regex-language φ [] = refl
derive-is-regex-language φ (x ∷ x₁) = sym (rg00 x x₁ record { state = φ ; is-derived = derive (unit refl) _ refl} refl) 
derive-is-regex-language (r *) []  with empty? (r *)
... | true = refl
... | false = refl
derive-is-regex-language (r *) (h ∷ x) = ?  where
    rg03 : (x s : Σ) → ?
    rg03 = ?
derive-is-regex-language (r & r₁) x = ?
derive-is-regex-language (r || r₁) [] = cong₂ (λ j k → j \/ k ) (derive-is-regex-language r []) (derive-is-regex-language r₁ []) 
derive-is-regex-language (r || r₁) (x ∷ x₁) = ? 
derive-is-regex-language < x₁ > [] = refl
derive-is-regex-language < x₁ > (x ∷ []) with eq? x₁ x
... | yes _  = refl
... | no _  = refl
derive-is-regex-language < x₁ > (x ∷ x₂ ∷ x₃) = sym rg02  where
    rg03 : (x s : Σ) → (derivative < x > s ≡ ε ) ∨ (derivative < x > s ≡ φ )
    rg03 x s with eq? x s
    ... | yes _ = case1 refl
    ... | no _ = case2 refl
    rg02 : regex-match < x₁ > (x ∷ x₂ ∷ x₃ ) ≡ false
    rg02 with rg03 x₁ x
    ... | case2 eq = rg00 x (x₂ ∷ x₃) record { state = _ ; is-derived = derive (unit refl) _ refl} eq
    ... | case1 eq = rg00 x₂ x₃ record { state = _ ; is-derived = derive (derive (unit refl) _ refl) _ refl } (derive-ε  _ _ eq )
--    immediate with eq? x₁ x generates an error w != eq? a b of type Dec (a ≡ b)

derive=ISB : (r : Regex Σ) → (x : List Σ )→ regex-language r eq? x ≡  regex-match1 r x
derive=ISB ε [] = refl
derive=ISB ε (x ∷ x₁) = ?
derive=ISB φ [] = refl
derive=ISB φ (x ∷ x₁) = ?
derive=ISB (r *) x = ?
derive=ISB (r & r₁) x = ?
derive=ISB (r || r₁) x = ?
derive=ISB < x₁ > [] = ?
derive=ISB < x₁ > (x ∷ []) with eq? x₁ x
... | yes _ = refl
... | no _ = refl
derive=ISB < x₁ > (x ∷ x₂ ∷ x₃) = ?



---
--     empty?  ((< a > * || < b > * ) & < c > )  = falsee
--
--     derive  ((< a > * || < b > * ) & < c > ) a   = < a > * & < c >
--     derive  ((< a > * || < b > * ) & < c > ) b   = < b > * & < c >
--     derive  ((< a > * || < b > * ) & < c > ) c   = ε
--     derive  ((< a > * || < b > * ) & < c > ) d   = φ
--     
--     empty?  ((< a > * ) & < c > )  = falsee
--     derive  (< a > * & < c > ) a = < a > * & < c >
--     derive  (< a > * & < c > ) b = φ
--     derive  (< a > * & < c > ) c = ε
--     derive  (< a > * & < c > ) d = φ
--
--     empty?  ((< b > * ) & < c > )  = falsee
--     derive  (< b > * & < c > ) a = φ
--     derive  (< b > * & < c > ) b = < b > * & < c >
--     derive  (< b > * & < c > ) c = ε
--     derive  (< b > * & < c > ) d = φ

