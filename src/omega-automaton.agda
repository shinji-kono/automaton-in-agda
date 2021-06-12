module omega-automaton where

open import Level renaming ( suc to succ ; zero to Zero )
open import Data.Nat
open import Data.List
open import Data.Maybe
-- open import Data.Bool using ( Bool ; true ; false ; _∧_ ) renaming ( not to negate )
open import  Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Nullary -- using (not_; Dec; yes; no)
open import Data.Empty

open import logic
open import automaton

open Automaton 

ω-run : { Q  Σ : Set } → (Ω : Automaton Q Σ ) → (astart : Q ) →  ℕ → ( ℕ → Σ )  → Q
ω-run Ω x zero s = x
ω-run Ω x (suc n) s = δ Ω (ω-run Ω x n s) ( s n )

--
-- accept as Buchi automaton
--
record Buchi { Q  Σ : Set } (Ω : Automaton Q Σ ) ( S : ℕ → Σ ) : Set where
    field
        from : ℕ
        stay : (x : Q) → (n : ℕ ) → n > from → aend Ω ( ω-run Ω x n S ) ≡ true

open Buchi

--  after sometimes, always p
--
--                       not p
--                   ------------>
--        <> [] p *                 <> [] p 
--                   <-----------
--                       p

    
--
-- accept as Muller automaton
--
record Muller { Q  Σ : Set } (Ω : Automaton Q Σ ) ( S : ℕ → Σ ) : Set where
    field
        next     : (n : ℕ ) → ℕ 
        infinite : (x : Q) → (n : ℕ ) →  aend Ω ( ω-run Ω x (n + (next n)) S ) ≡ true 

--  always sometimes p
--
--                       not p
--                   ------------>
--        [] <> p *                 [] <> p 
--                   <-----------
--                       p

data  States3   : Set  where
   ts* : States3
   ts  : States3

transition3 : States3  → Bool  → States3
transition3 ts* true  = ts*
transition3 ts* false  = ts
transition3 ts true  = ts*
transition3 ts false  = ts

mark1 :  States3  → Bool
mark1 ts* = true
mark1 ts = false

ωa1 : Automaton States3 Bool
ωa1 = record {
        δ = transition3
     ;  aend = mark1
  }  

true-seq :  ℕ → Bool
true-seq _ = true

false-seq :  ℕ → Bool
false-seq _ = false

flip-seq :  ℕ → Bool
flip-seq zero = false
flip-seq (suc n) = not ( flip-seq n )

lemma0 : Muller ωa1 flip-seq 
lemma0 = record {
        next = λ n → suc (suc n)
      ; infinite = lemma01
   } where
        lemma01 :  (x : States3) (n : ℕ) →
           aend ωa1 (ω-run ωa1 x (n + suc (suc n)) flip-seq) ≡ true
        lemma01 = {!!}

lemma1 : Buchi ωa1 true-seq 
lemma1 = record {
        from = zero
      ; stay = {!!}
   } where
      lem1 : ( n :  ℕ ) → n > zero → aend ωa1 (ω-run ωa1 {!!} n true-seq ) ≡ true
      lem1 zero ()
      lem1 (suc n) (s≤s z≤n) with ω-run ωa1 {!!} n true-seq 
      lem1 (suc n) (s≤s z≤n) | ts* = {!!}
      lem1 (suc n) (s≤s z≤n) | ts = {!!}

ωa2 : Automaton States3 Bool
ωa2 = record {
        δ = transition3
     ;  aend = λ x → not ( mark1 x )
  }  

flip-dec : (n : ℕ ) →  Dec (  flip-seq n   ≡ true )
flip-dec n with flip-seq n
flip-dec n | false = no  λ () 
flip-dec n | true = yes refl

flip-dec1 : (n : ℕ ) → flip-seq (suc n)  ≡ ( not ( flip-seq n ) )
flip-dec1 n = let open ≡-Reasoning in
          flip-seq (suc n )
       ≡⟨⟩
          ( not ( flip-seq n ) )
       ∎

flip-dec2 : (n : ℕ ) → not flip-seq (suc n)  ≡  flip-seq n 
flip-dec2 n = {!!}


record flipProperty : Set where
    field
       flipP : (n : ℕ) →  ω-run ωa2 {!!} {!!} ≡ ω-run ωa2 {!!} {!!}

lemma2 : Muller ωa2 flip-seq 
lemma2 = record {
          next = next
       ;  infinite = {!!}
   }  where
     next : ℕ → ℕ
     next = {!!}
     infinite' : (n m : ℕ) → n ≥″ m → aend ωa2 {!!} ≡ true → aend ωa2 {!!} ≡ true
     infinite' = {!!}
     infinite : (n : ℕ) → aend ωa2 {!!} ≡ true
     infinite = {!!}

lemma3 : Buchi ωa1 false-seq  →  ⊥
lemma3 = {!!}

lemma4 : Muller ωa1 flip-seq  →  ⊥
lemma4 = {!!}







