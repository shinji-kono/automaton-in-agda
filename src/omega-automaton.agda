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

ω-run : { Q  Σ : Set } → (Ω : Automaton Q Σ ) → Q →  ( ℕ → Σ )  → ( ℕ → Q )
ω-run Ω x s zero = x
ω-run Ω x s (suc n) = δ Ω (ω-run Ω x s n) ( s n )

--
-- accept as Buchi automaton
--
record Buchi { Q  Σ : Set } (Ω : Automaton Q Σ ) ( S : ℕ → Σ ) : Set where
    field
        from : ℕ
        stay : (x : Q) → (n : ℕ ) → n > from → aend Ω ( ω-run Ω x S n ) ≡ true

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
        infinite : (x : Q) → (n : ℕ ) →  aend Ω ( ω-run Ω x  S (n + (suc (next n)))) ≡ true 

open  Muller 
--  always sometimes p
--
--                       not p
--                   ------------>
--        [] <> p *                 [] <> p 
--                   <-----------
--                       p

open import nat
open import Data.Nat.Properties

-- LEMB : { Q  Σ : Set } (Ω : Automaton Q Σ ) ( S : ℕ → Σ ) → Q → Buchi Ω S ∨ (¬ ( Buchi Ω S ))
-- LEMB Ω S Q = {!!}  -- S need not to be constructive, so we have no constructive LEM

-- LEMM : { Q  Σ : Set } (Ω : Automaton Q Σ ) ( S : ℕ → Σ ) → Q → Muller Ω S ∨ (¬ ( Muller Ω S ))
-- LEMM = {!!}

ω-run-eq : { Q  Σ : Set } → (Ω Ω' : Automaton Q Σ ) → (q : Q) →  ( S : ℕ → Σ )  → (x : ℕ)
    → δ Ω ≡ δ Ω'
    → ω-run Ω q S x ≡ ω-run Ω' q S x
ω-run-eq Ω  Ω' q s zero refl =  refl
ω-run-eq Ω  Ω' q s (suc n) eq = begin
     ω-run Ω q s (suc n) ≡⟨⟩
     δ Ω (ω-run Ω q s n) (s n) ≡⟨ cong₂ (λ j k → j k (s n) ) eq (ω-run-eq Ω  Ω' q s n eq) ⟩
     δ Ω' (ω-run Ω' q s n) (s n) ≡⟨⟩
     ω-run Ω' q s (suc n) ∎  where open ≡-Reasoning

--
-- <> [] p → ¬ [] <> ¬ p
--


B→M : { Q  Σ : Set } (Ω : Automaton Q Σ ) ( S : ℕ → Σ ) → Q → Buchi Ω S → ¬ ( Muller record { δ = δ Ω ; aend = λ q → not (aend Ω q)} S )
B→M {Q} {Σ} Ω S q b m = ¬-bool bm04 bm02 where
   q1 : Q
   q1 = ω-run Ω q S (from b + suc (next m (from b)))
   bm02 : aend Ω q1 ≡ true
   bm02 = stay b q (from b + suc (next m (from b) )) x≤x+sy 
   Ω' : Automaton  Q Σ
   Ω' = record {  δ = δ Ω ; aend = λ q → not (aend Ω q) }
   bm03 : aend Ω' (ω-run Ω' q S (from b + (suc (next m (from b))))) ≡ true
   bm03 = infinite m q (from b)
   bm04 : aend Ω q1 ≡ false
   bm04 = begin
     aend Ω (ω-run Ω q S (from b + suc (next m (from b)))) ≡⟨ sym not-not-bool ⟩
     not (not (aend Ω (ω-run Ω q S (from b + suc (next m (from b)))))) ≡⟨ cong (λ k → not (not (aend  Ω k))) (ω-run-eq Ω Ω' q S (from b + suc (next m (from b))) refl) ⟩
     not (not (aend Ω (ω-run Ω' q S (from b + suc (next m (from b)))))) ≡⟨⟩
     not (aend Ω' (ω-run Ω' q S (from b + (suc (next m (from b)))))) ≡⟨ cong (λ k → not k ) bm03  ⟩
     false ∎  where open ≡-Reasoning

--
-- [] <> p → ¬ <> [] ¬ p
--

M→B : { Q  Σ : Set } (Ω : Automaton Q Σ ) ( S : ℕ → Σ ) → Q → Muller Ω S → ¬ ( Buchi record { δ = δ Ω ; aend = λ q → not (aend Ω q)} S )
M→B {Q} {Σ} Ω S q m b = ¬-bool bm04 bm02 where
   q1 : Q
   q1 = ω-run Ω q S (from b + suc (next m (from b)))
   bm02 : aend Ω q1 ≡ true
   bm02 = infinite m q (from b)
   Ω' : Automaton  Q Σ
   Ω' = record {  δ = δ Ω ; aend = λ q → not (aend Ω q) }
   bm03 : aend Ω' (ω-run Ω' q S (from b + (suc (next m (from b))))) ≡ true
   bm03 = stay b q (from b + suc (next m (from b) )) x≤x+sy 
   bm04 : aend Ω q1 ≡ false
   bm04 = begin
     aend Ω (ω-run Ω q S (from b + suc (next m (from b)))) ≡⟨ sym not-not-bool ⟩
     not (not (aend Ω (ω-run Ω q S (from b + suc (next m (from b)))))) ≡⟨ cong (λ k → not (not (aend  Ω k))) (ω-run-eq Ω Ω' q S (from b + suc (next m (from b))) refl) ⟩
     not (not (aend Ω (ω-run Ω' q S (from b + suc (next m (from b)))))) ≡⟨⟩
     not (aend Ω' (ω-run Ω' q S (from b + (suc (next m (from b)))))) ≡⟨ cong (λ k → not k ) bm03 ⟩
     false ∎  where open ≡-Reasoning



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

-- flip-seq is acceepted by Muller automaton ωa1 

lemma1 : Buchi ωa1 true-seq 
lemma1 = record {
        from = zero
      ; stay = {!!}
   } where
      lem1 : ( n :  ℕ ) → n > zero → aend ωa1 (ω-run ωa1 {!!} true-seq n ) ≡ true
      lem1 zero ()
      lem1 (suc n) (s≤s z≤n) with ω-run ωa1 {!!} true-seq n
      lem1 (suc n) (s≤s z≤n) | ts* = {!!}
      lem1 (suc n) (s≤s z≤n) | ts = {!!}

lemma0 : Muller ωa1 flip-seq 
lemma0 = {!!}

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
          next = next1
       ;  infinite = {!!}
   }  where
     next1 : ℕ → ℕ
     next1 = {!!}
     infinite' : (n m : ℕ) → n ≥″ m → aend ωa2 {!!} ≡ true → aend ωa2 {!!} ≡ true
     infinite' = {!!}
     infinite2 : (n : ℕ) → aend ωa2 {!!} ≡ true
     infinite2 = {!!}

lemma3 : Buchi ωa1 false-seq  →  ⊥
lemma3 = {!!}

lemma4 : Muller ωa1 flip-seq  →  ⊥
lemma4 = {!!}


