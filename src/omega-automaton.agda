{-# OPTIONS --cubical-compatible --safe --warning=noUnsupportedIndexedMatch #-}
-- {-# OPTIONS --cubical-compatible --safe #-}
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
-- accept as Muller automaton
--
record Muller { Q  Σ : Set } (Ω : Automaton Q Σ ) ( S : ℕ → Σ ) : Set where
    field
        from : ℕ
        stay : (x : Q) → (n : ℕ ) → n > from → aend Ω ( ω-run Ω x S n ) ≡ true

open Muller

--  after sometimes, always p
--
--                       not p
--                   ------------>
--        <> [] p *                 <> [] p
--                   <-----------
--                       p

--
-- accept as Buchi automaton
--
record Buchi { Q  Σ : Set } (Ω : Automaton Q Σ ) ( S : ℕ → Σ ) : Set where
    field
        next     : (n : ℕ ) → ℕ
        infinite : (x : Q) → (n : ℕ ) →  aend Ω ( ω-run Ω x  S (n + (suc (next n)))) ≡ true

open  Buchi
--  always sometimes p
--
--                       not p
--                   ------------>
--        [] <> p *                 [] <> p
--                   <-----------
--                       p

open import nat
open import Data.Nat.Properties

ω-cong : { Q  Σ : Set } → (Ω Ω' : Automaton Q Σ ) → (q : Q) →  ( S : ℕ → Σ )  → (x : ℕ)
    → δ Ω ≡ δ Ω'
    → ω-run Ω q S x ≡ ω-run Ω' q S x
ω-cong Ω  Ω' q s zero refl =  refl
ω-cong Ω  Ω' q s (suc n) eq = begin
     ω-run Ω q s (suc n) ≡⟨⟩
     δ Ω (ω-run Ω q s n) (s n) ≡⟨ cong₂ (λ j k → j k (s n) ) eq (ω-cong Ω  Ω' q s n eq) ⟩
     δ Ω' (ω-run Ω' q s n) (s n) ≡⟨⟩
     ω-run Ω' q s (suc n) ∎  where open ≡-Reasoning

--
-- <> [] p → ¬ [] <> ¬ p
--


B→M : { Q  Σ : Set } (Ω : Automaton Q Σ ) ( S : ℕ → Σ ) → Q → Muller Ω S → ¬ ( Buchi record { δ = δ Ω ; aend = λ q → not (aend Ω q)} S )
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
     not (not (aend Ω (ω-run Ω q S (from b + suc (next m (from b)))))) ≡⟨ cong (λ k → not (not (aend  Ω k))) (ω-cong Ω Ω' q S (from b + suc (next m (from b))) refl) ⟩
     not (not (aend Ω (ω-run Ω' q S (from b + suc (next m (from b)))))) ≡⟨⟩
     not (aend Ω' (ω-run Ω' q S (from b + (suc (next m (from b)))))) ≡⟨ cong (λ k → not k ) bm03  ⟩
     false ∎  where open ≡-Reasoning

--
-- [] <> p → ¬ <> [] ¬ p
--

M→B : { Q  Σ : Set } (Ω : Automaton Q Σ ) ( S : ℕ → Σ ) → Q → Buchi Ω S → ¬ ( Muller record { δ = δ Ω ; aend = λ q → not (aend Ω q)} S )
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
     not (not (aend Ω (ω-run Ω q S (from b + suc (next m (from b)))))) ≡⟨ cong (λ k → not (not (aend  Ω k))) (ω-cong Ω Ω' q S (from b + suc (next m (from b))) refl) ⟩
     not (not (aend Ω (ω-run Ω' q S (from b + suc (next m (from b)))))) ≡⟨⟩
     not (aend Ω' (ω-run Ω' q S (from b + (suc (next m (from b)))))) ≡⟨ cong (λ k → not k ) bm03 ⟩
     false ∎  where open ≡-Reasoning

open import Relation.Binary.Definitions


lemma3 : {i j : ℕ} → 0 ≡ i → j < i → ⊥
lemma3 refl ()
lemma5 : {i j : ℕ} → i < 1 → j < i → ⊥
lemma5 {zero}  {j} i<1 j<i = ⊥-elim ( nat-≤> j<i (s≤s z≤n ))
lemma5 {suc i} {j} i<1 j<i = ⊥-elim ( nat-≤> (s≤s z≤n ) i<1 )

TerminatingLoopS : {l m : Level} {t : Set l} (Context : Set m ) → {Invraiant : Context → Set m } → ( reduce : Context → ℕ)
   → (r : Context) → (p : Invraiant r)
   → (loop : (r : Context)  → Invraiant r → (next : (r1 : Context)  → Invraiant r1 → reduce r1 < reduce r  → t ) → t) → t
TerminatingLoopS {_} {_} {t} Context {Invraiant} reduce r p loop with <-cmp 0 (reduce r)
... | tri≈ ¬a b ¬c = loop r p (λ r1 p1 lt → ⊥-elim (lemma3 b lt) )
... | tri< a ¬b ¬c = loop r p (λ r1 p1 lt1 → TerminatingLoop1 (reduce r) r r1 (m≤n⇒m≤1+n lt1) p1 lt1 ) where
    TerminatingLoop1 : (j : ℕ) → (r r1 : Context) → reduce r1 < suc j  → Invraiant r1 →  reduce r1 < reduce r → t
    TerminatingLoop1 zero r r1 n≤j p1 lt = loop r1 p1 (λ r2 p1 lt1 → ⊥-elim (lemma5 n≤j lt1))
    TerminatingLoop1 (suc j) r r1  n≤j p1 lt with <-cmp (reduce r1) (suc j)
    ... | tri< a ¬b ¬c = TerminatingLoop1 j r r1 a p1 lt
    ... | tri≈ ¬a b ¬c = loop r1 p1 (λ r2 p2 lt1 → TerminatingLoop1 j r1 r2 (subst (λ k → reduce r2 < k ) b lt1 ) p2 lt1 )
    ... | tri> ¬a ¬b c =  ⊥-elim ( nat-≤> c n≤j )



open import finiteSet

--    q₀ → q₁ → ... q
--    q₀ → q₁ → q₅ .... q₅  ... q

open FiniteSet

-- descendSubset : { Q : Set } → (fin : FiniteSet Q) → ( I : Q → Bool) → ( P : Q → Bool )
--     → exists fin (λ q → I q /\ P q) ≡ true → Q → Bool
-- descendSubset = ?

-- is-Muller-valid : { Q  Σ : Set } (Ω : Automaton Q Σ ) → FiniteSet Q → Q → Dec ((S : ℕ → Σ) →  Muller Ω S)
-- is-Muller-valid = ?

-- descendSubset monotonically descend
-- derivation tree of Q will be constructed
-- check contruction of Muller Ω S


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

-- flip-seq is acceepted by Buchi automaton ωa1

-- lemma1 : Muller ωa1 true-seq
-- lemma1 = record {
--         from = zero
--       ; stay = {!!}
--    } where
--       lem1 : ( n :  ℕ ) → n > zero → aend ωa1 (ω-run ωa1 {!!} true-seq n ) ≡ true
--       lem1 zero ()
--       lem1 (suc n) (s≤s z≤n) with ω-run ωa1 {!!} true-seq n
--       lem1 (suc n) (s≤s z≤n) | ts* = {!!}
--       lem1 (suc n) (s≤s z≤n) | ts = {!!}

-- lemma0 : Buchi ωa1 flip-seq
-- lemma0 = {!!}

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

-- flip-dec2 : (n : ℕ ) → ? -- not flip-seq (suc n)  ≡  flip-seq n
-- flip-dec2 n = {!!}


-- record flipProperty : Set where
--     field
--        flipP : (n : ℕ) →  ω-run ωa2 {!!} {!!} ≡ ω-run ωa2 {!!} {!!}

-- lemma2 : Buchi ωa2 flip-seq
-- lemma2 = record {
--           next = next1
--        ;  infinite = {!!}
--    }  where
--      next1 : ℕ → ℕ
--      next1 = {!!}
--      infinite' : (n m : ℕ) → n ≥″ m → aend ωa2 {!!} ≡ true → aend ωa2 {!!} ≡ true
--      infinite' = {!!}
--      infinite2 : (n : ℕ) → aend ωa2 {!!} ≡ true
--      infinite2 = {!!}
--
-- lemma3 : Muller ωa1 false-seq  →  ⊥
-- lemma3 = {!!}
--
-- lemma4 : Buchi ωa1 flip-seq  →  ⊥
-- lemma4 = {!!}
--
--

-- Fair scheduler
--      P₀ .. Pn
--       will be scheduled in a fair way
--      []<> P₀ ∧ []<> P₁ ∧ ... []<> Pn

sched-run : (i pn self : ℕ ) → i < pn → self < pn → Bool
sched-run i pn self i<pn s<pn with i ≟ self
... | yes y = true
... | no y = false

-- fair-scheduler : {Q Σ : Set } → ( pn : ℕ ) → (input : ( n i : ℕ ) → i < pn ) → Set
-- fair-scheduler {Q} {Σ} pn input = fair-scheduler1 pn pn input where
--     task : automaton Q Σ
--     task = ?
--     fair-scheduler1 : {Q Σ : Set } → ( pn self : ℕ ) → (input : ( n i : ℕ ) → i < pn ) → Set
--     fair-scheduler1 {Q} {Σ} pn 0 input = Buchi record { δ = λ q i → sched-run ? pn 0 ? ? ; aend = λ q  → q }  ?
--     fair-scheduler1 pn (suc i) input = ?




