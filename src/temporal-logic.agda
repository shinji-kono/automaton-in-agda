open import Level renaming ( suc to succ ; zero to Zero )
module temporal-logic {n : Level} where

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

open import nat
open import Data.Nat.Properties
open import Data.Unit using ( ⊤ ; tt )

-- Linear Time Temporal Logic (clock base, it has ○ (next))

record TL : Set (Level.suc n) where
  field
    at : ℕ → Set n

open TL

always : (P : Set n) →   TL 
always P = record { at = λ t → P }

now :  (P : Set n) → TL 
now  P = record { at = λ t → t ≡ 0 → P }

record Sometime : Set n where
   field
      some : ℕ 

open Sometime

sometimes : (P : Set n) → TL
sometimes P = record { at = λ t → (s : Sometime) → P }

TLtest00 : {t : ℕ } (P : Set n) → at (always P) t → at (now P) t 
TLtest00 P all refl = all

TLtest01 : {t : ℕ } (P : Set n) → ¬ ( (t : ℕ ) →  (at (sometimes (¬ P) ) t )) →  at (always P) t
TLtest01 {t} P ns = ⊥-elim ( ns (λ s sm p → ? ) )

data LTTL ( V : Set )  : Set where
    s :  V → LTTL V                       -- proppsitional variable p is true on this time
    ○ :  LTTL V → LTTL V
    □ :  LTTL V → LTTL V
    ⋄ :  LTTL V → LTTL V
    _U_  :  LTTL V → LTTL  V → LTTL  V
    t-not :  LTTL V → LTTL  V
    _t\/_ :  LTTL V → LTTL  V → LTTL  V
    _t/\_ :  LTTL V → LTTL  V → LTTL  V

{-# TERMINATING #-}
M1 : { V : Set } → (σ : ℕ → V → Bool) → (i : ℕ ) →  LTTL V  → Set
M1 σ i (s x) = σ i x ≡ true
M1 σ i (○ x) = M1 σ (suc i) x  
M1 σ i (□ p) = (j : ℕ) → i ≤ j → M1  σ j p
M1 σ i (⋄ p) = ¬ ( M1 σ i (□ (t-not p) ))
M1 σ i (p U q) = ¬ ( ( j : ℕ) → i ≤ j → ¬ (M1 σ j q ∧ (( k : ℕ) → i ≤ k → k < j → M1 σ j p )) )
M1 σ i (t-not p) = ¬ ( M1 σ i p )
M1 σ i (p t\/ p₁) = M1 σ i p ∨ M1 σ i p₁ 
M1 σ i (p t/\ p₁) = M1 σ i p ∧ M1 σ i p₁ 

data Var : Set where
   p : Var
   q : Var

test00 : ℕ → Var → Bool
test00 3 p = true
test00 _ _ = false

test01 : M1 test00 3 ( s p )
test01 = refl

test02 : ¬ M1 test00 4 ( s p )
test02 ()

-- We cannot write this
--
-- LTTL? : { V : Set } → (σ : ℕ → V → Bool) → (i : ℕ ) → (e : LTTL V ) → Dec ( M1 σ i e )
-- LTTL? {V} σ zero (s x) with σ zero x 
-- ... | true = yes refl
-- ... | false = no ( λ () )
-- LTTL? {V} σ zero (○ e) with  LTTL? {V} σ 1 e 
-- ... | yes y = yes y
-- ... | no n = no n
-- LTTL? {V} σ zero (□ e) = ?
-- LTTL? {V} σ zero (⋄ e) = ?
-- LTTL? {V} σ zero (e U e₁) = ?
-- LTTL? {V} σ zero (t-not e) = ?
-- LTTL? {V} σ zero (e t\/ e₁) = ?
-- LTTL? {V} σ zero (e t/\ e₁) = ?
-- LTTL? {V} σ (suc i) e = ?

--  check validity or satisfiability of LTTL formula
--  generate Buchi or Muller automaton from LTTL formula
--     given some ω automaton, check it satisfies LTTL specification

data LITL ( V : Set )  : Set where
    iv :  V → LITL V
    i○ :  LITL V → LITL V
    _&_  :  LITL V → LITL  V → LITL  V
    i-not :  LITL V → LITL  V
    _i\/_ :  LITL V → LITL  V → LITL  V
    _i/\_ :  LITL V → LITL  V → LITL  V

open import Relation.Binary.Definitions
open import Data.Unit using ( tt ; ⊤ )

{-# TERMINATING #-}
MI : { V : Set } → (ℕ → V → Bool) → (i j : ℕ) → i ≤ j  →  LITL V  → Set
MI σ i j lt (iv x) = σ i x ≡ true
MI σ i j lt (i○ x) with <-cmp i j
... | tri< a ¬b ¬c = MI σ (suc i) j a x
... | tri≈ ¬a b ¬c = ⊤
... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> lt c)
MI σ i j lt (P & Q) = ¬ ( ( k : ℕ) → (i<k : i ≤ k) → (k<j : k ≤ j) → ¬ ( MI σ i k i<k P ∧ MI σ k j k<j P))
MI σ i j lt (i-not P) = ¬ ( MI σ i j lt P )
MI σ i j lt (P i\/ Q) = MI σ i j lt P ∧ MI σ i j lt Q 
MI σ i j lt (P i/\ Q) = MI σ i j lt P ∨ MI σ i j lt Q 

data QBool ( V : Set )  : Set where
    qb :  Bool → QBool V
    qv :  V → QBool V
    exists :  V → QBool V → QBool V
    b-not :  QBool V → QBool  V
    _b\/_ :  QBool V → QBool  V → QBool  V
    _b/\_ :  QBool V → QBool  V → QBool  V

{-# TERMINATING #-}
SQ1 : { V : Set } → ((x y : V) → Dec ( x ≡ y))   → QBool V → V  → Bool → QBool V
SQ1 {V} dec (qb x) v t = qb x
SQ1 {V} dec (qv x) v t with dec x v
... | yes _ = qb t
... | no _ = qv x
SQ1 {V} dec (exists x P) v t = SQ1 dec (SQ1 dec P x true) v t b\/  SQ1 dec (SQ1 dec P x false) v t
SQ1 {V} dec (b-not P) v t = b-not (SQ1 dec P v t )
SQ1 {V} dec (P b\/ Q) v t = SQ1 dec P v t b\/  SQ1 dec Q v t
SQ1 {V} dec (P b/\ Q) v t = SQ1 dec P v t b/\  SQ1 dec Q v t

{-# TERMINATING #-}
MQ : { V : Set } → (V → Bool) → ((x y : V) → Dec ( x ≡ y))   → QBool V → Bool
MQ {V} val dec (qb x) = x
MQ {V} val dec (qv x) = val x
MQ {V} val dec (exists x P) =  MQ val dec ( SQ1 dec P x true b\/ SQ1 dec P x false )
MQ {V} val dec (b-not P) = not ( MQ val dec P )
MQ {V} val dec (P b\/ Q) = MQ val dec P \/ MQ val dec Q 
MQ {V} val dec (P b/\ Q) = MQ val dec P /\ MQ val dec Q 

data QPTL ( V : Set )  : Set where
    qt :  Bool → QPTL V
    qs :  V → QPTL V
    q○ :  QPTL V → QPTL V
    q□ :  QPTL V → QPTL V
    q⋄ :  QPTL V → QPTL V
    q-exists :  V → QPTL V → QPTL V
    q-not :  QPTL V → QPTL  V
    _q\/_ :  QPTL V → QPTL  V → QPTL  V
    _q/\_ :  QPTL V → QPTL  V → QPTL  V

--
--  ∃ p ( <> p → ? )
--


{-# TERMINATING #-}
SQP1 : { V : Set } → ((x y : V) → Dec ( x ≡ y))   → QPTL V → V  → Bool → QPTL V
SQP1 {V} dec (qt x) v t = qt x
SQP1 {V} dec (qs x) v t with dec x v
... | yes _  = qt t
... | no  _  = qs x
SQP1 {V} dec (q-exists x P) v t = SQP1 dec (SQP1 dec P x true) v t q\/  SQP1 dec (SQP1 dec P x false) v t
SQP1 {V} dec (q○ P) v t = q○ P
SQP1 {V} dec (q□ P) v t = SQP1 {V} dec P v t q/\ q□ P
SQP1 {V} dec (q⋄ P) v t = q-not ( SQP1 dec (q□ (q-not P)) v t)
SQP1 {V} dec (q-not P) v t = q-not ( SQP1 dec P v t )
SQP1 {V} dec (P q\/ Q) v t = SQP1 {V} dec  P v t q\/ SQP1 {V} dec  Q v t 
SQP1 {V} dec (P q/\ Q) v t = SQP1 {V} dec  P v t q/\ SQP1 {V} dec  Q v t 

{-# TERMINATING #-}
MQPTL : { V : Set } → (ℕ → V → Bool) → ℕ → ((x y : V) → Dec ( x ≡ y))     →  QPTL V  → Set
MQPTL σ i dec (qt x) = x ≡ true
MQPTL σ i dec (qs x) = σ i x ≡ true
MQPTL σ i dec (q○ x) = MQPTL σ (suc i) dec x  
MQPTL σ i dec (q□ P) = (j : ℕ) → i ≤ j → MQPTL  σ j dec P
MQPTL σ i dec (q⋄ P) = ¬ ( MQPTL σ i dec (q□ (q-not P) ))
MQPTL σ i dec (q-not P) = ¬ ( MQPTL σ i dec P )
MQPTL σ i dec (q-exists x P) = MQPTL σ i dec ( SQP1 dec P x true q\/  (SQP1 dec P x false)) 
MQPTL σ i dec (P q\/ Q) = MQPTL σ i dec P ∧ MQPTL σ i dec Q 
MQPTL σ i dec (P q/\ Q) = MQPTL σ i dec P ∨ MQPTL σ i dec Q 

