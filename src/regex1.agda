{-# OPTIONS --allow-unsolved-metas #-}
module regex1 where

open import Level renaming ( suc to succ ; zero to Zero )
open import Data.Fin
open import Data.Nat hiding ( _≟_ )
open import Data.List hiding ( any ;  [_] )
-- import Data.Bool using ( Bool ; true ; false ; _∧_ )
-- open import Data.Bool using ( Bool ; true ; false ; _∧_ ; _∨_ )
open import  Relation.Binary.PropositionalEquality as RBF hiding ( [_] ) 
open import Relation.Nullary using (¬_; Dec; yes; no)
open import regex
open import logic

-- postulate a b c d : Set

data In : Set where
   a : In
   b : In
   c : In
   d : In

-- infixr 40 _&_ _||_

r1' =    (< a > & < b >) & < c >                                         --- abc
r1 =    < a > &  < b > & < c >                                            --- abc
r0 : ¬ (r1' ≡ r1)
r0 ()
any = < a > || < b >  || < c > || < d >                                   --- a|b|c|d
r2 =    ( any * ) & ( < a > & < b > & < c > )                            -- .*abc
r3 =    ( any * ) & ( < a > & < b > & < c > & < a > & < b > & < c > )
r4 =    ( < a > & < b > & < c > ) || ( < b > & < c > & < d > )
r5 =    ( any * ) & ( < a > & < b > & < c > || < b > & < c > & < d > )

open import nfa

--    former ++ later  ≡ x
split : {Σ : Set} → ((former : List Σ) → Bool) → ((later :  List Σ) → Bool) → (x : List Σ ) → Bool
split x y  [] = x [] /\ y []
split x y (h  ∷ t) = (x [] /\ y (h  ∷ t)) \/
  split (λ t1 → x (  h ∷ t1 ))  (λ t2 → y t2 ) t

-- tt1 : {Σ : Set} → ( P Q :  List In → Bool ) → split P Q ( a ∷ b ∷ c ∷ [] )
-- tt1 P Q = ?

{-# TERMINATING #-}
repeat : {Σ : Set} → (List Σ → Bool) → List Σ → Bool
repeat x [] = true
repeat {Σ} x ( h  ∷ t ) = split x (repeat {Σ} x) ( h  ∷ t )

-- Meaning of regular expression

regular-language : {Σ : Set} → Regex Σ → ((x y : Σ ) → Dec (x ≡ y))  →  List Σ → Bool
regular-language φ cmp _ = false
regular-language ε cmp [] = true
regular-language ε cmp (_ ∷ _) = false
regular-language (x *) cmp = repeat ( regular-language x cmp  )
regular-language (x & y) cmp  = split ( λ z → regular-language x  cmp z ) (λ z →  regular-language y  cmp z )
regular-language (x || y) cmp  = λ s → ( regular-language x  cmp s )  \/  ( regular-language y  cmp s)
regular-language < h > cmp  [] = false
regular-language < h > cmp  (h1  ∷ [] ) with cmp h h1
... | yes _ = true
... | no _  = false
regular-language < h >  _ (_ ∷ _ ∷ _)  = false

cmpi : (x y : In ) → Dec (x ≡ y)
cmpi a a = yes refl
cmpi b b =  yes refl
cmpi c c =  yes refl
cmpi d d =  yes refl
cmpi a b =  no (λ ())
cmpi a c =  no (λ ())
cmpi a d =  no (λ ())
cmpi b a = no (λ ())
cmpi b c = no (λ ()) 
cmpi b d = no (λ ()) 
cmpi c a = no (λ ()) 
cmpi c b = no (λ ()) 
cmpi c d = no (λ ()) 
cmpi d a = no (λ ()) 
cmpi d b = no (λ ()) 
cmpi d c = no (λ ()) 

test-regex : regular-language r1' cmpi ( a ∷ [] ) ≡ false
test-regex = refl

test-regex1 : regular-language r2 cmpi ( a ∷ a ∷ b ∷ c ∷ [] ) ≡ true
test-regex1 = refl

                                                                                                                    
test-AB→split : {Σ : Set} → {A B : List In → Bool} → split A B ( a ∷ b ∷ a ∷ [] ) ≡ (
       ( A [] /\ B ( a ∷ b ∷ a ∷ [] ) ) \/
       ( A ( a ∷ [] ) /\ B ( b ∷ a ∷ [] ) ) \/
       ( A ( a ∷ b ∷ [] ) /\ B ( a ∷ [] ) ) \/
       ( A ( a ∷ b ∷ a ∷ [] ) /\ B  []  )
   )
test-AB→split {_} {A} {B} = refl

list-eq : {Σ : Set} → (cmpi : (s t : Σ)  → Dec (s ≡ t ))  → (s t : List Σ ) → Bool
list-eq cmpi [] [] = true
list-eq cmpi [] (x ∷ t) = false
list-eq cmpi (x ∷ s) [] = false
list-eq cmpi (x ∷ s) (y ∷ t) with cmpi x y
... | yes _ = list-eq cmpi s t
... | no _ = false

-- split-spec-01 :  {s t u : List In } → s ++ t ≡ u → split (list-eq cmpi s) (list-eq cmpi t)  u ≡ true
-- split-spec-01 = {!!}

-- from example 1.53 1

ex53-1 : Set 
ex53-1 = (s : List In ) → regular-language ( (< a > *) & < b > & (< a > *) ) cmpi s ≡ true → {!!} -- contains exact one b

ex53-2 : Set 
ex53-2 = (s : List In ) → regular-language ( (any * ) & < b > & (any *) ) cmpi s ≡ true → {!!} -- contains at lease one b

evenp : {Σ : Set} →  List Σ → Bool
oddp : {Σ : Set} →  List Σ → Bool
oddp [] = false
oddp (_ ∷ t) = evenp t

evenp [] = true
evenp (_ ∷ t) = oddp t

-- from example 1.53 5
egex-even : Set
egex-even = (s : List In ) → regular-language ( ( any & any ) * ) cmpi s ≡ true → evenp s ≡ true

test11 =  regular-language ( ( any & any ) * ) cmpi (a ∷ [])
test12 =  regular-language ( ( any & any ) * ) cmpi (a ∷ b ∷ [])

-- proof-egex-even : egex-even 
-- proof-egex-even [] _ = refl
-- proof-egex-even (a ∷ []) ()
-- proof-egex-even (b ∷ []) ()
-- proof-egex-even (c ∷ []) ()
-- proof-egex-even (x ∷ x₁ ∷ s) y = proof-egex-even s {!!}

open import finiteSet

iFin : FiniteSet In
iFin = record {
     finite = finite0
   ; Q←F = Q←F0
   ; F←Q = F←Q0
   ; finiso→ = finiso→0
   ; finiso← = finiso←0
 } where
     finite0 : ℕ
     finite0 = 4
     Q←F0 : Fin finite0 → In
     Q←F0 zero = a
     Q←F0 (suc zero) = b
     Q←F0 (suc (suc zero)) = c
     Q←F0 (suc (suc (suc zero))) = d
     F←Q0 : In → Fin finite0
     F←Q0 a = # 0
     F←Q0 b = # 1
     F←Q0 c = # 2
     F←Q0 d = # 3
     finiso→0 : (q : In) → Q←F0 ( F←Q0 q ) ≡ q
     finiso→0 a = refl
     finiso→0 b = refl
     finiso→0 c =  refl
     finiso→0 d =  refl
     finiso←0 : (f : Fin finite0 ) → F←Q0 ( Q←F0 f ) ≡ f
     finiso←0 zero = refl
     finiso←0 (suc zero) = refl
     finiso←0 (suc (suc zero)) = refl
     finiso←0 (suc (suc (suc zero))) = refl


open import derive In iFin
open import automaton

ra-ex = trace (regex→automaton cmpi r2) (record { state = r2 ; is-derived = unit }) ( a ∷ b ∷ c ∷ [])

