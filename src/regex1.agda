{-# OPTIONS --allow-unsolved-metas #-}
module regex1 where

open import Level renaming ( suc to succ ; zero to Zero )
open import Data.Fin
open import Data.Nat hiding ( _≟_ )
open import Data.List hiding ( any ;  [_] )
import Data.Bool using ( Bool ; true ; false ; _∧_ )
open import Data.Bool using ( Bool ; true ; false ; _∧_ ; _∨_ )
open import  Relation.Binary.PropositionalEquality as RBF hiding ( [_] ) 
open import Relation.Nullary using (¬_; Dec; yes; no)
open import regex

-- postulate a b c d : Set

data In : Set where
   a : In
   b : In
   c : In
   d : In

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

-- infixr 40 _&_ _||_

r1' =    (< a > & < b >) & < c >                                         --- abc
r1 =    < a > & < b > & < c >                                            --- abc
any = < a > || < b >  || < c >                                           --- a|b|c
r2 =    ( any * ) & ( < a > & < b > & < c > )                            -- .*abc
r3 =    ( any * ) & ( < a > & < b > & < c > & < a > & < b > & < c > )
r4 =    ( < a > & < b > & < c > ) || ( < b > & < c > & < d > )
r5 =    ( any * ) & ( < a > & < b > & < c > || < b > & < c > & < d > )

open import nfa

--    former ++ later  ≡ x
split : {Σ : Set} → ((former : List Σ) → Bool) → ((later :  List Σ) → Bool) → (x : List Σ ) → Bool
split x y  [] = x [] ∧ y []
split x y (h  ∷ t) = (x [] ∧ y (h  ∷ t)) ∨
  split (λ t1 → x (  h ∷ t1 ))  (λ t2 → y t2 ) t

-- tt1 : {Σ : Set} → ( P Q :  List In → Bool ) → split P Q ( a ∷ b ∷ c ∷ [] )
-- tt1 P Q = ?

{-# TERMINATING #-}
repeat : {Σ : Set} → (List Σ → Bool) → List Σ → Bool
repeat x [] = true
repeat {Σ} x ( h  ∷ t ) = split x (repeat {Σ} x) ( h  ∷ t )

regular-language : {Σ : Set} → Regex Σ → ((x y : Σ ) → Dec (x ≡ y))  →  List Σ → Bool
regular-language φ cmp _ = false
regular-language ε cmp [] = true
regular-language ε cmp (_ ∷ _) = false
regular-language (x *) cmp = repeat ( regular-language x cmp  )
regular-language (x & y) cmp  = split ( λ z → (regular-language x  cmp) z ) (λ z →  regular-language y  cmp z )
regular-language (x || y) cmp  = λ s → ( regular-language x  cmp s )  ∨  ( regular-language y  cmp s)
regular-language < h > cmp  [] = false
regular-language < h > cmp  (h1  ∷ [] ) with cmp h h1
... | yes _ = true
... | no _  = false
regular-language < h >  _ (_ ∷ _ ∷ _)  = false

test-regex : regular-language r1' cmpi ( a ∷ [] ) ≡ false
test-regex = refl

test-regex1 : regular-language r2 cmpi ( a ∷ a ∷ b ∷ c ∷ [] ) ≡ true
test-regex1 = refl

                                                                                                                    
test-AB→split : {Σ : Set} → {A B : List In → Bool} → split A B ( a ∷ b ∷ a ∷ [] ) ≡ (
       ( A [] ∧ B ( a ∷ b ∷ a ∷ [] ) ) ∨
       ( A ( a ∷ [] ) ∧ B ( b ∷ a ∷ [] ) ) ∨
       ( A ( a ∷ b ∷ [] ) ∧ B ( a ∷ [] ) ) ∨
       ( A ( a ∷ b ∷ a ∷ [] ) ∧ B  []  )
   )
test-AB→split {_} {A} {B} = refl

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

open import derive In cmpi
open import automaton

ra-ex = trace (regex→automaton r2) (record { state = r2 ; is-derived = unit }) ( a ∷ b ∷ c ∷ [])

