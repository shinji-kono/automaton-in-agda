module puzzle where

---- 仮定
-- 猫か犬を飼っている人は山羊を飼ってない
-- 猫を飼ってない人は、犬かウサギを飼っている
-- 猫も山羊も飼っていない人は、ウサギを飼っている
--
---- 問題
-- 山羊を飼っている人は、犬を飼っていない
-- 山羊を飼っている人は、ウサギを飼っている
-- ウサギを飼っていない人は、猫を飼っている

module pet-research where
  open import logic
  open import Relation.Nullary
  open import Data.Empty

  postulate   -- the law of exclude middle
     lem : (a : Set) → a ∨ ( ¬ a )

  record PetResearch ( Cat Dog Goat Rabbit : Set ) : Set where
     field
        fact1 :  Cat ∨ Dog  → ¬ Goat
        fact2 : ¬ Cat →   Dog ∨ Rabbit 
        fact3 : ¬ ( Cat ∨ Goat ) →  Rabbit

  module tmp ( Cat Dog Goat Rabbit : Set ) (p :  PetResearch  Cat Dog Goat Rabbit ) where

    open PetResearch

    problem0 : Cat ∨ Dog ∨ Goat ∨ Rabbit
    problem0 with lem Cat | lem Goat
    ... | case1 c | g = case1 c
    ... | case2 ¬c | case1 g = case2 ( case2 ( case1 g ) )
    ... | case2 ¬c | case2 ¬g  = case2 ( case2 ( case2 ( fact3 p lemma1 ))) where
        lemma1 : ¬ ( Cat ∨ Goat )
        lemma1 (case1 c) = ¬c c
        lemma1 (case2 g) = ¬g g

    problem1 : Goat → ¬ Dog
    problem1 g d = fact1 p (case2 d) g 
  
    problem2 : Goat → Rabbit
    problem2 g with lem Cat | lem Dog
    problem2 g | case1 c | d = ⊥-elim ( fact1 p (case1 c ) g )
    problem2 g | case2 ¬c | case1 d = ⊥-elim ( fact1 p (case2 d ) g )
    problem2 g | case2 ¬c | case2 ¬d with lem Rabbit
    ... | case1  r = r
    ... | case2 ¬r = fact3 p lemma2 where
        lemma2 : ¬ ( Cat ∨ Goat )
        lemma2 (case1 c) = ¬c c
        lemma2 (case2 g) with fact2 p ¬c
        lemma2 (case2 g) | case1 d = ¬d d
        lemma2 (case2 g) | case2 r = ¬r r

    problem3 : (¬ Rabbit ) → Cat
    problem3 ¬r with lem Cat | lem Goat 
    problem3 ¬r | case1 c | g = c
    problem3 ¬r | case2 ¬c | g = ⊥-elim ( ¬r ( fact3 p lemma3 )) where
        lemma3 :  ¬ ( Cat ∨ Goat )
        lemma3 (case1 c) = ¬c c
        lemma3 (case2 g) with fact2 p ¬c
        lemma3 (case2 g) | case1 d = fact1 p (case2 d ) g
        lemma3 (case2 g) | case2 r = ¬r r

module pet-research1 ( Cat Dog Goat Rabbit : Set ) where

  open import Data.Bool
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality 

  _=>_ :  Bool → Bool → Bool
  _ => true = true
  false => false = true
  true => false = false

  ¬_ : Bool → Bool
  ¬ p = not p

  problem0 :  ( Cat Dog Goat Rabbit : Bool ) →
    ((( Cat ∨ Dog ) => (¬ Goat) ) ∧ ( (¬ Cat ) =>  ( Dog ∨ Rabbit ) ) ∧ ( ( ¬ ( Cat ∨ Goat ) ) =>  Rabbit ) )
    => (Cat ∨ Dog ∨ Goat ∨ Rabbit) ≡ true
  problem0 true d g r = refl
  problem0 false true g r = refl
  problem0 false false true r = refl
  problem0 false false false true = refl
  problem0 false false false false = refl

  problem1 :  ( Cat Dog Goat Rabbit : Bool ) →
    ((( Cat ∨ Dog ) => (¬ Goat) ) ∧ ( (¬ Cat ) =>  ( Dog ∨ Rabbit ) ) ∧ ( ( ¬ ( Cat ∨ Goat ) ) =>  Rabbit ) )
    => ( Goat => ( ¬ Dog )) ≡ true
  problem1 c false false r = refl
  problem1 c true false r = refl
  problem1 c false true r = refl
  problem1 false true true r = refl
  problem1 true true true r = refl

  problem2 :  ( Cat Dog Goat Rabbit : Bool ) →
    ((( Cat ∨ Dog ) => (¬ Goat) ) ∧ ( (¬ Cat ) =>  ( Dog ∨ Rabbit ) ) ∧ ( ( ¬ ( Cat ∨ Goat ) ) =>  Rabbit ) )
    => ( Goat => Rabbit ) ≡ true
  problem2 c d false false = refl
  problem2 c d false true = refl
  problem2 c d true true = refl
  problem2 true d true false = refl
  problem2 false false true false = refl
  problem2 false true true false = refl

  problem3 :  ( Cat Dog Goat Rabbit : Bool ) →
    ((( Cat ∨ Dog ) => (¬ Goat) ) ∧ ( (¬ Cat ) =>  ( Dog ∨ Rabbit ) ) ∧ ( ( ¬ ( Cat ∨ Goat ) ) =>  Rabbit ) )
    => ( (¬ Rabbit ) => Cat ) ≡ true
  problem3 false d g true = refl 
  problem3 true d g true = refl
  problem3 true d g false = refl
  problem3 false false false false = refl
  problem3 false false true false = refl
  problem3 false true false false = refl
  problem3 false true true false = refl

-- module pet-research2 ( Cat Dog Goat Rabbit : Set ) where
-- 
--   open import Data.Bool hiding ( _∨_ )
--   open import Relation.Binary
--   open import Relation.Binary.PropositionalEquality 
-- 
--   ¬_ : Bool → Bool
--   ¬ p = p xor true
-- 
--   infixr 5 _∨_ 
--   _∨_ :  Bool → Bool → Bool
--   a ∨ b = ¬ ( (¬ a) ∧ (¬ b ) )
-- 
--   _=>_ :  Bool → Bool → Bool
--   a => b = (¬ a ) ∨ b 
-- 
--   open import Data.Bool.Solver using (module xor-∧-Solver)
--   open xor-∧-Solver
-- 
--   problem0' :  ( Cat : Bool ) → (Cat xor Cat ) ≡ false
--   problem0' = solve 1 (λ c → (c :+ c ) := con false ) refl
-- 
--   problem1' :  ( Cat : Bool ) → (Cat ∧ (Cat xor true ))  ≡ false 
--   problem1' = solve 1 (λ c → ((c :* (c :+ con true )) ) := con false ) {!!}
-- 
--   open import Data.Nat
--   :¬_ : {n : ℕ} → Polynomial n → Polynomial n
--   :¬ p = p :+ con true
-- 
--   _:∨_ : {n : ℕ} → Polynomial n → Polynomial n → Polynomial n
--   a :∨ b = :¬ ( ( :¬ a ) :* ( :¬ b ))
-- 
--   _:=>_ : {n : ℕ} → Polynomial n → Polynomial n → Polynomial n
--   a :=> b = ( :¬ a ) :∨ b 
-- 
--   _:∧_ = _:*_
-- 
--   infixr 6 _:∧_
--   infixr 5 _:∨_ 
-- 
--   problem0 :  ( Cat Dog Goat Rabbit : Bool ) →
--     ((( Cat ∨ Dog ) => (¬ Goat) ) ∧ ( (¬ Cat ) =>  ( Dog ∨ Rabbit ) ) ∧ ( ( ¬ ( Cat ∨ Goat ) ) =>  Rabbit ) )
--     => (Cat ∨ Dog ∨ Goat ∨ Rabbit) ≡ true
--   problem0 = solve 4 ( λ Cat Dog Goat Rabbit → (
--     ( ((Cat :∨ Dog ) :=> (:¬ Goat)) :∧ ( ((:¬ Cat ) :=>  ( Dog :∨ Rabbit )) :∧ (( :¬ ( Cat :∨ Goat ) ) :=>  Rabbit)  ))
--     :=> ( Cat :∨ (Dog :∨ ( Goat :∨ Rabbit))) ) := con true ) {!!}
-- 
--   problem1 :  ( Cat Dog Goat Rabbit : Bool ) →
--     ((( Cat ∨ Dog ) => (¬ Goat) ) ∧ ( (¬ Cat ) =>  ( Dog ∨ Rabbit ) ) ∧ ( ( ¬ ( Cat ∨ Goat ) ) =>  Rabbit ) )
--     => ( Goat => ( ¬ Dog )) ≡ true
--   problem1 c false false r = {!!}
--   problem1 c true false r = {!!}
--   problem1 c false true r = {!!}
--   problem1 false true true r = refl
--   problem1 true true true r = refl
-- 
--   problem2 :  ( Cat Dog Goat Rabbit : Bool ) →
--     ((( Cat ∨ Dog ) => (¬ Goat) ) ∧ ( (¬ Cat ) =>  ( Dog ∨ Rabbit ) ) ∧ ( ( ¬ ( Cat ∨ Goat ) ) =>  Rabbit ) )
--     => ( Goat => Rabbit ) ≡ true
--   problem2 c d false false = {!!}
--   problem2 c d false true = {!!}
--   problem2 c d true true = {!!}
--   problem2 true d true false = refl
--   problem2 false false true false = refl
--   problem2 false true true false = refl
-- 
--   problem3 :  ( Cat Dog Goat Rabbit : Bool ) →
--     ((( Cat ∨ Dog ) => (¬ Goat) ) ∧ ( (¬ Cat ) =>  ( Dog ∨ Rabbit ) ) ∧ ( ( ¬ ( Cat ∨ Goat ) ) =>  Rabbit ) )
--     => ( (¬ Rabbit ) => Cat ) ≡ true
--   problem3 false d g true = {!!}
--   problem3 true d g true = {!!}
--   problem3 true d g false = {!!}
--   problem3 false false false false = refl
--   problem3 false false true false = refl
--   problem3 false true false false = refl
--   problem3 false true true false = refl
