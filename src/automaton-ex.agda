module automaton-ex where

open import Data.Nat
open import Data.List
open import Data.Maybe
open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Nullary using (¬_; Dec; yes; no)
open import logic

open import automaton
open Automaton

data  StatesQ   : Set  where
   q1 : StatesQ
   q2 : StatesQ
   q3 : StatesQ

data  In2   : Set  where
   i0 : In2
   i1 : In2
transitionQ : StatesQ  → In2 → StatesQ
transitionQ q1 i0 = q1
transitionQ q1 i1 = q2
transitionQ q2 i0 = q3
transitionQ q2 i1 = q2
transitionQ q3 i0 = q2
transitionQ q3 i1 = q2

aendQ : StatesQ → Bool
aendQ q2 = true
aendQ _ = false

a1 : Automaton StatesQ In2
a1 = record {
       δ = transitionQ
     ; aend = aendQ
   }

test1 : accept a1 q1 ( i0 ∷ i1 ∷ i0 ∷ [] ) ≡ false
test1 = refl
test2 = accept a1 q1 ( i0 ∷ i1 ∷ i0 ∷ i1 ∷ [] ) 

data  States1   : Set  where
   sr : States1
   ss : States1
   st : States1

transition1 : States1  → In2  → States1
transition1 sr i0  = sr
transition1 sr i1  = ss
transition1 ss i0  = sr
transition1 ss i1  = st
transition1 st i0  = sr
transition1 st i1  = st

fin1 :  States1  → Bool
fin1 st = true
fin1 ss = false
fin1 sr = false

am1  :  Automaton  States1 In2
am1  =  record {  δ = transition1 ; aend = fin1   }


example1-1 = accept am1 sr ( i0  ∷ i1  ∷ i0  ∷ [] )
example1-2 = accept am1 sr ( i1  ∷ i1  ∷ i1  ∷ [] )
trace-2 = trace am1 sr ( i1  ∷ i1  ∷ i1  ∷ [] )

example1-3 = reachable am1 sr st ( i1  ∷ i1  ∷ i1  ∷ [] )

ieq : (i i' : In2 ) → Dec ( i ≡ i' )
ieq i0 i0 = yes refl
ieq i1 i1 = yes refl
ieq i0 i1 = no ( λ () )
ieq i1 i0 = no ( λ () )

