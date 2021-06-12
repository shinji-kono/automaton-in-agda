module nfa136 where

open import logic
open import nfa
open import automaton 
open import Data.List
open import finiteSet
open import Data.Fin
open import  Relation.Binary.PropositionalEquality hiding ( [_] )

data  StatesQ   : Set  where
   q1 : StatesQ
   q2 : StatesQ
   q3 : StatesQ

data  A2   : Set  where
   a0 : A2
   b0 : A2

finStateQ : FiniteSet StatesQ 
finStateQ = record {
        Q←F = Q←F
      ; F←Q  = F←Q
      ; finiso→ = finiso→
      ; finiso← = finiso←
   } where
       Q←F : Fin 3 → StatesQ
       Q←F zero = q1
       Q←F (suc zero) = q2
       Q←F (suc (suc zero)) = q3
       F←Q : StatesQ → Fin 3
       F←Q q1 = zero
       F←Q q2 = suc zero
       F←Q q3 = suc (suc zero)
       finiso→ : (q : StatesQ) → Q←F (F←Q q) ≡ q
       finiso→ q1 = refl
       finiso→ q2 = refl
       finiso→ q3 = refl
       finiso← : (f : Fin 3) → F←Q (Q←F f) ≡ f
       finiso← zero = refl
       finiso← (suc zero) = refl
       finiso← (suc (suc zero)) = refl
       finiso← (suc (suc (suc ()))) 

transition136 : StatesQ  → A2  → StatesQ → Bool
transition136 q1 b0 q2 = true
transition136 q1 a0 q1 = true  -- q1 → ep → q3
transition136 q2 a0 q2 = true
transition136 q2 a0 q3 = true
transition136 q2 b0 q3 = true
transition136 q3 a0 q1 = true
transition136 _ _ _ = false

end136 : StatesQ → Bool
end136  q1 = true
end136  _ = false

start136 : StatesQ → Bool
start136 q1 = true
start136 _ = false

exists136 : (StatesQ → Bool) → Bool
exists136 f = f q1 \/ f q2 \/ f q3

to-list-136 : (StatesQ → Bool) → List StatesQ
to-list-136 f = tl1 where
   tl3 : List StatesQ 
   tl3 with f q3
   ... | true = q3 ∷  []
   ... | false = []
   tl2 : List StatesQ 
   tl2 with f q2
   ... | true = q2 ∷ tl3 
   ... | false = tl3
   tl1 : List StatesQ 
   tl1 with f q1
   ... | true = q1 ∷ tl2
   ... | false = tl2

nfa136 :  NAutomaton  StatesQ A2
nfa136 =  record { Nδ = transition136; Nend = end136 }

example136-1 = Naccept nfa136 exists136 start136( a0  ∷ b0  ∷ a0 ∷ a0 ∷ [] )

t146-1 = Ntrace nfa136 exists136 to-list-136 start136( a0  ∷ b0  ∷ a0 ∷ a0 ∷ [] )

example136-0 = Naccept nfa136 exists136 start136( a0 ∷ [] )

example136-2 = Naccept nfa136 exists136 start136( b0  ∷ a0  ∷ b0 ∷ a0 ∷ b0 ∷ [] )
t146-2 = Ntrace nfa136 exists136 to-list-136 start136( b0  ∷ a0  ∷ b0 ∷ a0 ∷ b0 ∷ [] )

open FiniteSet

nx : (StatesQ → Bool) → (List A2 ) → StatesQ → Bool
nx now [] = now
nx now ( i ∷ ni ) = (Nmoves nfa136 exists136 (nx now ni) i )

example136-3 = to-list-136 start136
example136-4 = to-list-136 (nx start136  ( a0  ∷ b0 ∷ a0 ∷ [] ))

open import sbconst2

fm136 : Automaton ( StatesQ → Bool  )  A2
fm136  = subset-construction exists136 nfa136 

open NAutomaton

lemma136 : ( x : List A2 ) → Naccept nfa136 exists136 start136 x  ≡ accept fm136 start136 x 
lemma136 x = lemma136-1 x start136 where
    lemma136-1 : ( x : List A2 ) → ( states : StatesQ → Bool )
        → Naccept nfa136 exists136 states x  ≡ accept fm136 states x 
    lemma136-1 [] _ = refl
    lemma136-1 (h ∷ t) states = lemma136-1 t (δconv exists136 (Nδ nfa136) states h)
