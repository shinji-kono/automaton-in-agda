module nfa136 where

open import logic
open import nfa
open import automaton 
open import Data.List
open import Data.Fin
open import  Relation.Binary.PropositionalEquality hiding ( [_] )

data  StatesQ   : Set  where
   q1 : StatesQ
   q2 : StatesQ
   q3 : StatesQ

data  A2   : Set  where
   a0 : A2
   b0 : A2

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

nfa136 :  NAutomaton  StatesQ A2
nfa136 =  record { Nδ = transition136; Nend = end136 }

states136 = q1 ∷ q2 ∷ q3 ∷ []

example136-1 = Naccept nfa136 exists136 start136( a0  ∷ b0  ∷ a0 ∷ a0 ∷ [] )

t146-1 = Ntrace nfa136 states136 exists136  start136( a0  ∷ b0  ∷ a0 ∷ a0 ∷ [] )

test111 = ?

example136-0 = Naccept nfa136 exists136 start136( a0 ∷ [] )

example136-2 = Naccept nfa136 exists136 start136( b0  ∷ a0  ∷ b0 ∷ a0 ∷ b0 ∷ [] )
t146-2 = Ntrace nfa136 states136 exists136  start136( b0  ∷ a0  ∷ b0 ∷ a0 ∷ b0 ∷ [] )

nx : (StatesQ → Bool) → (List A2 ) → StatesQ → Bool
nx now [] = now
nx now ( i ∷ ni ) = (Nmoves nfa136 exists136 (nx now ni) i )

example136-3 = to-list states136 start136
example136-4 = to-list states136 (nx start136  ( a0  ∷ b0 ∷ a0 ∷ [] ))

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

data  Σ2   : Set  where
   ca : Σ2
   cb : Σ2
   cc : Σ2
   cf : Σ2

data  Q2   : Set  where
   a0 : Q2
   a1 : Q2
   ae : Q2
   b0 : Q2
   b1 : Q2
   be : Q2

-- a.*f

aδ : Q2 → Σ2 → Q2 → Bool
aδ a0 ca a1 = true
aδ a0 _ _ = false
aδ a1 cf ae = true
aδ a1 _ a1 = true
aδ _ _ _ = false

a-end : Q2 → Bool
a-end ae = true
a-end _ = false

a-start : Q2 → Bool
a-start a0 = true
a-start _ = false

nfa-a : NAutomaton Q2 Σ2
nfa-a = record { Nδ = aδ ; Nend = a-end }

nfa-a-exists : (Q2 → Bool) → Bool
nfa-a-exists p = p a0 \/ p a1 \/ p ae

test-a1 : Bool
test-a1 = Naccept nfa-a nfa-a-exists a-start ( ca ∷ cf ∷ ca ∷ [] )

test-a2 = map reverse ( NtraceDepth nfa-a a-start (a0 ∷ a1 ∷ ae  ∷ [])  ( ca ∷ cf ∷ cf ∷ [] ) )

-- b.*f

bδ : Q2 → Σ2 → Q2 → Bool
bδ ae cb b1 = true
bδ ae _ _ = false
bδ b1 cf be = true
bδ b1 _ b1 = true
bδ _ _ _ = false

b-end : Q2 → Bool
b-end be = true
b-end _ = false

b-start : Q2 → Bool
b-start ae = true
b-start _ = false

nfa-b : NAutomaton Q2 Σ2
nfa-b = record { Nδ = bδ ; Nend = b-end }

nfa-b-exists : (Q2 → Bool) → Bool
nfa-b-exists p = p b0 \/ p b1 \/ p ae

-- (a.*f)(b.*f)

abδ : Q2 → Σ2 → Q2 → Bool
abδ x i y = aδ x i y \/ bδ x i y

nfa-ab : NAutomaton Q2 Σ2
nfa-ab = record { Nδ = abδ ; Nend = b-end }

nfa-ab-exists : (Q2 → Bool) → Bool
nfa-ab-exists p = nfa-a-exists p \/ nfa-b-exists p

test-ab1 : Bool
test-ab1 = Naccept nfa-a nfa-a-exists a-start ( ca ∷ cf ∷ ca ∷ cb ∷ cf ∷ [] )

test-ab2 : Bool
test-ab2 = Naccept nfa-a nfa-a-exists a-start ( ca ∷ cf ∷ ca ∷ cb ∷ cb ∷ [] )

test-ab3 = map reverse ( NtraceDepth nfa-ab a-start (a0 ∷ a1 ∷ ae  ∷ b0 ∷ b1 ∷ be  ∷ [])  ( ca ∷ cf ∷ ca ∷ cb ∷ cf ∷ [] ))

test112 : Automaton (Q2 → Bool) Σ2
test112 = subset-construction nfa-ab-exists nfa-ab

test114 = Automaton.δ (subset-construction nfa-ab-exists nfa-ab)

test113 : Bool
test113 = accept test112 a-start ( ca ∷ cf ∷ ca ∷ cb ∷ cb ∷ [] )

