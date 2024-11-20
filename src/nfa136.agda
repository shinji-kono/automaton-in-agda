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

-- test111 = ?

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
   af : Q2
   b0 : Q2
   b1 : Q2
   be : Q2
   bf : Q2

-- a.*f

a-end : Q2 → Bool
a-end ae = true
a-end _ = false

aδ : Q2 → Σ2 → Q2 
aδ a0 ca = a1 
aδ a0 cb = af
aδ a0 cc = af
aδ a0 cf = af
aδ a1 cf = ae 
aδ a1 _ = a1 
aδ ae cf = ae 
aδ ae _ = a1 
aδ _ _ = af 
fa-a : Automaton Q2 Σ2
fa-a = record { δ = aδ ; aend = a-end }

test111 : Bool
test111 = accept fa-a a0 ( ca ∷ cf ∷ ca ∷ [] )

-- b.*f

b-end : Q2 → Bool
b-end be = true
b-end _ = false

bδ : Q2 → Σ2 → Q2 
bδ ae cb = b1 
bδ ae _ = bf 
bδ b1 cf = be 
bδ b1 _ = b1 
bδ be cf = be 
bδ be _ = b1 
bδ _ _ = bf 
fa-b : Automaton Q2 Σ2
fa-b = record { δ = bδ ; aend = b-end }

test115 : Bool
test115 = accept fa-b b0 ( cb ∷ cf ∷ cf ∷ [] )

open import regular-language

-- (a.*f)(b.*f)    -- a.*(fb).*f
test116 = split (accept fa-a a0) (accept fa-b b0) ( ca ∷ cf ∷ cb ∷ cf ∷ cf ∷ [] )
--                                                  a0   ae   b0   b1   be 
test117 = split (accept fa-a a0) (accept fa-b b0) ( ca ∷ cf ∷ ca ∷ cb ∷ ca ∷ cf ∷ cf ∷ [] )
--                                                  a0   ae   a0   b0   b1   be
--                                                  a0   ae   ae   b0   b1   be

naδ : Q2 → Σ2 → Q2 → Bool
naδ a0 ca a1 = true
naδ a0 _ _ = false
naδ a1 cf ae = true
naδ a1 _ a1 = true
naδ ae cf ae = true
naδ ae _ a1 = true
naδ _ _ _ = false

a-start : Q2 → Bool
a-start a0 = true
a-start _ = false

nfa-a : NAutomaton Q2 Σ2
nfa-a = record { Nδ = naδ ; Nend = a-end }

nfa-a-exists : (Q2 → Bool) → Bool
nfa-a-exists p = p a0 \/ p a1 \/ p ae

test-a1 : Bool
test-a1 = Naccept nfa-a nfa-a-exists a-start ( ca ∷ cf ∷ ca ∷ [] )

-- test-a2 = map reverse ( NtraceDepth nfa-a a-start (a0 ∷ a1 ∷ ae  ∷ [])  ( ca ∷ cf ∷ cf ∷ [] ) )

-- b.*f

nbδ : Q2 → Σ2 → Q2 → Bool
nbδ ae cb b1 = true
nbδ ae _ _ = false
nbδ b1 cf be = true
nbδ b1 _ b1 = true
nbδ be cf be = true
nbδ be _ b1 = true
nbδ _ _ _ = false

b-start : Q2 → Bool
b-start ae = true
b-start _ = false

nfa-b : NAutomaton Q2 Σ2
nfa-b = record { Nδ = nbδ ; Nend = b-end }

nfa-b-exists : (Q2 → Bool) → Bool
nfa-b-exists p = p b0 \/ p b1 \/ p be

-- (a.*f)(b.*f)

abδ : Q2 → Σ2 → Q2 → Bool
abδ x i y = naδ x i y \/ nbδ x i y

nfa-ab : NAutomaton Q2 Σ2
nfa-ab = record { Nδ = abδ ; Nend = b-end }

nfa-ab-exists : (Q2 → Bool) → Bool
nfa-ab-exists p = nfa-a-exists p \/ nfa-b-exists p

test-ab1-data : List Σ2
test-ab1-data = ( ca ∷ cf ∷ ca ∷ cb ∷ cf ∷ [] )

test-ab1 : Bool
test-ab1 = Naccept nfa-ab nfa-ab-exists a-start test-ab1-data  -- should be false

test-ab2-data : List Σ2
test-ab2-data = ( ca ∷ cf ∷ ca ∷ cf ∷ cb ∷ cb ∷ cf ∷ [] )

test-ab2 : Bool
test-ab2 = Naccept nfa-ab nfa-ab-exists a-start test-ab2-data   -- should be true

q2-list : List Q2
q2-list = a0 ∷ a1 ∷ ae ∷ af ∷ b0 ∷ b1 ∷ be ∷ bf ∷ []

test-tr : List (List Q2)
test-tr = Ntrace nfa-ab q2-list nfa-ab-exists a-start ( ca ∷ cf ∷ cf ∷ cb ∷ cb ∷ cf ∷ [] )

-- test-ab3 = map reverse ( NtraceDepth nfa-ab a-start (a0 ∷ a1 ∷ ae  ∷ b0 ∷ b1 ∷ be  ∷ [])  ( ca ∷ cf ∷ ca ∷ cb ∷ cf ∷ [] ))

test112 : Automaton (Q2 → Bool) Σ2
test112 = subset-construction nfa-ab-exists nfa-ab

test114 = Automaton.δ (subset-construction nfa-ab-exists nfa-ab)

test113 : Bool
test113 = accept test112 a-start ( ca ∷ cf ∷ ca ∷ cb ∷ cb ∷ [] )

-- 
open import regex
open import Relation.Nullary using (¬_; Dec; yes; no)

Σ2-cmp : (x y : Σ2 ) → Dec0 (x ≡ y)
Σ2-cmp ca ca = yes0 refl
Σ2-cmp ca cb = no0 (λ ())
Σ2-cmp ca cc = no0 (λ ())    
Σ2-cmp ca cf = no0 (λ ())    
Σ2-cmp cb ca =  no0 (λ ())
Σ2-cmp cb cb = yes0 refl
Σ2-cmp cb cc =  no0 (λ ())
Σ2-cmp cb cf =  no0 (λ ())
Σ2-cmp cc ca =  no0 (λ ())
Σ2-cmp cc cb =  no0 (λ ())
Σ2-cmp cc cc = yes0 refl
Σ2-cmp cc cf =  no0 (λ ())
Σ2-cmp cf ca =  no0 (λ ())
Σ2-cmp cf cb =  no0 (λ ())
Σ2-cmp cf cc =  no0 (λ ())
Σ2-cmp cf cf = yes0 refl

Σ2-any :  Regex Σ2
Σ2-any = < ca > || < cb > || < cc > || < cf >

test-ab1-regex : regex-language ( (< ca > & (Σ2-any *) & < cf > ) & (< cb > & (Σ2-any *) & < cf > )  )  Σ2-cmp test-ab1-data ≡ false
test-ab1-regex = refl

test-ab2-regex : regex-language ( (< ca > & (Σ2-any *) & < cf > ) & (< cb > & (Σ2-any *) & < cf > )  )  Σ2-cmp test-ab2-data ≡ true
test-ab2-regex = refl




