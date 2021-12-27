{-# OPTIONS --allow-unsolved-metas #-}
module nfa where

-- open import Level renaming ( suc to succ ; zero to Zero )
open import Data.Nat
open import Data.List
open import Data.Fin hiding ( _<_ )
open import Data.Maybe hiding ( zip )
open import Relation.Nullary
open import Data.Empty
-- open import Data.Bool using ( Bool ; true ; false ; _∧_ ; _∨_ )
open import  Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Nullary using (¬_; Dec; yes; no)
open import logic

data  States1   : Set  where
   sr : States1
   ss : States1
   st : States1

data  In2   : Set  where
   i0 : In2
   i1 : In2


record NAutomaton ( Q : Set ) ( Σ : Set  )
       : Set  where
    field
          Nδ : Q → Σ → Q → Bool
          Nend  :  Q → Bool

open NAutomaton

LStates1 : List States1
LStates1 = sr ∷ ss ∷ st ∷ []

-- one of qs q is true
existsS1 : ( States1 → Bool ) → Bool            
existsS1 qs = qs sr \/ qs ss \/ qs st

-- extract list of q which qs q is true
to-listS1 : ( States1 → Bool ) → List States1
to-listS1 qs = ss1 LStates1 where
   ss1 : List States1 → List States1
   ss1 [] = []
   ss1 (x ∷ t) with qs x
   ... | true   = x ∷ ss1 t
   ... | false  = ss1 t 

Nmoves : { Q : Set } { Σ : Set  }
    → NAutomaton Q  Σ
    → (exists : ( Q → Bool ) → Bool)
    →  ( Qs : Q → Bool )  → (s : Σ ) → ( Q → Bool )
Nmoves {Q} { Σ} M exists  Qs  s  = λ q → exists ( λ qn → (Qs qn /\ ( Nδ M qn s q )  ))

Naccept : { Q : Set } { Σ : Set  } 
    → NAutomaton Q  Σ
    → (exists : ( Q → Bool ) → Bool)
    → (Nstart : Q → Bool) → List  Σ → Bool
Naccept M exists sb []  = exists ( λ q → sb q /\ Nend M q )
Naccept M exists sb (i ∷ t ) = Naccept M exists (λ q →  exists ( λ qn → (sb qn /\ ( Nδ M qn i q )  ))) t

{-# TERMINATING #-}
NtraceDepth : { Q : Set } { Σ : Set  } 
    → NAutomaton Q  Σ
    → (Nstart : Q → Bool) → List Q  → List  Σ → List (List ( Σ ∧ Q ))
NtraceDepth {Q} {Σ} M sb all is = ndepth all sb is [] [] where
    ndepth : List Q → (q : Q → Bool ) → List Σ  → List ( Σ ∧ Q )  →  List (List ( Σ ∧ Q )  ) →  List (List ( Σ ∧ Q )  )
    ndepth1 : Q → Σ → List Q →  List Σ  → List ( Σ ∧ Q )  →  List ( List ( Σ ∧ Q )) →  List ( List ( Σ ∧ Q ))
    ndepth1 q i [] is t t1 = t1
    ndepth1 q i (x ∷ qns) is t t1 =  ndepth all (Nδ M x i) is (⟪ i , q ⟫ ∷ t) (ndepth1 q i qns is t t1 )
    ndepth [] sb is t t1 =  t1
    ndepth (q ∷ qs) sb [] t t1 with sb q /\ Nend M q
    ... | true =  ndepth qs sb [] t ( t  ∷ t1 )
    ... | false =  ndepth qs sb [] t t1
    ndepth (q ∷ qs) sb (i ∷ is) t t1 with sb q 
    ... | true  = ndepth qs sb (i ∷ is) t (ndepth1 q i all is t t1 )
    ... | false = ndepth qs sb (i ∷ is) t t1

-- trace in state set
--
Ntrace : { Q : Set } { Σ : Set  } 
    → NAutomaton Q  Σ
    → (exists : ( Q → Bool ) → Bool)
    → (to-list : ( Q → Bool ) → List Q )
    → (Nstart : Q → Bool) → List  Σ → List (List Q)
Ntrace M exists to-list sb []  = to-list ( λ q → sb q /\ Nend M q ) ∷ []
Ntrace M exists to-list sb (i ∷ t ) =
    to-list (λ q →  sb q ) ∷
    Ntrace M exists to-list (λ q →  exists ( λ qn → (sb qn /\ ( Nδ M qn i q )  ))) t

data-fin-00 : ( Fin 3 ) → Bool 
data-fin-00 zero = true
data-fin-00 (suc zero) = true
data-fin-00 (suc (suc zero)) = true
data-fin-00 (suc (suc (suc ()))) 

data-fin-01 :  (x : ℕ ) → x < 3 → Bool 
data-fin-01 zero lt = true
data-fin-01 (suc zero) lt = true
data-fin-01 (suc (suc zero)) lt = true
data-fin-01 (suc (suc (suc x))) (s≤s (s≤s (s≤s ())))

transition3 : States1  → In2  → States1 → Bool
transition3 sr i0 sr = true
transition3 sr i1 ss = true
transition3 sr i1 sr = true
transition3 ss i0 sr = true
transition3 ss i1 st = true
transition3 st i0 sr = true
transition3 st i1 st = true
transition3 _ _ _ = false

fin1 :  States1  → Bool
fin1 st = true
fin1 ss = false
fin1 sr = false

test5 = existsS1  (λ q → fin1 q )
test6 = to-listS1 (λ q → fin1 q )

start1 : States1 → Bool
start1 sr = true
start1 _ = false

am2  :  NAutomaton  States1 In2
am2  =  record { Nδ = transition3 ; Nend = fin1}

example2-1 = Naccept am2 existsS1 start1 ( i0  ∷ i1  ∷ i0  ∷ [] ) 
example2-2 = Naccept am2 existsS1 start1 ( i1  ∷ i1  ∷ i1  ∷ [] ) 

t-1 : List ( List States1 )
t-1 = Ntrace am2 existsS1 to-listS1 start1 ( i1  ∷ i1  ∷ i1  ∷ [] )  -- (sr ∷ []) ∷ (sr ∷ ss ∷ []) ∷ (sr ∷ ss ∷ st ∷ []) ∷ (st ∷ []) ∷ []
t-2 = Ntrace am2 existsS1 to-listS1 start1 ( i0  ∷ i1  ∷ i0  ∷ [] )  -- (sr ∷ []) ∷ (sr ∷ []) ∷ (sr ∷ ss ∷ []) ∷ [] ∷ []
t-3 = NtraceDepth am2 start1 LStates1 ( i1  ∷ i1  ∷ i1  ∷ [] ) 
t-4 = NtraceDepth am2 start1 LStates1 ( i0  ∷ i1  ∷ i0  ∷ [] ) 
t-5 = NtraceDepth am2 start1 LStates1 ( i0  ∷ i1 ∷ [] ) 

transition4 : States1  → In2  → States1 → Bool
transition4 sr i0 sr = true
transition4 sr i1 ss = true
transition4 sr i1 sr = true
transition4 ss i0 ss = true
transition4 ss i1 st = true
transition4 st i0 st = true
transition4 st i1 st = true
transition4 _ _ _ = false

fin4 :  States1  → Bool
fin4 st = true
fin4 _ = false

start4 : States1 → Bool
start4 ss = true
start4 _ = false

am4  :  NAutomaton  States1 In2
am4  =  record { Nδ = transition4 ; Nend = fin4}

example4-1 = Naccept am4 existsS1 start4 ( i0  ∷ i1  ∷ i1  ∷ i0 ∷ [] ) 
example4-2 = Naccept am4 existsS1 start4 ( i0  ∷ i1  ∷ i1  ∷ i1 ∷ [] ) 

fin0 :  States1  → Bool
fin0 st = false
fin0 ss = false
fin0 sr = false

test0 : Bool
test0 = existsS1 fin0

test1 : Bool
test1 = existsS1 fin1

test2 = Nmoves am2 existsS1 start1 

open import automaton 

am2def  :  Automaton (States1 → Bool )  In2
am2def  =  record { δ    = λ qs s q → existsS1 (λ qn → qs q /\ Nδ am2 q s qn )
                  ; aend = λ qs     → existsS1 (λ q → qs q /\ Nend am2  q) } 

dexample4-1 = accept am2def start1 ( i0  ∷ i1  ∷ i1  ∷ i0 ∷ [] ) 
texample4-1 = trace am2def start1 ( i0  ∷ i1  ∷ i1  ∷ i0 ∷ [] ) 

-- LStates1 contains all states in States1

-- a list of Q contains (q : Q)

eqState1? : (x y : States1)  →  Dec ( x ≡ y )
eqState1? sr sr = yes refl
eqState1? ss ss = yes refl
eqState1? st st = yes refl
eqState1? sr ss = no (λ ())
eqState1? sr st = no (λ ())
eqState1? ss sr = no (λ ())
eqState1? ss st = no (λ ())
eqState1? st sr = no (λ ())
eqState1? st ss = no (λ ())


list-contains  : {Q : Set} → ( (x y : Q ) → Dec ( x ≡ y ) ) → (qs : List Q) → (q : Q ) → Bool
list-contains {Q} eq? [] q = false
list-contains {Q} eq? (x ∷ qs) q with eq? x q
... | yes _  = true
... | no _  = list-contains eq? qs q

containsP : {Q : Set} → ( eq? : (x y : Q ) →  Dec ( x ≡ y ))  → (qs : List Q) → (q : Q ) → Set 
containsP eq? qs q = list-contains eq? qs q ≡ true

contains-all : (q : States1 ) → containsP eqState1? LStates1 q 
contains-all sr = refl
contains-all ss = refl
contains-all st = refl

-- foldr : (A → B → B) → B → List A → B
-- foldr c n []       = n
-- foldr c n (x ∷ xs) = c x (foldr c n xs)

ssQ : {Q : Set } ( qs : Q → Bool ) → List Q → List Q
ssQ qs [] = []
ssQ qs (x ∷ t) with qs x
... | true   = x ∷ ssQ qs t
... | false  = ssQ qs t 

bool-t1 : {b : Bool } → b ≡ true → (true /\ b)  ≡ true
bool-t1 refl = refl

bool-1t : {b : Bool } → b ≡ true → (b /\ true)  ≡ true
bool-1t refl = refl

to-list1 : {Q : Set } (qs : Q → Bool ) →  (all : List Q) → foldr (λ q x → qs q /\ x ) true (ssQ  qs all ) ≡ true
to-list1 qs []  = refl
to-list1 qs (x ∷ all)  with qs x  | inspect qs x
... | false | record { eq = eq } = to-list1 qs all 
... | true  | record { eq = eq } = subst (λ k → k /\ foldr (λ q → _/\_ (qs q)) true (ssQ qs all) ≡ true ) (sym eq) ( bool-t1 (to-list1 qs all) )

existsS1-valid : ¬ ( (qs : States1 → Bool ) →  ( existsS1 qs ≡ true ) )
existsS1-valid n = ¬-bool refl ( n ( λ x → false ))

--
--  using finiteSet
--

open import finiteSet
open import finiteSetUtil
open FiniteSet

allQ : {Q : Set } (finq : FiniteSet Q) → List Q
allQ {Q} finq = to-list finq (λ x → true)

existQ : {Q : Set } (finq : FiniteSet Q) → (Q → Bool) → Bool
existQ finq qs = exists finq qs

eqQ? : {Q : Set } (finq : FiniteSet Q) → (x y : Q ) → Bool
eqQ? finq x y = equal? finq x y

finState1 : FiniteSet States1
finState1 = record {
     finite = finite0
   ; Q←F = Q←F0 
   ; F←Q = F←Q0 
   ; finiso→ = finiso→0
   ; finiso← = finiso←0
 } where
     finite0 : ℕ
     finite0 = 3
     Q←F0 : Fin finite0 → States1
     Q←F0 zero = sr
     Q←F0 (suc zero) = ss
     Q←F0 (suc (suc zero)) = st
     F←Q0 : States1 → Fin finite0
     F←Q0 sr = # 0
     F←Q0 ss = # 1
     F←Q0 st = # 2
     finiso→0 : (q : States1) → Q←F0 ( F←Q0 q ) ≡ q
     finiso→0 sr = refl
     finiso→0 ss = refl
     finiso→0 st = refl
     finiso←0 : (f : Fin finite0 ) → F←Q0 ( Q←F0 f ) ≡ f
     finiso←0 zero = refl
     finiso←0 (suc zero) = refl
     finiso←0 (suc (suc zero)) = refl

