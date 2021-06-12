{-# OPTIONS --allow-unsolved-metas #-}
module nfa where

-- open import Level renaming ( suc to succ ; zero to Zero )
open import Data.Nat
open import Data.List
open import Data.Fin hiding ( _<_ )
open import Data.Maybe
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
    →  ( Qs : Q → Bool )  → (s : Σ ) → Q → Bool
Nmoves {Q} { Σ} M exists  Qs  s q  =
      exists ( λ qn → (Qs qn /\ ( Nδ M qn s q )  ))

Naccept : { Q : Set } { Σ : Set  } 
    → NAutomaton Q  Σ
    → (exists : ( Q → Bool ) → Bool)
    → (Nstart : Q → Bool) → List  Σ → Bool
Naccept M exists sb []  = exists ( λ q → sb q /\ Nend M q )
Naccept M exists sb (i ∷ t ) = Naccept M exists (λ q →  exists ( λ qn → (sb qn /\ ( Nδ M qn i q )  ))) t

Ntrace : { Q : Set } { Σ : Set  } 
    → NAutomaton Q  Σ
    → (exists : ( Q → Bool ) → Bool)
    → (to-list : ( Q → Bool ) → List Q )
    → (Nstart : Q → Bool) → List  Σ → List (List Q)
Ntrace M exists to-list sb []  = to-list ( λ q → sb q /\ Nend M q ) ∷ []
Ntrace M exists to-list sb (i ∷ t ) =
    to-list (λ q →  sb q ) ∷
    Ntrace M exists to-list (λ q →  exists ( λ qn → (sb qn /\ ( Nδ M qn i q )  ))) t


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
t-1 = Ntrace am2 existsS1 to-listS1 start1 ( i1  ∷ i1  ∷ i1  ∷ [] ) 
t-2 = Ntrace am2 existsS1 to-listS1 start1 ( i0  ∷ i1  ∷ i0  ∷ [] ) 

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

