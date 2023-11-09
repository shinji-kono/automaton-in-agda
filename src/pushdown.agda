{-# OPTIONS --cubical-compatible --safe #-}

module pushdown where

open import Level renaming ( suc to succ ; zero to Zero )
open import Data.Nat
open import Data.List
open import Data.Maybe
-- open import Data.Bool using ( Bool ; true ; false )
open import  Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Level renaming ( suc to succ ; zero to Zero )
-- open import Data.Product
open import logic
open import automaton


data PushDown   (  Γ : Set  ) : Set  where
   pop    : PushDown  Γ
   push   :  Γ → PushDown  Γ
   none   :  PushDown  Γ


record PushDownAutomaton ( Q : Set ) ( Σ : Set  ) ( Γ : Set  )
       : Set  where
    field
        pδ : Q → Σ →  Γ → Q ∧ ( PushDown  Γ )
        pok : Q → Bool
        pempty : Γ
    pmoves :  Q → List  Γ  → Σ → ( Q ∧ List  Γ )
    pmoves q [] i with pδ q i pempty
    pmoves q [] i | ⟪ qn , pop ⟫ =  ⟪  qn , [] ⟫
    pmoves q [] i | ⟪ qn , push x ⟫ =  ⟪ qn , ( x ∷  [] )  ⟫
    pmoves q [] i | ⟪ qn , none ⟫ =  ⟪ qn ,  [] ⟫
    pmoves q (  H  ∷ T  ) i with pδ q i H
    pmoves q (H ∷ T) i | ⟪ qn , pop ⟫ =  ⟪ qn , T  ⟫
    pmoves q (H ∷ T) i | ⟪ qn , none ⟫ =  ⟪ qn , (H ∷ T)  ⟫
    pmoves q (H ∷ T) i | ⟪ qn , push x ⟫ =  ⟪ qn ,  x ∷ H ∷ T  ⟫

    paccept : (q : Q ) ( In : List  Σ ) ( sp : List   Γ ) → Bool
    paccept q [] [] = pok q
    paccept q ( H  ∷ T) [] with pδ q H pempty
    paccept q (H ∷ T) [] | ⟪ qn , pop ⟫ = paccept qn T []
    paccept q (H ∷ T) [] | ⟪ qn , none ⟫ = paccept qn T []
    paccept q (H ∷ T) [] | ⟪ qn , push x ⟫ = paccept qn T (x  ∷ [] )
    paccept q [] (_ ∷ _ ) = false
    paccept q ( H  ∷ T ) ( SH  ∷ ST ) with pδ q H SH
    ... | ⟪ nq , pop ⟫     = paccept nq T ST
    ... | ⟪ nq , none ⟫    = paccept nq T (SH ∷ ST)
    ... | ⟪ nq , push ns ⟫ = paccept nq T ( ns  ∷  SH ∷ ST )

--
--        Automaton Q Σ
--             Automaton (Q → Bool  ) Σ
--             Automaton (Q ∧ List Q) Σ

record PDA ( Q : Set ) ( Σ : Set  ) ( Γ : Set  )
       : Set  where
    field
        automaton : Automaton Q Σ
        pδ : Q →  PushDown  Γ 
    open Automaton
    paccept : (q : Q ) ( In : List  Σ ) ( sp : List   Γ ) → Bool
    paccept q [] [] = aend automaton q 
    paccept q (H  ∷ T) [] with pδ  (δ automaton q H) 
    paccept q (H ∷ T) [] | pop     = paccept (δ automaton q H) T []
    paccept q (H ∷ T) [] | none    = paccept (δ automaton q H) T []
    paccept q (H ∷ T) [] | push x  = paccept (δ automaton q H) T (x  ∷ [] )
    paccept q [] (_ ∷ _ ) = false
    paccept q ( H  ∷ T ) ( SH  ∷ ST ) with pδ (δ automaton q H) 
    ... | pop      = paccept (δ automaton q H) T ST
    ... | none     = paccept (δ automaton q H) T (SH ∷ ST)
    ... | push ns  = paccept (δ automaton q H) T ( ns  ∷  SH ∷ ST )

data  States0   : Set  where
   sr : States0

data  In2   : Set  where
   i0 : In2
   i1 : In2

pnn : PushDownAutomaton States0 In2 States0
pnn = record {
         pδ  = pδ
      ;  pempty = sr
      ;  pok = λ q → true
   } where
        pδ  : States0 → In2 → States0 → States0 ∧ PushDown States0
        pδ sr i0 _ = ⟪ sr , push sr ⟫
        pδ sr i1 _ = ⟪ sr , pop  ⟫ 

data  States2   : Set  where
   ph1 : States2
   ph2 : States2
   phf : States2

pnnp : PDA States2 In2 States2
pnnp = record {
         automaton = record { aend = aend ; δ = δ }
       ; pδ  = pδ
   } where
        δ : States2 → In2 → States2
        δ ph1 i0 = ph1
        δ ph1 i1 = ph2
        δ ph2 i1 = ph2
        δ _ _ = phf
        aend : States2 → Bool
        aend ph2 = true
        aend _ = false
        pδ  : States2 → PushDown States2
        pδ ph1 = push ph1 
        pδ ph2 = pop   
        pδ phf = none   

data  States1   : Set  where
   ss : States1
   st : States1

pn1 : PushDownAutomaton States1 In2 States1
pn1 = record {
         pδ  = pδ
      ;  pempty = ss
      ;  pok = pok1
   } where
        pok1 :  States1 → Bool
        pok1 ss = false
        pok1 st = true
        pδ  : States1 → In2 → States1 → States1 ∧ PushDown States1
        pδ ss i0 _ = ⟪ ss , push ss ⟫ 
        pδ ss i1 _ = ⟪ st , pop ⟫ 
        pδ st i0 _ = ⟪ st , push ss ⟫ 
        pδ st i1 _ = ⟪ st , pop  ⟫ 

test1 = PushDownAutomaton.paccept pnn sr ( i0 ∷ i0 ∷ i1 ∷ i1 ∷ [] ) []
test2 = PushDownAutomaton.paccept pnn sr ( i0 ∷ i0 ∷ i1 ∷ i0 ∷ [] ) []
test3 = PushDownAutomaton.pmoves pnn sr [] i0 
test4 = PushDownAutomaton.paccept pnn sr ( i0 ∷ i0 ∷ i1 ∷ i1 ∷ i0 ∷ i1 ∷ [] ) []

test5 = PushDownAutomaton.paccept pn1 ss ( i0 ∷ i0 ∷ i1 ∷ i1 ∷ [] ) []
test6 = PushDownAutomaton.paccept pn1 ss ( i0 ∷ i0 ∷ i1 ∷ i1 ∷ i0 ∷ i1 ∷ [] ) []

