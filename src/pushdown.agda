module pushdown where

open import Level renaming ( suc to succ ; zero to Zero )
open import Data.Nat
open import Data.List
open import Data.Maybe
open import Data.Bool using ( Bool ; true ; false )
open import  Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Level renaming ( suc to succ ; zero to Zero )
open import Data.Product


data PushDown   (  Γ : Set  ) : Set  where
   pop    : PushDown  Γ
   push   :  Γ → PushDown  Γ


record PushDownAutomaton ( Q : Set ) ( Σ : Set  ) ( Γ : Set  )
       : Set  where
    field
        pδ : Q → Σ →  Γ → Q × ( PushDown  Γ )
        pok : Q → Bool
        pempty : Γ
    pmoves :  Q → List  Γ  → Σ → ( Q × List  Γ )
    pmoves q [] i with pδ q i pempty
    pmoves q [] i | qn , pop = ( qn , [] )
    pmoves q [] i | qn , push x = ( qn , ( x ∷  [] ) )
    pmoves q (  H  ∷ T  ) i with pδ q i H
    pmoves q (H ∷ T) i | qn , pop =  ( qn , T )
    pmoves q (H ∷ T) i | qn , push x = ( qn , ( x ∷ H ∷ T) )

    paccept : (q : Q ) ( In : List  Σ ) ( sp : List   Γ ) → Bool
    paccept q [] [] = pok q
    paccept q ( H  ∷ T) [] with pδ q H pempty
    paccept q (H ∷ T) [] | qn , pop = paccept qn T []
    paccept q (H ∷ T) [] | qn , push x = paccept qn T (x  ∷ [] )
    paccept q [] (_ ∷ _ ) = false
    paccept q ( H  ∷ T ) ( SH  ∷ ST ) with pδ q H SH
    ... | (nq , pop )     = paccept nq T ST
    ... | (nq , push ns ) = paccept nq T ( ns  ∷  SH ∷ ST )


--  0011
--  00000111111
inputnn : ( n :  ℕ )  →  { Σ : Set  } → ( x y : Σ )  → List  Σ → List  Σ
inputnn zero {_} _ _ s = s
inputnn (suc n) x y s = x  ∷ ( inputnn n x y ( y  ∷ s ) )       


data  States0   : Set  where
   sr : States0

data  In2   : Set  where
   i0 : In2
   i1 : In2

test0 = inputnn 5 i0 i1 []
 
pnn : PushDownAutomaton States0 In2 States0
pnn = record {
         pδ  = pδ
      ;  pempty = sr
      ;  pok = λ q → true
   } where
        pδ  : States0 → In2 → States0 → States0 × PushDown States0
        pδ sr i0 _ = (sr , push sr) 
        pδ sr i1 _ = (sr , pop ) 

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
        pδ  : States1 → In2 → States1 → States1 × PushDown States1
        pδ ss i0 _ = (ss , push ss) 
        pδ ss i1 _ = (st , pop) 
        pδ st i0 _ = (st , push ss) 
        pδ st i1 _ = (st , pop ) 

test1 = PushDownAutomaton.paccept pnn sr ( i0 ∷ i0 ∷ i1 ∷ i1 ∷ [] ) []
test2 = PushDownAutomaton.paccept pnn sr ( i0 ∷ i0 ∷ i1 ∷ i0 ∷ [] ) []
test3 = PushDownAutomaton.pmoves pnn sr [] i0 
test4 = PushDownAutomaton.paccept pnn sr ( i0 ∷ i0 ∷ i1 ∷ i1 ∷ i0 ∷ i1 ∷ [] ) []

test5 = PushDownAutomaton.paccept pn1 ss ( i0 ∷ i0 ∷ i1 ∷ i1 ∷ [] ) []
test6 = PushDownAutomaton.paccept pn1 ss ( i0 ∷ i0 ∷ i1 ∷ i1 ∷ i0 ∷ i1 ∷ [] ) []

open import Data.Empty

test70 : (n : ℕ ) → (x : List In2) →  PushDownAutomaton.paccept pnn sr x [] ≡ true → inputnn n i0 i1 [] ≡ x
test70 zero [] refl = refl
test70 zero (x ∷ y) pa = ⊥-elim (test701 pa) where
   test701 : PushDownAutomaton.paccept pnn sr (x ∷ y) [] ≡ true → ⊥
   test701 pa with  PushDownAutomaton.pδ pnn sr x sr
   ... | sr , pop = {!!}
   ... | sr , push x = {!!}
test70 (suc n) x pa = {!!}

test71 : (n : ℕ ) → (x : List In2)  → inputnn n i0 i1 [] ≡ x →  PushDownAutomaton.paccept pnn sr x [] ≡ true
test71 = {!!}

test7 : (n : ℕ ) →  PushDownAutomaton.paccept pnn sr (inputnn n i0 i1 []) [] ≡ true
test7 zero = refl
test7 (suc n) with test7 n
... | t = test7lem [] t where
     test7lem : (x : List States0) → PushDownAutomaton.paccept pnn sr (inputnn n i0 i1 [])              x  ≡ true
                                   → PushDownAutomaton.paccept pnn sr (inputnn n i0 i1 (i1 ∷ [])) (sr ∷ x) ≡ true
     test7lem x with PushDownAutomaton.paccept pnn sr (inputnn (suc n) i0 i1 [])                (sr ∷ x)
     ... | t2 = {!!}
