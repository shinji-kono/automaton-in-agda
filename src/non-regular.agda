module non-regular where

open import Data.Nat
open import Data.Empty
open import Data.List
open import Data.Maybe hiding ( map )
open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import logic
open import automaton
open import automaton-ex
open import finiteSetUtil
open import finiteSet
open import Relation.Nullary 
open import regular-language

open FiniteSet

inputnn :  List  In2 → Maybe (List In2)
inputnn [] = just []
inputnn  (i1 ∷ t) = just (i1 ∷ t)
inputnn  (i0 ∷ t) with inputnn t
... | nothing = nothing
... | just [] = nothing
... | just (i0 ∷ t1) = nothing   -- can't happen
... | just (i1 ∷ t1) = just t1   -- remove i1 from later part

inputnn1 :  List  In2 → Bool
inputnn1  s with inputnn  s 
... | nothing = false
... | just [] = true
... | just _ = false

t1 = inputnn1 ( i0 ∷ i1 ∷ [] )
t2 = inputnn1 ( i0 ∷ i0 ∷ i1 ∷ i1 ∷ [] )
t3 = inputnn1 ( i0 ∷ i0 ∷ i0 ∷ i1 ∷ i1 ∷ [] )

inputnn0 : ( n :  ℕ )  →  { Σ : Set  } → ( x y : Σ ) → List  Σ → List  Σ 
inputnn0 zero {_} _ _ s = s
inputnn0 (suc n) x y s = x  ∷ ( inputnn0 n x y ( y  ∷ s ) )

t4 : inputnn1 ( inputnn0 5 i0 i1 [] ) ≡ true
t4 = refl

--
--  if there is an automaton with n states , which accespt inputnn1, it has a trasition function.
--  The function is determinted by inputs,
--

open RegularLanguage
open Automaton

open _∧_

data Trace { Q : Set } { Σ : Set  } (fa : Automaton Q  Σ ) : (is : List Σ) → ( List Q) → Set where
    tend  : {q : Q} → aend fa q ≡ true → Trace fa [] (q ∷ [])
    tnext : {q : Q} → {i : Σ} { is : List Σ} {qs : List Q} 
        → Trace fa is (δ fa q i  ∷ qs) → Trace fa (i ∷ is) ( q ∷ δ fa q i  ∷ qs ) 

tr-accept→ : { Q : Set } { Σ : Set  }
    → (fa : Automaton Q  Σ )
    → (is : List Σ) → (q : Q) → (qs : List Q) → Trace fa is (q ∷ qs) → accept fa q is ≡ true
tr-accept→ {Q} {Σ} fa [] q [] (tend x)  = x
tr-accept→ {Q} {Σ} fa (i ∷ is) q (x ∷ qs) (tnext tr) = tr-accept→ {Q} {Σ} fa is (δ fa q i) qs tr

tr-accept← : { Q : Set } { Σ : Set  }
    → (fa : Automaton Q  Σ )
    → (is : List Σ) → (q : Q)  → accept fa q is ≡ true → Trace fa is (trace fa q is)
tr-accept← {Q} {Σ} fa [] q ac = tend ac
tr-accept← {Q} {Σ} fa (x ∷ []) q ac = tnext (tend ac )
tr-accept← {Q} {Σ} fa (x ∷ x1 ∷ is) q ac = tnext (tr-accept← fa (x1 ∷ is)  (δ fa q x)  ac) 

open import Relation.Binary.HeterogeneousEquality as HE using (_≅_ ) 

record TA { Q : Set } { Σ : Set  } (fa : Automaton Q  Σ ) {is : List Σ} { qs : List Q } (tr : Trace fa is qs) : Set where
    field
       x y z : List Σ
       qx qy qz : List Q
       trace0 : Trace fa (x ++ y ++ z) (qx ++ qy ++ qz) 
       trace1 : Trace fa (x ++ y ++ y ++ z) (qx ++ qy ++ qy ++ qz) 
       trace-eq : trace0 ≅ tr

tr-append : { Q : Set } { Σ : Set  } (fa : Automaton Q  Σ ) (finq : FiniteSet Q) (q : Q) (is : List Σ) ( qs : List Q )
     →  dup-in-list finq q qs ≡ true
     →  (tr : Trace fa is qs ) → TA fa tr
tr-append {Q} {Σ} fa finq q is qs dup tr = tra-phase1 qs is tr dup where
   tra-phase3 : (qs : List Q) → (is : List Σ)  → (tr : Trace fa is qs ) → {!!}
        → (qy : List Q) → (iy : List Σ)  → (ty : Trace fa iy qy ) → phase2 finq q qy ≡ true → {!!}
        → Trace fa (iy ++ is) (qy ++ qs)
   tra-phase3 = {!!}
   tra-phase2 : (qs : List Q) → (is : List Σ)  → (tr : Trace fa is qs ) → phase2 finq q qs ≡ true
        → (qy : List Q) → (iy : List Σ)  → (ty : Trace fa iy qy ) → phase2 finq q qy ≡ true
        → TA fa tr
   tra-phase2 (q0 ∷ []) is (tend x₁) p qy iy ty py = {!!}
   tra-phase2 (q0 ∷ (q₁ ∷ qs)) (x ∷ is) (tnext tr) p qy iy ty py with equal? finq q q0
   ... | true = {!!}
   ... | false = {!!} where
       tr1 : TA fa tr
       tr1 = tra-phase2 (q₁ ∷ qs) is tr p qy iy ty py
   tra-phase1 : (qs : List Q) → (is : List Σ)  → (tr : Trace fa is qs ) → phase1 finq q qs ≡ true  → TA fa tr
   tra-phase1 (q0 ∷ []) is (tend x₁) p = {!!}
   tra-phase1 (q0 ∷ (q₁ ∷ qs)) (x ∷ is) (tnext tr) p with equal? finq q q0
   ... | true = {!!} where
       tr2 : TA fa tr
       tr2 = tra-phase2 (q₁ ∷ qs) is tr p (q₁ ∷ qs) is tr p
   ... | false = {!!} where
       tr1 : TA fa tr
       tr1 = tra-phase1 (q₁ ∷ qs) is tr p

open RegularLanguage

lemmaNN : (r : RegularLanguage In2 ) → ¬ ( (s : List In2)  → isRegular inputnn1  s r ) 
lemmaNN r Rg = {!!} where
    n : ℕ
    n = suc (finite (afin r))
    nn =  inputnn0 n i0 i1 []
    nn01  : (i : ℕ) → inputnn1 ( inputnn0 i i0 i1 [] ) ≡ true
    nn01  = {!!}
    nn03 : accept (automaton r) (astart r) nn ≡ true
    nn03 = {!!}
    nntrace = trace (automaton r) (astart r) nn
    nn04 :  Trace (automaton r) nn nntrace
    nn04 = tr-accept← (automaton r) nn (astart r) nn03 
    nn02 : TA (automaton r) nn04
    nn02 = tr-append (automaton r) (afin r) (Dup-in-list.dup nn05) _ _ (Dup-in-list.is-dup nn05) nn04 where
        nn05 : Dup-in-list ( afin r) nntrace
        nn05 = dup-in-list>n (afin r) nntrace {!!}
    
