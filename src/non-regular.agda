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
open import nat


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

t5 : ( n : ℕ ) → Set
t5 n = inputnn1 ( inputnn0 n i0 i1 [] ) ≡ true

nn01  : (i : ℕ) → inputnn1 ( inputnn0 i i0 i1 [] ) ≡ true
nn01 zero = refl
nn01 (suc i) = {!!} where 
      nn02 : (i : ℕ) → ( x : List In2) → inputnn ( inputnn0 i i0 i1 x ) ≡ inputnn x
      nn02 zero _ = refl
      nn02 (suc i) x with inputnn (inputnn0 (suc i) i0 i1 x)
      ... | nothing = {!!}
      ... | just []  = {!!}
      ... | just (i0 ∷ t1)   = {!!}
      ... | just (i1 ∷ t1)   = {!!}
--
--  if there is an automaton with n states , which accespt inputnn1, it has a trasition function.
--  The function is determinted by inputs,
--

open RegularLanguage
open Automaton

open _∧_

data Trace { Q : Set } { Σ : Set  } (fa : Automaton Q  Σ ) : (is : List Σ) → Q → Set where
    tend  : {q : Q} → aend fa q ≡ true → Trace fa [] q
    tnext : (q : Q) → {i : Σ} { is : List Σ} 
        → Trace fa is (δ fa q i) → Trace fa (i ∷ is) q 

tr-len :  { Q : Set } { Σ : Set  }
    → (fa : Automaton Q  Σ )
    → (is : List Σ) → (q : Q) → Trace fa is q → suc (length is) ≡ length (trace fa q is ) 
tr-len {Q} {Σ} fa .[] q (tend x) = refl 
tr-len {Q} {Σ} fa (i ∷ is) q (tnext .q t) = cong suc (tr-len {Q} {Σ} fa is (δ fa q i) t)

tr-accept→ : { Q : Set } { Σ : Set  }
    → (fa : Automaton Q  Σ )
    → (is : List Σ) → (q : Q) → Trace fa is q → accept fa q is ≡ true
tr-accept→ {Q} {Σ} fa [] q (tend x)  = x
tr-accept→ {Q} {Σ} fa (i ∷ is) q  (tnext _ tr) = tr-accept→ {Q} {Σ} fa is (δ fa q i) tr

tr-accept← : { Q : Set } { Σ : Set  }
    → (fa : Automaton Q  Σ )
    → (is : List Σ) → (q : Q)  → accept fa q is ≡ true → Trace fa is q
tr-accept← {Q} {Σ} fa [] q ac = tend ac
tr-accept← {Q} {Σ} fa (x ∷ []) q ac = tnext _ (tend ac )
tr-accept← {Q} {Σ} fa (x ∷ x1 ∷ is) q ac = tnext _ (tr-accept← fa (x1 ∷ is)  (δ fa q x)  ac) 

tr→qs : { Q : Set } { Σ : Set  }
    → (fa : Automaton Q  Σ )
    → (is : List Σ) → (q : Q) → Trace fa is q → List Q
tr→qs fa [] q (tend x) = []
tr→qs fa (i ∷ is) q (tnext q tr) = q ∷ tr→qs fa is (δ fa q i) tr 

tr→qs=is : { Q : Set } { Σ : Set  }
    → (fa : Automaton Q  Σ )
    → (is : List Σ) → (q : Q) → (tr : Trace fa is q ) → length is ≡  length (tr→qs fa is q tr)
tr→qs=is fa .[] q (tend x) = refl
tr→qs=is fa (i ∷ is) q (tnext .q tr) = cong suc (tr→qs=is fa is  (δ fa q i) tr)

open Data.Maybe

open import Relation.Binary.HeterogeneousEquality as HE using (_≅_ ) 
open import Relation.Binary.Definitions
open import Data.Unit using (⊤ ; tt)
open import Data.Nat.Properties

data QDSEQ { Q : Set } { Σ : Set  } { fa : Automaton  Q  Σ} ( finq : FiniteSet Q) (qd : Q) (z1 :  List Σ) :
       {q : Q} {y2 : List Σ} → Trace fa (y2 ++ z1) q → Set where
   qd-nil :  (q : Q) → (tr : Trace fa z1 q) → equal? finq qd q ≡ true → QDSEQ finq qd z1 tr
   qd-next : {i : Σ} (y2 : List Σ) → (q : Q) → (tr : Trace fa (y2 ++ z1) (δ fa q i)) → equal? finq qd q ≡ false
       → QDSEQ finq qd z1 tr 
       → QDSEQ finq qd z1 (tnext q tr)

record TA1 { Q : Set } { Σ : Set  } (fa : Automaton Q  Σ ) (finq : FiniteSet Q)  ( q qd : Q ) (is : List Σ)  : Set where
    field
       y z : List Σ
       yz=is : y ++ z ≡ is 
       trace-z    : Trace fa z  qd
       trace-yz   : Trace fa (y ++ z)  q
       q=qd : QDSEQ finq qd z trace-yz

--
-- using accept ≡ true may simplify the pumping-lemma
-- QDSEQ is too complex, should we generate (lengty y ≡ 0 → equal ) ∧  ...
--
-- like this ...
-- record TA2 { Q : Set } { Σ : Set  } (fa : Automaton Q  Σ ) (finq : FiniteSet Q)  ( q qd : Q ) (is : List Σ)  : Set where
--     field
--        y z : List Σ
--        yz=is : y ++ z ≡ is 
--        trace-z    : accpet fa z qd ≡ true
--        trace-yz   : accept fa (y ++ z)  q ≡ true
--        q=qd  : last (tr→qs fa q trace-yz) ≡ just qd 
--        ¬q=qd : non-last (tr→qs fa q trace-yz) ≡ just qd 

record TA { Q : Set } { Σ : Set  } (fa : Automaton Q  Σ )   ( q : Q ) (is : List Σ)  : Set where
    field
       x y z : List Σ
       xyz=is : x ++ y ++ z ≡ is 
       trace-xyz  : Trace fa (x ++ y ++ z)  q
       trace-xyyz : Trace fa (x ++ y ++ y ++ z) q
       non-nil-y : ¬ (y ≡ [])

pumping-lemma : { Q : Set } { Σ : Set  } (fa : Automaton Q  Σ ) (finq : FiniteSet Q) (q qd : Q) (is : List Σ) 
     → (tr : Trace fa is q )
     → dup-in-list finq qd (tr→qs fa is q tr) ≡ true
     → TA fa q is
pumping-lemma {Q} {Σ} fa finq q qd is tr dup = tra-phase1 q is tr dup where
   open TA
   tra-phase2 : (q : Q)  → (is : List Σ)  → (tr : Trace fa is  q )
       → phase2 finq qd (tr→qs fa is q tr) ≡ true → TA1 fa finq q qd is
   tra-phase2 q (i ∷ is) (tnext q tr) p with equal? finq qd q | inspect ( equal? finq qd) q
   ... | true | record { eq = eq } = record { y = [] ; z = i ∷ is ; yz=is = refl ; q=qd = qd-nil q (tnext q tr) eq
        ; trace-z  = subst (λ k → Trace fa (i ∷ is) k ) (sym (equal→refl finq eq)) (tnext q tr) ; trace-yz = tnext q tr }
   ... | false | record { eq = ne } = record { y = i ∷ TA1.y ta ; z = TA1.z ta ; yz=is = cong (i ∷_ ) (TA1.yz=is ta )
       ; q=qd = tra-08
       ; trace-z = TA1.trace-z ta ; trace-yz = tnext q ( TA1.trace-yz ta ) } where
            ta : TA1 fa finq (δ fa q i) qd is
            ta = tra-phase2 (δ fa q i) is tr p 
            tra-07 : Trace fa (TA1.y ta ++ TA1.z ta) (δ fa q i)
            tra-07 = subst (λ k → Trace fa k (δ fa q i)) (sym (TA1.yz=is ta)) tr
            tra-08 : QDSEQ finq qd (TA1.z ta) (tnext q (TA1.trace-yz ta))
            tra-08 = qd-next (TA1.y ta) q (TA1.trace-yz (tra-phase2 (δ fa q i) is tr p))  ne (TA1.q=qd ta)
   tra-phase1 : (q : Q)  → (is : List Σ)  → (tr : Trace fa is  q ) → phase1 finq qd (tr→qs fa is q tr) ≡ true  → TA fa q is
   tra-phase1 q (i ∷ is) (tnext q tr) p with equal? finq qd q | inspect (equal? finq qd) q
   ... | true | record { eq = eq } = record { x = [] ; y = i ∷ TA1.y ta ;  z = TA1.z ta ; xyz=is =  cong (i ∷_ ) (TA1.yz=is ta)
           ; non-nil-y = λ ()
           ; trace-xyz  = tnext q (TA1.trace-yz ta)
           ; trace-xyyz = tnext q tra-05 } where
        ta : TA1 fa finq (δ fa q i ) qd is
        ta = tra-phase2 (δ fa q i ) is tr p 
        y1 = TA1.y ta
        z1 = TA1.z ta
        tryz0 : Trace fa (y1 ++ z1) (δ fa qd i)
        tryz0 = subst₂ (λ j k → Trace fa k (δ fa j i) ) (sym (equal→refl finq eq)) (sym (TA1.yz=is ta)) tr
        tryz : Trace fa (i ∷ y1 ++ z1) qd
        tryz = tnext qd tryz0
        -- create Trace (y ++ y ++ z)
        tra-04 : (y2 : List Σ) → (q : Q) → (tr : Trace fa (y2 ++ z1) q)
               →  QDSEQ finq qd z1 {q} {y2} tr 
               → Trace fa (y2 ++ (i ∷ y1) ++ z1) q
        tra-04 [] q tr (qd-nil q _ x₁) with equal? finq qd q | inspect (equal? finq qd) q
        ... | true | record { eq = eq } = subst (λ k → Trace fa (i ∷ y1 ++ z1) k) (equal→refl finq eq) tryz
        ... | false | record { eq = ne } = ⊥-elim ( ¬-bool  refl x₁ ) 
        tra-04 (y0 ∷ y2) q (tnext q tr) (qd-next _ _  _ x₁ qdseq) with equal? finq qd q | inspect (equal? finq qd) q
        ... | true | record { eq = eq } = ⊥-elim ( ¬-bool x₁ refl ) 
        ... | false | record { eq = ne } = tnext q (tra-04 y2 (δ fa q y0) tr qdseq ) 
        tra-05 : Trace fa (TA1.y ta ++ (i ∷ TA1.y ta) ++ TA1.z ta) (δ fa q i)
        tra-05 with equal→refl finq eq
        ... | refl = tra-04 y1  (δ fa qd i) (TA1.trace-yz ta) (TA1.q=qd ta)
   ... | false | _ = record { x = i ∷ x ta ; y = y ta ; z = z ta ; xyz=is = cong (i ∷_ ) (xyz=is ta) 
           ; non-nil-y = non-nil-y ta
            ; trace-xyz = tnext q (trace-xyz ta ) ; trace-xyyz = tnext q (trace-xyyz ta )} where
        ta : TA fa (δ fa q i ) is
        ta = tra-phase1 (δ fa q i ) is tr p

open RegularLanguage
open import Data.Nat.Properties
open import nat

lemmaNN : (r : RegularLanguage In2 ) → ¬ ( (s : List In2)  → isRegular inputnn1  s r ) 
lemmaNN r Rg = tann {TA.x TAnn} (TA.non-nil-y TAnn ) {!!} (tr-accept→ (automaton r) _  (astart r) (TA.trace-xyz TAnn) )
       (tr-accept→ (automaton r) _  (astart r) (TA.trace-xyyz TAnn) ) where
    n : ℕ
    n = suc (finite (afin r))
    nn =  inputnn0 n i0 i1 []
    nn03 : accept (automaton r) (astart r) nn ≡ true
    nn03 = subst (λ k → k ≡ true ) (Rg nn ) (nn01 n)
    nn09 : (n m : ℕ) → n ≤ n + m
    nn09 zero m = z≤n
    nn09 (suc n) m = s≤s (nn09 n m)
    nn04 :  Trace (automaton r) nn (astart r)
    nn04 = tr-accept← (automaton r) nn (astart r) nn03 
    nntrace = tr→qs (automaton r) nn (astart r) nn04
    nn07 : (n : ℕ) →  length (inputnn0 n i0 i1 []) ≡ n + n 
    nn07 n = subst (λ k → length (inputnn0 n i0 i1 []) ≡ k) (+-comm (n + n) _ ) (nn08 n [] )where
       nn08 : (n : ℕ) → (s : List In2) → length (inputnn0 n i0 i1 s) ≡ n + n + length s
       nn08 zero s = refl
       nn08 (suc n) s = begin
         length (inputnn0 (suc n) i0 i1 s) ≡⟨ refl ⟩
         suc (length (inputnn0 n i0 i1 (i1 ∷ s))) ≡⟨ cong suc (nn08 n (i1 ∷ s)) ⟩
         suc (n + n + suc (length s)) ≡⟨ +-assoc (suc n) n _  ⟩
         suc n + (n + suc (length s)) ≡⟨ cong (λ k → suc n + k) (sym (+-assoc n  _ _))  ⟩
         suc n + ((n + 1) + length s) ≡⟨ cong (λ k → suc n + (k + length s)) (+-comm n _) ⟩
         suc n + (suc n + length s) ≡⟨ sym (+-assoc (suc n)  _ _) ⟩
         suc n + suc n + length s  ∎  where open ≡-Reasoning
    nn05 : length nntrace > finite (afin r)
    nn05 = begin
         suc (finite (afin r))  ≤⟨ nn09 _ _ ⟩
         n + n   ≡⟨ sym (nn07 n) ⟩
         length (inputnn0 n i0 i1 []) ≡⟨ tr→qs=is (automaton r) (inputnn0 n i0 i1 []) (astart r) nn04 ⟩
         length nntrace ∎  where open ≤-Reasoning
    nn06 : Dup-in-list ( afin r) (tr→qs (automaton r) nn (astart r) nn04)
    nn06 = dup-in-list>n (afin r) nntrace nn05
    TAnn : TA (automaton r) (astart r) nn
    TAnn = pumping-lemma (automaton r) (afin r) (astart r) (Dup-in-list.dup nn06) nn nn04 (Dup-in-list.is-dup nn06)
    count : In2 → List In2 → ℕ
    count _ [] = 0
    count i0 (i0 ∷ s) = suc (count i0 s)
    count i1 (i1 ∷ s) = suc (count i1 s)
    count x (_ ∷ s) = count x s
    nn11 : {x : In2} → (s t : List In2) → count x (s ++ t) ≡ count x s + count x t
    nn11 {x} [] t = refl
    nn11 {i0} (i0 ∷ s) t = cong suc ( nn11 s t )
    nn11 {i0} (i1 ∷ s) t = nn11 s t 
    nn11 {i1} (i0 ∷ s) t = nn11 s t 
    nn11 {i1} (i1 ∷ s) t = cong suc ( nn11 s t )
    nn10 : (s : List In2) → accept (automaton r) (astart r) s ≡ true → count i0 s ≡ count i1 s
    nn10 s p = nn101 s (subst (λ k → k ≡ true) (sym (Rg s)) p ) where
        nn101 : (s : List In2) → inputnn1 s ≡ true →  count i0 s ≡ count i1 s
        nn101 [] p = refl
        nn101 (x ∷ s) p = {!!}
    i1-i0? : List In2 → Bool
    i1-i0? [] = false
    i1-i0? (i1 ∷ []) = false
    i1-i0? (i0 ∷ []) = false
    i1-i0? (i1 ∷ i0 ∷ s) = true
    i1-i0? (_ ∷ s0 ∷ s1) = i1-i0? (s0 ∷ s1)  
    nn20 : {s s0 s1 : List In2} → accept (automaton r) (astart r) s ≡ true → ¬ ( s ≡ s0 ++ i1 ∷ i0 ∷ s1 )
    nn20 {s} {s0} {s1} p np = {!!}
    mono-color : List In2 → Bool
    mono-color [] = true
    mono-color (i0 ∷ s) = mono-color0 s where
        mono-color0 : List In2 → Bool
        mono-color0 [] = true
        mono-color0 (i1 ∷ s) = false
        mono-color0 (i0 ∷ s) = mono-color0 s
    mono-color (i1 ∷ s) = mono-color1 s where
        mono-color1 : List In2 → Bool
        mono-color1 [] = true
        mono-color1 (i0 ∷ s) = false
        mono-color1 (i1 ∷ s) = mono-color1 s
    record Is10 (s : List In2) : Set where
       field
           s0 s1 : List In2
           is-10 :  s ≡ s0 ++ i1 ∷ i0 ∷ s1
    not-mono : { s : List In2 } → ¬ (mono-color s ≡ true)  → Is10 (s ++ s)
    not-mono = {!!}
    mono-count : { s : List In2 } → mono-color s ≡ true   → (length s ≡ count i0 s) ∨ ( length s ≡ count i1 s)
    mono-count = {!!}
    tann : {x y z : List In2} → ¬ y ≡ []
       → x ++ y ++ z ≡ nn
       → accept (automaton r) (astart r) (x ++ y ++ z) ≡ true → ¬ (accept (automaton r) (astart r) (x ++ y ++ y ++ z)  ≡ true )
    tann {x} {y} {z} ny eq axyz axyyz with mono-color y
    ... | true = {!!}
    ... | false = {!!}

