-- {-# OPTIONS  --allow-unsolved-metas #-}
{-# OPTIONS --cubical-compatible --safe #-}


module pumping where

open import Data.Nat
open import Data.Empty
open import Data.List
open import Data.List.Properties
open import Data.Maybe hiding ( map )
open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import logic
open import automaton
-- open import automaton-ex
open import finiteSetUtil
open import finiteSet
open import Relation.Nullary
open import regular-language
open import nat


open FiniteSet

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
tr-accept→ {Q} {Σ} fa .[] is (tend x) = x
tr-accept→ {Q} {Σ} fa (i ∷ is) q (tnext .q tr) = tr-accept→ {Q} {Σ} fa is (δ fa q i) tr

tr-accept← : { Q : Set } { Σ : Set  }
    → (fa : Automaton Q  Σ )
    → (is : List Σ) → (q : Q)  → accept fa q is ≡ true → Trace fa is q
tr-accept← {Q} {Σ} fa [] q ac = tend ac
tr-accept← {Q} {Σ} fa (x ∷ []) q ac = tnext _ (tend ac )
tr-accept← {Q} {Σ} fa (x ∷ x1 ∷ is) q ac = tnext _ (tr-accept← fa (x1 ∷ is)  (δ fa q x)  ac)

tr→qs : { Q : Set } { Σ : Set  }
    → (fa : Automaton Q  Σ )
    → (is : List Σ) → (q : Q) → Trace fa is q → List Q
tr→qs {Q} {Σ} fa .[] q (tend x) = []
tr→qs {Q} {Σ} fa .(_ ∷ _) q (tnext .q tr) = q ∷ tr→qs fa _ (δ fa q _) tr

tr→qs=is : { Q : Set } { Σ : Set  }
    → (fa : Automaton Q  Σ )
    → (is : List Σ) → (q : Q) → (tr : Trace fa is q ) → length is ≡  length (tr→qs fa is q tr)
tr→qs=is fa .[] q (tend x) = refl
tr→qs=is fa (i ∷ is) q (tnext .q tr) = cong suc (tr→qs=is fa is  (δ fa q i) tr)

open Data.Maybe

-- open import Relation.Binary.HeterogeneousEquality as HE using (_≅_ )
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
-- record TA2 { Q : Set } { Σ : Set  } (fa : Automaton Q  Σ ) (finq : FiniteSet Q)  ( q qd : Q ) (is : List Σ)  : Set where
--    field
--        y z : List Σ
--        yz=is : y ++ z ≡ is
--        trace-z    : accept fa qd z ≡ true
--        trace-yz   : accept fa q (y ++ z)  ≡ true
--        q=qd  :  equal? finq qd q ≡ true  → Trace fa z q
--        ¬q=qd :  equal? finq qd q ≡ false → Trace fa z q ∧ Trace fa (y ++ z) q
--           -- head (tr→qs fa q trace-yz) ≡ just qd

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
   tra-phase2 q [] (tend eq1) ()
   tra-phase2 q .(i ∷ is) (tnext .q {i} {is} tr) eq1 with equal? finq qd q in eq
   ...  | true = record { y = [] ; z = _ ; yz=is = refl ; q=qd = qd-nil q (tnext q tr) eq
        ; trace-z  = subst (λ k → Trace fa _ k ) (sym (equal→refl finq eq)) (tnext q tr) ; trace-yz = tnext q tr }
   ... | false = record { y = i ∷ TA1.y ta ; z = TA1.z ta ; yz=is = cong (i ∷_ ) (TA1.yz=is ta )
       ; q=qd = tra-08
       ; trace-z = TA1.trace-z ta ; trace-yz = tnext q ( TA1.trace-yz ta ) } where
            ta : TA1 fa finq (δ fa q i) qd is
            ta = tra-phase2 (δ fa q i) is tr eq1
            tra-07 : Trace fa (TA1.y ta ++ TA1.z ta) (δ fa q i)
            tra-07 = subst (λ k → Trace fa k (δ fa q i)) (sym (TA1.yz=is ta)) tr
            tra-08 : QDSEQ finq qd (TA1.z ta) (tnext q (TA1.trace-yz ta))
            tra-08 = qd-next (TA1.y ta) q (TA1.trace-yz (tra-phase2 (δ fa q i) is tr eq1)) eq (TA1.q=qd ta)
   tra-phase1 : (q : Q)  → (is : List Σ)  → (tr : Trace fa is  q ) → phase1 finq qd (tr→qs fa is q tr) ≡ true  → TA fa q is
   tra-phase1 q [] (tend eq1) ()
   tra-phase1 q .(i ∷ is) (tnext .q {i} {is} tr) p with equal? finq qd q in eq
   ... | true = record { x = [] ; y = i ∷ TA1.y ta ;  z = TA1.z ta ; xyz=is =  cong (i ∷_ ) (TA1.yz=is ta)
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
       -- lemma01 : (a b : List Σ) → a ++ b ≡ [] → (a ≡ [] ) ∧ (b ≡ [])
       -- lemma01 [] [] eq = ⟪ refl , refl ⟫
       -- lemma01 [] (_ ∷ _) ()
       -- lemma01 (_ ∷ _) b ()
       -- list-decomp : {A : Set } → {a c : A } → {b d : List A } → a ∷ b ≡ c ∷ d → (a ≡ c) ∧ (b ≡ d)
       -- list-decomp eq = ⟪ ∷-injectiveˡ eq , ∷-injectiveʳ eq ⟫  -- this is a cheat to avoid warning
       tra-05 : Trace fa (TA1.y ta ++ (i ∷ TA1.y ta) ++ TA1.z ta) (δ fa q i)
       tra-05 = tra-06 _ _ (TA1.trace-yz ta) (TA1.q=qd ta) where
            tra-06 : (y2 : List Σ) → (q : Q) → (tr : Trace fa (y2 ++ z1) q) → QDSEQ finq qd z1 tr  → Trace fa (y2 ++ (i ∷ y1) ++ z1) q
            tra-06 .[] q tr (qd-nil .q .tr x₁) = subst (λ k → Trace fa _ k) (equal→refl finq x₁) tryz
            tra-06 .(_ ∷ y2) q .(tnext q tr) (qd-next y2 .q tr x₁ qdseq) = subst (λ k → Trace fa k q ) refl ( tnext q lemma03)  where
                lemma03 : Trace fa _ (δ fa q _)
                lemma03 = tra-06 _ (δ fa q _) tr qdseq
   ... | false = record { x = i ∷ x ta ; y = y ta ; z = z ta ; xyz=is = cong (i ∷_ ) (xyz=is ta)
          ; non-nil-y = non-nil-y ta
           ; trace-xyz = tnext q (trace-xyz ta ) ; trace-xyyz = tnext q (trace-xyyz ta )} where
       ta : TA fa (δ fa q i ) is
       ta = tra-phase1 (δ fa q i ) is tr p

