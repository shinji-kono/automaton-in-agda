{-# OPTIONS --cubical-compatible  --safe #-}

module finiteSetUtil  where

open import Data.Nat hiding ( _≟_ )
open import Data.Fin renaming ( _<_ to _<<_ ; _>_ to _f>_ ; _≟_ to _f≟_ ) hiding (_≤_ ; pred )
open import Data.Fin.Properties hiding ( <-trans ; ≤-trans ; ≤-refl ; <-irrelevant ) renaming ( <-cmp to <-fcmp )
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import logic
open import nat
open import finiteSet
open import fin
open import Data.Nat.Properties as NP  hiding ( _≟_ )

record Found ( Q : Set ) (p : Q → Bool ) : Set where
     field
       found-q : Q
       found-p : p found-q ≡ true

open Bijection

open import Axiom.Extensionality.Propositional
open import Level hiding (suc ; zero)

module _ {Q : Set } (F : FiniteSet Q) where
     open FiniteSet F
     equal?-refl  : { x : Q } → equal? x x ≡ true
     equal?-refl {x} with F←Q x ≟ F←Q x
     ... | yes eq = refl
     ... | no ne = ⊥-elim (ne refl)
     equal→refl  : { x y : Q } → equal? x y ≡ true → x ≡ y
     equal→refl {q0} {q1} eq with F←Q q0 ≟ F←Q q1
     equal→refl {q0} {q1} refl | yes eq = begin
            q0
        ≡⟨ sym ( finiso→ q0) ⟩
            Q←F (F←Q q0)
        ≡⟨ cong (λ k → Q←F k ) eq ⟩
            Q←F (F←Q q1)
        ≡⟨  finiso→   q1 ⟩
            q1
        ∎  where open ≡-Reasoning
     eqP : (x y : Q) → Dec ( x ≡ y )
     eqP x y with F←Q x ≟ F←Q y
     ... | yes eq = yes (subst₂ (λ j k → j ≡ k ) (finiso→ x) (finiso→ y) (cong Q←F eq) )
     ... | no n = no (λ eq → n (cong F←Q eq))
     End : (m : ℕ ) → (p : Q → Bool ) → Set
     End m p = (i : Fin finite) → m ≤ toℕ i → p (Q←F i )  ≡ false
     first-end :  ( p : Q → Bool ) → End finite p
     first-end p i i>n = ⊥-elim (nat-≤> i>n (fin<n {finite} i) )
     next-end : {m : ℕ } → ( p : Q → Bool ) → End (suc m) p
              → (m<n : m < finite ) → p (Q←F (fromℕ< m<n )) ≡ false
              → End m p
     next-end {m} p prev m<n np i m<i with NP.<-cmp m (toℕ i)
     next-end p prev m<n np i m<i | tri< a ¬b ¬c = prev i a
     next-end p prev m<n np i m<i | tri> ¬a ¬b c = ⊥-elim ( nat-≤> m<i c )
     next-end {m} p prev m<n np i m<i | tri≈ ¬a b ¬c = subst ( λ k → p (Q←F k) ≡ false) (m<n=i i b m<n ) np where
              m<n=i : {n : ℕ } (i : Fin n) {m : ℕ } → m ≡ (toℕ i) → (m<n : m < n )  → fromℕ< m<n ≡ i
              m<n=i i refl m<n = fromℕ<-toℕ i m<n
     found : { p : Q → Bool } → (q : Q ) → p q ≡ true → exists p ≡ true
     found {p} q pt = found1 finite  (NP.≤-refl ) ( first-end p ) where
         found1 : (m : ℕ ) (m<n : m Data.Nat.≤ finite ) → ((i : Fin finite) → m ≤ toℕ i → p (Q←F i )  ≡ false ) →  exists1 m m<n p ≡ true
         found1 0 m<n end = ⊥-elim ( ¬-bool (subst (λ k → k ≡ false ) (cong (λ k → p k) (finiso→ q) ) (end (F←Q q) z≤n )) pt )
         found1 (suc m)  m<n end with bool-≡-? (p (Q←F (fromℕ< m<n))) true
         found1 (suc m)  m<n end | yes eq = subst (λ k → k \/ exists1 m (<to≤  m<n) p ≡ true ) (sym eq) (bool-or-4 {exists1 m (<to≤  m<n) p} )
         found1 (suc m)  m<n end | no np = begin
                 p (Q←F (fromℕ< m<n)) \/ exists1 m (<to≤  m<n) p
              ≡⟨ bool-or-1 (¬-bool-t np ) ⟩
                 exists1 m (<to≤  m<n) p
              ≡⟨ found1 m (<to≤  m<n) (next-end p end m<n (¬-bool-t np )) ⟩
                 true
              ∎  where open ≡-Reasoning
     not-found : { p : Q → Bool } → ( (q : Q ) → p q ≡ false ) → exists p ≡ false
     not-found {p} pn = not-found2 finite NP.≤-refl where
         not-found2 : (m : ℕ ) → (m<n : m Data.Nat.≤ finite ) → exists1 m m<n p ≡ false
         not-found2  zero  _ = refl
         not-found2 ( suc m ) m<n with pn (Q←F (fromℕ< {m} {finite} m<n))
         not-found2 (suc m) m<n | eq = begin
                  p (Q←F (fromℕ< m<n)) \/ exists1 m (<to≤ m<n) p
              ≡⟨ bool-or-1 eq ⟩
                  exists1 m (<to≤ m<n) p
              ≡⟨ not-found2 m (<to≤ m<n)  ⟩
                  false
              ∎  where open ≡-Reasoning
     found← : { p : Q → Bool } → exists p ≡ true → Found Q p
     found← {p} exst = found2 finite NP.≤-refl  (first-end p ) where
         found2 : (m : ℕ ) (m<n : m Data.Nat.≤ finite ) → End m p →  Found Q p
         found2 0 m<n end = ⊥-elim ( ¬-bool f01 exst ) where
             f01 : exists p ≡ false
             f01 = not-found (λ q → subst ( λ k → p k ≡ false  ) (finiso→ _) (end (F←Q q)  z≤n ))
         found2 (suc m)  m<n end with bool-≡-? (p (Q←F (fromℕ< m<n))) true
         found2 (suc m)  m<n end | yes eq = record { found-q = Q←F (fromℕ< m<n) ; found-p = eq }
         found2 (suc m)  m<n end | no np =
               found2 m (<to≤ m<n) (next-end p end m<n (¬-bool-t np ))
     not-found← : { p : Q → Bool } → exists p ≡ false → (q : Q ) → p q ≡ false
     not-found← {p} np q = ¬-bool-t ( contra-position {_} {_} {_} {exists p ≡ true} (found q) (λ ep → ¬-bool np ep ) )
     Q←F-inject : {x y : Fin finite} → Q←F x ≡ Q←F y → x ≡ y
     Q←F-inject eq = subst₂ (λ j k → j ≡ k ) (finiso←  _) (finiso← _) (cong F←Q eq)
     F←Q-inject : {x y : Q } → F←Q x ≡ F←Q y → x ≡ y
     F←Q-inject eq = subst₂ (λ j k → j ≡ k ) (finiso→  _) (finiso→ _) (cong Q←F eq)



iso-fin : {A B : Set} → FiniteSet A  → Bijection A B → FiniteSet B
iso-fin {A} {B}  fin iso = record {
       Q←F = λ f → fun→ iso ( FiniteSet.Q←F fin f )
     ; F←Q = λ b → FiniteSet.F←Q fin (fun← iso b )
     ; finiso→ = finiso→
     ; finiso← = finiso←
   } where
   finiso→ : (q : B) → fun→ iso (FiniteSet.Q←F fin (FiniteSet.F←Q fin (Bijection.fun← iso q))) ≡ q
   finiso→ q = begin
             fun→ iso (FiniteSet.Q←F fin (FiniteSet.F←Q fin (Bijection.fun← iso q)))
           ≡⟨ cong (λ k → fun→ iso k ) (FiniteSet.finiso→ fin _ ) ⟩
             fun→ iso (Bijection.fun← iso q)
           ≡⟨ fiso→ iso _ ⟩
              q
           ∎  where open ≡-Reasoning
   finiso← : (f : Fin (FiniteSet.finite fin ))→ FiniteSet.F←Q fin (Bijection.fun← iso (Bijection.fun→ iso (FiniteSet.Q←F fin f))) ≡ f
   finiso← f = begin
              FiniteSet.F←Q fin (Bijection.fun← iso (Bijection.fun→ iso (FiniteSet.Q←F fin f)))
           ≡⟨ cong (λ k → FiniteSet.F←Q fin k ) (Bijection.fiso← iso _) ⟩
              FiniteSet.F←Q fin (FiniteSet.Q←F fin f)
           ≡⟨ FiniteSet.finiso← fin _  ⟩
              f
           ∎  where
           open ≡-Reasoning

data One : Set where
   one : One

finOne : FiniteSet One
finOne =  record { finite = 1 ;  Q←F = λ _ → one ; F←Q = λ _ → # 0 ; finiso→ = fin00 ; finiso← = fin1≡0  }  where
    fin00 : (q : One) → one ≡ q
    fin00 one = refl

fin-∨1 : {B : Set} → (fb : FiniteSet B ) → FiniteSet (One ∨ B)
fin-∨1 {B} fb =  record {
       Q←F = Q←F
     ; F←Q =  F←Q
     ; finiso→ = finiso→
     ; finiso← = finiso←
   }  where
   b = FiniteSet.finite fb
   Q←F : Fin (suc b) → One ∨ B
   Q←F zero = case1 one
   Q←F (suc f) = case2 (FiniteSet.Q←F fb f)
   F←Q : One ∨ B → Fin (suc b)
   F←Q (case1 one) = zero
   F←Q (case2 f ) = suc (FiniteSet.F←Q fb f)
   finiso→ : (q : One ∨ B) → Q←F (F←Q q) ≡ q
   finiso→ (case1 one) = refl
   finiso→ (case2 b) = cong (λ k → case2 k ) (FiniteSet.finiso→ fb b)
   finiso← : (q : Fin (suc b)) → F←Q (Q←F q) ≡ q
   finiso← zero = refl
   finiso← (suc f) = cong ( λ k → suc k ) (FiniteSet.finiso← fb f)


fin-∨2 : {B : Set} → ( a : ℕ ) → FiniteSet B  → FiniteSet (Fin a ∨ B)
fin-∨2 {B} zero  fb = iso-fin fb iso where
 iso : Bijection B (Fin zero ∨ B)
 iso =  record {
        fun← = fun←1
      ; fun→ = λ b → case2 b
      ; fiso→ = fiso→1
      ; fiso← = λ _ → refl
    } where
     fun←1 : Fin zero ∨ B → B
     fun←1 (case2 x) = x
     fiso→1 : (f : Fin zero ∨ B ) → case2 (fun←1 f) ≡ f
     fiso→1 (case2 x)  = refl
fin-∨2 {B} (suc a) fb =  iso-fin (fin-∨1 (fin-∨2 a fb) ) iso
    where
 iso : Bijection (One ∨ (Fin a ∨ B) ) (Fin (suc a) ∨ B)
 fun← iso (case1 zero) = case1 one
 fun← iso (case1 (suc f)) = case2 (case1 f)
 fun← iso (case2 b) = case2 (case2 b)
 fun→ iso (case1 one) = case1 zero
 fun→ iso (case2 (case1 f)) = case1 (suc f)
 fun→ iso (case2 (case2 b)) = case2 b
 fiso← iso (case1 one) = refl
 fiso← iso (case2 (case1 x)) = refl
 fiso← iso (case2 (case2 x)) = refl
 fiso→ iso (case1 zero) = refl
 fiso→ iso (case1 (suc x)) = refl
 fiso→ iso (case2 x) = refl


FiniteSet→Fin : {A : Set} → (fin : FiniteSet A  ) → Bijection (Fin (FiniteSet.finite fin)) A
fun← (FiniteSet→Fin fin) f = FiniteSet.F←Q fin f
fun→ (FiniteSet→Fin fin) f = FiniteSet.Q←F fin f
fiso← (FiniteSet→Fin fin) = FiniteSet.finiso← fin
fiso→ (FiniteSet→Fin fin) =  FiniteSet.finiso→ fin


fin-∨ : {A B : Set} → FiniteSet A → FiniteSet B → FiniteSet (A ∨ B)
fin-∨ {A} {B}  fa fb = iso-fin (fin-∨2 a  fb ) iso2 where
    a = FiniteSet.finite fa
    ia = FiniteSet→Fin fa
    iso2 : Bijection (Fin a ∨ B ) (A ∨ B)
    fun← iso2 (case1 x) = case1 (fun← ia x )
    fun← iso2 (case2 x) = case2 x
    fun→ iso2 (case1 x) = case1 (fun→ ia x )
    fun→ iso2 (case2 x) = case2 x
    fiso← iso2 (case1 x) = cong ( λ k → case1 k ) (Bijection.fiso← ia x)
    fiso← iso2 (case2 x) = refl
    fiso→ iso2 (case1 x) = cong ( λ k → case1 k ) (Bijection.fiso→ ia x)
    fiso→ iso2 (case2 x) = refl

open import Data.Product hiding ( map )

fin-× : {A B : Set} → FiniteSet A → FiniteSet B → FiniteSet (A × B)
fin-× {A} {B}  fa fb with FiniteSet→Fin fa
... | a=f = iso-fin (fin-×-f a ) iso-1 where
   a = FiniteSet.finite fa
   b = FiniteSet.finite fb
   iso-1 : Bijection (Fin a × B) ( A × B )
   fun← iso-1 x = ( FiniteSet.F←Q fa (proj₁ x)  , proj₂ x)
   fun→ iso-1 x = ( FiniteSet.Q←F fa (proj₁ x)  , proj₂ x)
   fiso← iso-1 x  =  lemma  where
     lemma : (FiniteSet.F←Q fa (FiniteSet.Q←F fa (proj₁ x)) , proj₂ x) ≡ ( proj₁ x , proj₂ x )
     lemma = cong ( λ k → ( k ,  proj₂ x ) )  (FiniteSet.finiso← fa _ )
   fiso→ iso-1 x = cong ( λ k → ( k ,  proj₂ x ) )  (FiniteSet.finiso→ fa _ )

   iso-2 : {a : ℕ } → Bijection (B ∨ (Fin a × B)) (Fin (suc a) × B)
   fun← iso-2 (zero , b ) = case1 b
   fun← iso-2 (suc fst , b ) = case2 ( fst , b )
   fun→ iso-2 (case1 b) = ( zero , b )
   fun→ iso-2 (case2 (a , b )) = ( suc a , b )
   fiso← iso-2 (case1 x) = refl
   fiso← iso-2 (case2 x) = refl
   fiso→ iso-2 (zero , b ) = refl
   fiso→ iso-2 (suc a , b ) = refl

   fin-×-f : ( a  : ℕ ) → FiniteSet ((Fin a) × B)
   fin-×-f zero = record { Q←F = λ () ; F←Q = λ () ; finiso→ = λ () ; finiso← = λ () ; finite = 0 }
   fin-×-f (suc a) = iso-fin ( fin-∨ fb ( fin-×-f a ) ) iso-2

open _∧_

fin-∧ : {A B : Set} → FiniteSet A → FiniteSet B → FiniteSet (A ∧ B)
fin-∧ {A} {B} fa fb with FiniteSet→Fin fa    -- same thing for our tool
... | a=f = iso-fin (fin-×-f a ) iso-1 where
   a = FiniteSet.finite fa
   b = FiniteSet.finite fb
   iso-1 : Bijection (Fin a ∧ B) ( A ∧ B )
   fun← iso-1 x = record { proj1 = FiniteSet.F←Q fa (proj1 x)  ; proj2 =  proj2 x}
   fun→ iso-1 x = record { proj1 = FiniteSet.Q←F fa (proj1 x)  ; proj2 =  proj2 x}
   fiso← iso-1 x  =  lemma  where
     lemma : record { proj1 = FiniteSet.F←Q fa (FiniteSet.Q←F fa (proj1 x)) ; proj2 =  proj2 x} ≡ record {proj1 =  proj1 x ; proj2 =  proj2 x }
     lemma = cong ( λ k → record {proj1 = k ;  proj2 = proj2 x } )  (FiniteSet.finiso← fa _ )
   fiso→ iso-1 x = cong ( λ k → record {proj1 =  k ; proj2 =  proj2 x } )  (FiniteSet.finiso→ fa _ )

   iso-2 : {a : ℕ } → Bijection (B ∨ (Fin a ∧ B)) (Fin (suc a) ∧ B)
   fun← iso-2 (record { proj1 = zero ; proj2 =  b }) = case1 b
   fun← iso-2 (record { proj1 = suc fst ; proj2 =  b }) = case2 ( record { proj1 = fst ; proj2 =  b } )
   fun→ iso-2 (case1 b) = record {proj1 =  zero ; proj2 =  b }
   fun→ iso-2 (case2 (record { proj1 = a ; proj2 =  b })) = record { proj1 =  suc a ; proj2 =  b }
   fiso← iso-2 (case1 x) = refl
   fiso← iso-2 (case2 x) = refl
   fiso→ iso-2 (record { proj1 = zero ; proj2 =  b }) = refl
   fiso→ iso-2 (record { proj1 = suc a ; proj2 =  b }) = refl

   fin-×-f : ( a  : ℕ ) → FiniteSet ((Fin a) ∧ B)
   fin-×-f zero = record { Q←F = λ () ; F←Q = λ () ; finiso→ = λ () ; finiso← = λ () ; finite = 0 }
   fin-×-f (suc a) = iso-fin ( fin-∨ fb ( fin-×-f a ) ) iso-2

-- import Data.Nat.DivMod

open import Data.Vec hiding ( map ; length )
import Data.Product

exp2 : (n : ℕ ) → exp 2 (suc n) ≡ exp 2 n Data.Nat.+ exp 2 n
exp2 n = begin
      exp 2 (suc n)
   ≡⟨⟩
      2 * ( exp 2 n )
   ≡⟨ *-comm 2 (exp 2 n)  ⟩
      ( exp 2 n ) * 2
   ≡⟨ *-suc ( exp 2 n ) 1 ⟩
      (exp 2 n ) Data.Nat.+ ( exp 2 n ) * 1
   ≡⟨ cong ( λ k →  (exp 2 n ) Data.Nat.+  k ) (proj₂ *-identity (exp 2 n) ) ⟩
      exp 2 n Data.Nat.+ exp 2 n
   ∎  where
       open ≡-Reasoning
       open Data.Product

cast-iso : {n m : ℕ } → (eq : n ≡ m ) → (f : Fin m ) → Data.Fin.cast eq ( Data.Fin.cast (sym eq ) f)  ≡ f
cast-iso refl zero =  refl
cast-iso refl (suc f) = cong ( λ k → suc k ) ( cast-iso refl f )


fin2List : {n : ℕ } → FiniteSet (Vec Bool n)
fin2List {zero} = record {
   Q←F = λ _ → Vec.[]
 ; F←Q =  λ _ → # 0
 ; finiso→ = finiso→
 ; finiso← = finiso←
   } where
   Q = Vec Bool zero
   finiso→ : (q : Q) → [] ≡ q
   finiso→ [] = refl
   finiso← : (f : Fin (exp 2 zero)) → # 0 ≡ f
   finiso← zero = refl
fin2List {suc n} = subst (λ k → FiniteSet (Vec Bool (suc n)) ) (sym (exp2 n)) ( iso-fin (fin-∨ (fin2List ) (fin2List )) iso )
    where
   QtoR : Vec Bool (suc  n) →  Vec Bool n ∨ Vec Bool n
   QtoR ( true ∷ x ) = case1 x
   QtoR ( false ∷ x ) = case2 x
   RtoQ : Vec Bool n ∨ Vec Bool n → Vec Bool (suc  n)
   RtoQ ( case1 x ) = true ∷ x
   RtoQ ( case2 x ) = false ∷ x
   isoRQ : (x : Vec Bool (suc  n) ) → RtoQ ( QtoR x ) ≡ x
   isoRQ (true ∷ _ ) = refl
   isoRQ (false ∷ _ ) = refl
   isoQR : (x : Vec Bool n ∨ Vec Bool n ) → QtoR ( RtoQ x ) ≡ x
   isoQR (case1 x) = refl
   isoQR (case2 x) = refl
   iso : Bijection (Vec Bool n ∨ Vec Bool n) (Vec Bool (suc n))
   iso = record { fun← = QtoR ; fun→ = RtoQ ; fiso← = isoQR ; fiso→ = isoRQ  }

F2L : {Q : Set } {n : ℕ } → (fin : FiniteSet Q ) → n < suc (FiniteSet.finite fin) → ( (q : Q) → toℕ (FiniteSet.F←Q fin q ) < n  → Bool ) → Vec Bool n
F2L  {Q} {zero} fin _ Q→B = []
F2L  {Q} {suc n} fin (s≤s n<m) Q→B = Q→B (FiniteSet.Q←F fin (fromℕ< n<m)) lemma6 ∷ F2L {Q} fin (NP.<-trans n<m a<sa ) qb1 where
   lemma6 : toℕ (FiniteSet.F←Q fin (FiniteSet.Q←F fin (fromℕ< n<m))) < suc n
   lemma6 = subst (λ k → toℕ k < suc n ) (sym (FiniteSet.finiso← fin _ )) (subst (λ k → k < suc n) (sym (toℕ-fromℕ< n<m ))  a<sa )
   qb1 : (q : Q) → toℕ (FiniteSet.F←Q fin q) < n → Bool
   qb1 q q<n = Q→B q (NP.<-trans q<n a<sa)

List2Func : { Q : Set } → {n : ℕ } → (fin : FiniteSet Q ) → n < suc (FiniteSet.finite fin)  → Vec Bool n →  Q → Bool
List2Func {Q} {zero} fin (s≤s z≤n) [] q = false
List2Func {Q} {suc n} fin (s≤s n<m) (h ∷ t) q with  FiniteSet.F←Q fin q ≟ fromℕ< n<m
... | yes _ = h
... | no _ = List2Func {Q} fin (NP.<-trans n<m a<sa ) t q

open import Level renaming ( suc to Suc ; zero to Zero)


L2F : {Q : Set } {n : ℕ } → (fin : FiniteSet Q )  → n < suc (FiniteSet.finite fin) → Vec Bool n → (q :  Q ) → toℕ (FiniteSet.F←Q fin q ) < n  → Bool
L2F fin n<m x q q<n = List2Func fin n<m x q

L2F-iso : { Q : Set } → (fin : FiniteSet Q ) → (f : Q → Bool ) → (q : Q ) → (L2F fin a<sa (F2L fin a<sa (λ q _ → f q) )) q (toℕ<n _) ≡ f q
L2F-iso {Q} fin f q = l2f m a<sa (toℕ<n _) where
  m = FiniteSet.finite fin
  lemma11f : {n : ℕ } → (n<m : n < m )  → ¬ ( FiniteSet.F←Q fin q ≡ fromℕ< n<m ) → toℕ (FiniteSet.F←Q fin q) ≤ n → toℕ (FiniteSet.F←Q fin q) < n
  lemma11f  n<m ¬q=n q≤n = lemma13 n<m (contra-position (lemma12 n<m _) ¬q=n ) q≤n where
     lemma13 : {n nq : ℕ } → (n<m : n < m )  → ¬ ( nq ≡ n ) → nq  ≤ n → nq < n
     lemma13 {0} {0} (s≤s z≤n) nt z≤n = ⊥-elim ( nt refl )
     lemma13 {suc _} {0} (s≤s (s≤s n<m)) nt z≤n = s≤s z≤n
     lemma13 {suc n} {suc nq} n<m nt (s≤s nq≤n) = s≤s (lemma13 {n} {nq} (NP.<-trans a<sa n<m ) (λ eq → nt ( cong ( λ k → suc k ) eq )) nq≤n)
     lemma3f : {a b : ℕ } → (lt : a < b ) → fromℕ< (s≤s lt) ≡ suc (fromℕ< lt)
     lemma3f (s≤s lt) = refl
     lemma12f : {n m : ℕ } → (n<m : n < m ) → (f : Fin m )  → toℕ f ≡ n → f ≡ fromℕ< n<m
     lemma12f {zero} {suc m} (s≤s z≤n) zero refl = refl
     lemma12f {suc n} {suc m} (s≤s n<m) (suc f) refl = subst ( λ k → suc f ≡ k ) (sym (lemma3f n<m) ) ( cong ( λ k → suc k ) ( lemma12f {n} {m} n<m f refl  ) )
  l2f :  (n : ℕ ) → (n<m : n < suc m ) → (q<n : toℕ (FiniteSet.F←Q fin q ) < n )  →  (L2F fin n<m (F2L fin n<m  (λ q _ → f q))) q q<n ≡ f q
  l2f zero (s≤s z≤n) ()
  l2f (suc n) (s≤s n<m) (s≤s n<q) with FiniteSet.F←Q fin q ≟ fromℕ< n<m
  l2f (suc n) (s≤s n<m) (s≤s n<q) | yes p = begin
        f (FiniteSet.Q←F fin (fromℕ< n<m))
     ≡⟨ cong ( λ k → f (FiniteSet.Q←F fin k )) (sym p)  ⟩
        f (FiniteSet.Q←F fin ( FiniteSet.F←Q fin q ))
     ≡⟨ cong ( λ k → f k ) (FiniteSet.finiso→ fin _ ) ⟩
        f q
     ∎  where
       open ≡-Reasoning
  l2f (suc n) (s≤s n<m) (s≤s n<q) | no ¬p = l2f n (NP.<-trans n<m a<sa) (lemma11f n<m ¬p n<q)

Fin2Finite : ( n : ℕ ) → FiniteSet (Fin n)
Fin2Finite n = record { F←Q = λ x → x ; Q←F = λ x → x ; finiso← = λ q → refl ; finiso→ = λ q → refl }

--
-- fin→ is in finiteFunc.agda
--      we excludeit becauase it uses f-extensionarity

open import Data.List

open FiniteSet

memberQ : { Q : Set }  (finq : FiniteSet Q) (q : Q) (qs : List Q ) → Bool
memberQ {Q} finq q [] = false
memberQ {Q} finq q (q0 ∷ qs) with equal? finq q q0
... | true = true
... | false = memberQ finq q qs

--
-- there is a duplicate element in finite list
--

--
-- How about this?
--      get list of Q
--      remove one element for each Q from list
--      there must be remaining list > 1
--      theses are duplicates
--      actualy it is duplicate

phase2 : { Q : Set }  (finq : FiniteSet Q) (q : Q) (qs : List Q ) → Bool
phase2 finq q [] = false
phase2 finq q (x ∷ qs) with equal? finq q x
... | true = true
... | false = phase2 finq q qs
phase1 : { Q : Set }  (finq : FiniteSet Q) (q : Q) (qs : List Q ) → Bool
phase1 finq q [] = false
phase1 finq q (x ∷ qs) with equal? finq q x
... | true = phase2 finq q qs
... | false = phase1 finq q qs

dup-in-list : { Q : Set }  (finq : FiniteSet Q) (q : Q) (qs : List Q ) → Bool
dup-in-list {Q} finq q qs = phase1 finq q qs

--
-- if length of the list is longer than kinds of a finite set, there is a duplicate
-- prove this based on the theorem on Data.Fin
--

dup-in-list+fin : { Q : Set }  (finq : FiniteSet Q)
   → (q : Q) (qs : List Q )
   → fin-dup-in-list (F←Q  finq q) (map (F←Q finq) qs) ≡ true
   → dup-in-list finq q qs ≡ true
dup-in-list+fin {Q} finq q qs p = i-phase1 qs p where
    i-phase2 : (qs : List Q) →   fin-phase2 (F←Q  finq q) (map (F←Q finq) qs) ≡ true
        → phase2 finq q qs ≡ true
    i-phase2 (x ∷ qs) p with equal? finq q x in eq | <-fcmp  (F←Q finq q)  (F←Q finq x)
    ... | true |  t = refl
    ... | false |  tri< a ¬b ¬c = i-phase2 qs p
    ... | false |  tri≈ ¬a b ¬c = ⊥-elim (¬-bool eq
        (subst₂ (λ j k → equal? finq j k ≡ true) (finiso→ finq q) (subst (λ k →  Q←F finq k ≡ x) (sym b) (finiso→ finq x)) ( equal?-refl finq  )))
    ... | false |  tri> ¬a ¬b c = i-phase2 qs p
    i-phase1 : (qs : List Q) → fin-phase1 (F←Q  finq q) (map (F←Q finq) qs) ≡ true
        → phase1 finq q qs ≡ true
    i-phase1 (x ∷ qs) p with equal? finq q x in eq | <-fcmp  (F←Q finq q)  (F←Q finq x)
    ... | true |  tri< a ¬b ¬c =  ⊥-elim ( nat-≡< (cong (λ x → toℕ (F←Q finq x)) ( equal→refl finq eq )) a )
    ... | true |  tri≈ ¬a b ¬c = i-phase2 qs p
    ... | true |  tri> ¬a ¬b c = ⊥-elim ( nat-≡< (cong (λ x → toℕ (F←Q finq x)) (sym ( equal→refl finq eq ))) c )
    ... | false |  tri< a ¬b ¬c = i-phase1 qs p
    ... | false |  tri≈ ¬a b ¬c = ⊥-elim (¬-bool eq
        (subst₂ (λ j k → equal? finq j k ≡ true) (finiso→ finq q) (subst (λ k →  Q←F finq k ≡ x) (sym b) (finiso→ finq x)) ( equal?-refl finq  )))
    ... | false |  tri> ¬a ¬b c = i-phase1 qs p

record Dup-in-list {Q : Set } (finq : FiniteSet Q) (qs : List Q)  : Set where
   field
      dup : Q
      is-dup : dup-in-list finq dup qs ≡ true

dup-in-list>n : {Q : Set } → (finq : FiniteSet Q) → (qs : List Q)  → (len> : length qs > finite finq ) → Dup-in-list finq qs
dup-in-list>n {Q} finq qs lt = record { dup = Q←F finq (FDup-in-list.dup dl)
  ; is-dup = dup-in-list+fin finq (Q←F finq (FDup-in-list.dup dl)) qs dl01 } where
     maplen : (qs : List Q) → length (map (F←Q finq) qs) ≡ length qs
     maplen [] = refl
     maplen (x ∷ qs) = cong suc (maplen qs)
     dl : FDup-in-list (finite finq ) (map (F←Q finq) qs)
     dl = fin-dup-in-list>n (map (F←Q finq) qs) (subst (λ k → k > finite finq ) (sym (maplen qs)) lt)
     dl01 :  fin-dup-in-list (F←Q finq (Q←F finq (FDup-in-list.dup dl))) (map (F←Q finq) qs) ≡ true
     dl01 = subst (λ k →  fin-dup-in-list k (map (F←Q finq) qs) ≡ true )
         (sym (finiso← finq _)) ( FDup-in-list.is-dup dl )

open import bijection using ( InjectiveF ; Is )

-- open import Relation.Binary.HeterogeneousEquality as HE using (_≅_ )

inject-fin : {A B : Set}  (fa : FiniteSet A )
   → (fi : InjectiveF B A)
   → (is-B : (a : A ) → Dec (Is B A (InjectiveF.f fi) a)  )
   → FiniteSet B
inject-fin {A} {B} fa fi is-B with finite fa in eq1
... | zero = record {
       finite = 0
       ; Q←F = λ ()
       ; F←Q = λ b → ⊥-elim ( lem00 b)
       ; finiso→ = λ b → ⊥-elim ( lem00 b)
       ; finiso← = λ ()
       } where
          lem00 : ( b : B) → ⊥
          lem00 b with subst (λ k → Fin k ) eq1 (F←Q fa (InjectiveF.f fi b))
          ... | ()
... | suc pfa = record {
       finite = maxb
       ; Q←F = λ fb → CountB.b (cb00 _ (fin<n {_} fb))
       ; F←Q = λ b → fromℕ< (cb<mb b)
       ; finiso→ = iso1
       ; finiso← = iso0
       } where
    f = InjectiveF.f fi
    pfa<fa : pfa < finite fa
    pfa<fa = subst (λ k → pfa < k ) (sym eq1) a<sa
    0<fa : 0 < finite fa
    0<fa = <-transˡ (s≤s z≤n) pfa<fa

    count-B : ℕ → ℕ
    count-B zero with is-B (Q←F fa ( fromℕ< {0} 0<fa ))
    ... | yes isb = 1
    ... | no nisb = 0
    count-B (suc n) with <-cmp (finite fa) (suc n)
    ... | tri< a ¬b ¬c = count-B n
    ... | tri≈ ¬a b ¬c = count-B n
    ... | tri> ¬a ¬b c with is-B (Q←F fa (fromℕ< c))
    ... | yes isb = suc (count-B n)
    ... | no nisb = count-B n

    record CountB (n : ℕ)  : Set where
       field
          b : B
          cb : ℕ
          b=cn : cb ≡ toℕ (F←Q fa (f b))
          cb=n : count-B cb ≡ suc n
          cb-inject : (cb1 : ℕ) → (c1<a : cb1 < finite fa)  → Is B A f (Q←F fa (fromℕ< c1<a)) → count-B cb ≡ count-B cb1 → cb ≡ cb1

    maxb : ℕ
    maxb = count-B (finite fa)

    count-B-mono : {i j : ℕ} → i ≤ j → count-B i ≤ count-B j
    count-B-mono {i} {j} i≤j with ≤-∨ i≤j
    ... | case1 refl = ≤-refl
    ... | case2 i<j = lem00 _ _ i<j where
         lem00 : (i j : ℕ) → i < j → count-B i ≤ count-B j
         lem00 i (suc j) (s≤s i<j) = ≤-trans (count-B-mono i<j) (lem01 j) where
             lem01 : (j : ℕ) → count-B j ≤ count-B (suc j)
             lem01 zero with <-cmp (finite fa) 1
             lem01 zero | tri< a ¬b ¬c = ≤-refl
             lem01 zero | tri≈ ¬a b ¬c = ≤-refl
             lem01 zero | tri> ¬a ¬b c with is-B (Q←F fa (fromℕ< c)) | is-B (Q←F fa ( fromℕ< {0} 0<fa ))
             ... | yes isb1 | yes isb0  = s≤s z≤n
             ... | yes isb1 | no  nisb0 = z≤n
             ... | no nisb1 | yes isb0  = refl-≤≡ (sym lem14 ) where
                  lem14 : count-B 0 ≡ 1    -- in-equality does not work we have to repeat the proof
                  lem14 with is-B (Q←F fa ( fromℕ< {0} 0<fa ))
                  ... | yes isb = refl
                  ... | no ne = ⊥-elim (ne isb0)
             ... | no nisb1 | no  nisb0 = z≤n
             lem01 (suc i) with <-cmp (finite fa) (suc i) | <-cmp (finite fa) (suc (suc i))
             ... | tri< a ¬b ¬c | tri< a₁ ¬b₁ ¬c₁ = refl-≤≡ (sym lem14) where
                  lem14 : count-B (suc i) ≡ count-B i
                  lem14 with <-cmp (finite fa) (suc i)
                  ... | tri< a ¬b ¬c = refl
                  ... | tri≈ ¬a b ¬c = ⊥-elim ( ¬a a )
                  ... | tri> ¬a ¬b c = ⊥-elim ( ¬a a )
             ... | tri< a ¬b ¬c | tri≈ ¬a b ¬c₁ = ⊥-elim (nat-≡< b (<-trans a a<sa))
             ... | tri< a ¬b ¬c | tri> ¬a ¬b₁ c = ⊥-elim (nat-<> a (<-trans a<sa c) )
             ... | tri≈ ¬a b ¬c | tri< a ¬b ¬c₁ = refl-≤≡ (sym lem14 ) where
                  lem14 : count-B (suc i) ≡ count-B i
                  lem14 with <-cmp (finite fa) (suc i)
                  ... | tri< a ¬b ¬c = refl
                  ... | tri≈ ¬a b ¬c = refl
                  ... | tri> ¬a ¬b c = ⊥-elim ( ¬c c )
             ... | tri≈ ¬a b ¬c | tri≈ ¬a₁ b₁ ¬c₁ = ⊥-elim (nat-≡< (sym b) (subst (λ k → _ < k ) (sym b₁) a<sa) )
             ... | tri≈ ¬a b ¬c | tri> ¬a₁ ¬b c = ⊥-elim (nat-≡< (sym b) (<-trans a<sa c))
             ... | tri> ¬a ¬b c | tri< a ¬b₁ ¬c = ⊥-elim (nat-≤> a (<-transʳ  c a<sa ) )
             ... | tri> ¬a ¬b c | tri≈ ¬a₁ b ¬c with is-B (Q←F fa (fromℕ< c))
             ... | yes  isb = refl-≤≡ (sym lem14) where
                  lem14 : count-B (suc i) ≡ suc (count-B i)
                  lem14 with <-cmp (finite fa) (suc i)
                  ... | tri< a₂ ¬b₂ ¬c₂ = ⊥-elim (¬c₂ c)
                  ... | tri≈ ¬a₂ b₂ ¬c₂ = ⊥-elim (¬c₂ c)
                  ... | tri> ¬a₂ ¬b₂ c₂ with is-B (Q←F fa ( fromℕ< c₂ ))
                  ... | yes isb = refl
                  ... | no ne = ⊥-elim (ne record {a = Is.a isb ; fa=c = trans (Is.fa=c isb) (cong (λ k → Q←F fa k) (lemma10 refl )) } )
             ... | no  nisb = refl-≤≡ (sym lem14) where
                  lem14 : count-B (suc i) ≡ count-B i
                  lem14 with <-cmp (finite fa) (suc i)
                  ... | tri< a₂ ¬b₂ ¬c₂ = ⊥-elim (¬c₂ c)
                  ... | tri≈ ¬a₂ b₂ ¬c₂ = ⊥-elim (¬c₂ c)
                  ... | tri> ¬a₂ ¬b₂ c₂ with is-B (Q←F fa ( fromℕ< c₂ ))
                  ... | yes isb = ⊥-elim (nisb record {a = Is.a isb ; fa=c = trans (Is.fa=c isb) (cong (λ k → Q←F fa k) (lemma10 refl )) } )
                  ... | no ne = refl
             lem01 (suc i) | tri> ¬a ¬b c | tri> ¬a₁ ¬b₁ c₁
                  with is-B (Q←F fa (fromℕ< c)) | is-B (Q←F fa (fromℕ< c₁))
             ... | yes  isb0 | yes  isb1 = ≤-trans (refl-≤≡ (sym lem14)) a≤sa where
                  lem14 : count-B (suc i) ≡ suc (count-B i)
                  lem14 with <-cmp (finite fa) (suc i)
                  ... | tri< a₂ ¬b₂ ¬c₂ = ⊥-elim (¬c₂ c)
                  ... | tri≈ ¬a₂ b₂ ¬c₂ = ⊥-elim (¬c₂ c)
                  ... | tri> ¬a₂ ¬b₂ c₂ with is-B (Q←F fa ( fromℕ< c₂ ))
                  ... | no ne = ⊥-elim (ne record {a = Is.a isb0 ; fa=c = trans (Is.fa=c isb0) (cong (λ k → Q←F fa k) (lemma10 refl )) } )
                  ... | yes isb = refl
             ... | yes  isb0 | no  nisb1 = refl-≤≡ (sym lem14) where
                  lem14 : count-B (suc i) ≡ suc (count-B i)
                  lem14 with <-cmp (finite fa) (suc i)
                  ... | tri< a₂ ¬b₂ ¬c₂ = ⊥-elim (¬c₂ c)
                  ... | tri≈ ¬a₂ b₂ ¬c₂ = ⊥-elim (¬c₂ c)
                  ... | tri> ¬a₂ ¬b₂ c₂ with is-B (Q←F fa ( fromℕ< c₂ ))
                  ... | no ne = ⊥-elim (ne record {a = Is.a isb0 ; fa=c = trans (Is.fa=c isb0) (cong (λ k → Q←F fa k) (lemma10 refl )) } )
                  ... | yes isb = refl
             ... | no  nisb0 | yes  isb1 = ≤-trans (refl-≤≡ (sym lem14)) a≤sa where
                  lem14 : count-B (suc i) ≡ count-B i
                  lem14 with <-cmp (finite fa) (suc i)
                  ... | tri< a₂ ¬b₂ ¬c₂ = ⊥-elim (¬c₂ c)
                  ... | tri≈ ¬a₂ b₂ ¬c₂ = ⊥-elim (¬c₂ c)
                  ... | tri> ¬a₂ ¬b₂ c₂ with is-B (Q←F fa ( fromℕ< c₂ ))
                  ... | no ne = refl
                  ... | yes isb = ⊥-elim (nisb0 record {a = Is.a isb ; fa=c = trans (Is.fa=c isb) (cong (λ k → Q←F fa k) (lemma10 refl )) } )
             ... | no  nisb0 | no  nisb1 = refl-≤≡ (sym lem14) where
                  lem14 : count-B (suc i) ≡ count-B i
                  lem14 with <-cmp (finite fa) (suc i)
                  ... | tri< a₂ ¬b₂ ¬c₂ = ⊥-elim (¬c₂ c)
                  ... | tri≈ ¬a₂ b₂ ¬c₂ = ⊥-elim (¬c₂ c)
                  ... | tri> ¬a₂ ¬b₂ c₂ with is-B (Q←F fa ( fromℕ< c₂ ))
                  ... | no ne = refl
                  ... | yes isb = ⊥-elim (nisb0 record {a = Is.a isb ; fa=c = trans (Is.fa=c isb) (cong (λ k → Q←F fa k) (lemma10 refl )) } )

    lem31 : (b : B) → 0 < count-B (toℕ (F←Q fa (f b)))
    lem31 b = lem32 (toℕ (F←Q fa (f b))) refl where
        lem32 : (i : ℕ) → toℕ (F←Q fa (f b)) ≡ i → 0 < count-B i
        lem32 zero   eq with is-B (Q←F fa ( fromℕ< {0} 0<fa ))
        ... | yes isb = s≤s z≤n
        ... | no nisb = ⊥-elim ( nisb record { a = b ; fa=c = lem33 } ) where
            lem33 : f b ≡ Q←F fa ( fromℕ< {0} 0<fa )
            lem33 = begin
              f b ≡⟨ sym (finiso→  fa _) ⟩
              Q←F fa ( F←Q fa (f b))  ≡⟨ sym (cong (λ k → Q←F fa k)  ( fromℕ<-toℕ _ (fin<n _))) ⟩
              Q←F fa ( fromℕ< (fin<n _) )  ≡⟨ cong (λ k → Q←F fa k) (fromℕ<-cong _ _ eq (fin<n _) 0<fa) ⟩
              Q←F fa ( fromℕ< {0} 0<fa ) ∎ where
                open ≡-Reasoning
        lem32 (suc i) eq with <-cmp (finite fa) (suc i)
        ... | tri< a ¬b ¬c = ⊥-elim ( nat-≡< eq (<-trans (fin<n _) a) )
        ... | tri≈ ¬a eq1 ¬c = ⊥-elim ( nat-≡< eq (subst (λ k → toℕ (F←Q fa (f b)) < k ) eq1 (fin<n _)))
        ... | tri> ¬a ¬b c with is-B (Q←F fa (fromℕ< c))
        ... | yes isb = s≤s z≤n
        ... | no nisb = ⊥-elim ( nisb record { a = b ; fa=c = lem33 } ) where
            lem33 : f b ≡ Q←F fa ( fromℕ< c)
            lem33 = begin
              f b ≡⟨ sym (finiso→  fa _) ⟩
              Q←F fa ( F←Q fa (f b))  ≡⟨ sym (cong (λ k → Q←F fa k)  ( fromℕ<-toℕ _ (fin<n _))) ⟩
              Q←F fa ( fromℕ< (fin<n _) )  ≡⟨ cong (λ k → Q←F fa k) (fromℕ<-cong _ _ eq (fin<n _) c ) ⟩
              Q←F fa ( fromℕ< c ) ∎ where
                open ≡-Reasoning

    cb<mb : (b : B) → pred (count-B (toℕ (F←Q fa (f b)))) < maxb
    cb<mb b = sx≤y→x<y ( begin
        suc ( pred (count-B (toℕ (F←Q fa (f b)))))  ≡⟨ sucprd (lem31 b) ⟩
        count-B (toℕ (F←Q fa (f b)))  ≤⟨ lem02 ⟩
        count-B (finite fa)   ∎ ) where
          open ≤-Reasoning
          lem02 : count-B (toℕ (F←Q fa (f b))) ≤ count-B (finite fa)
          lem02 = count-B-mono (<to≤ (fin<n {_} (F←Q fa (f b))))

    cb00 : (n : ℕ) → n < count-B (finite fa) → CountB n
    cb00 n n<cb = lem09 (finite fa) (count-B (finite fa)) (<-transˡ a<sa n<cb) refl where

        lem06 : (i j : ℕ) → (i<fa : i < finite fa) (j<fa : j < finite fa)
            →  Is B A f (Q←F fa (fromℕ< i<fa)) → Is B A f (Q←F fa (fromℕ< j<fa)) → count-B i ≡ count-B j → i ≡ j
        lem06 i j i<fa j<fa bi bj eq = lem08 where
            lem20 : (i j : ℕ) → i < j → (i<fa : i < finite fa) (j<fa : j < finite fa)
                →  Is B A f (Q←F fa (fromℕ< i<fa)) → Is B A f (Q←F fa (fromℕ< j<fa)) → count-B i < count-B j
            lem20 zero (suc j) i<j i<fa j<fa bi bj with <-cmp (finite fa) (suc j)
            ... | tri< a ¬b ¬c = ⊥-elim (¬c j<fa)
            ... | tri≈ ¬a b ¬c = ⊥-elim (¬c j<fa)
            ... | tri> ¬a ¬b c with  is-B (Q←F fa ( fromℕ< 0<fa )) |  is-B (Q←F fa (fromℕ< c))
            ... | no nisc  | _ = ⊥-elim (nisc record { a = Is.a bi ; fa=c = lem26 } ) where
                 lem26 : f (Is.a bi) ≡ Q←F fa (fromℕ< 0<fa)
                 lem26 = trans (Is.fa=c bi) (cong (Q←F fa) (fromℕ<-cong _ _ refl i<fa 0<fa) )
            ... |  yes _ | no nisc = ⊥-elim (nisc record { a = Is.a bj ; fa=c = lem26 } ) where
                 lem26 : f (Is.a bj) ≡ Q←F fa (fromℕ< c)
                 lem26 = trans (Is.fa=c bj) (cong (Q←F fa) (fromℕ<-cong _ _ refl j<fa c) )
            ... | yes isb1 |  yes _ = lem25 where
                 lem14 : count-B 0 ≡ 1
                 lem14 with is-B (Q←F fa ( fromℕ< 0<fa ))
                 ... | no ne = ⊥-elim (ne record {a = Is.a isb1 ; fa=c = trans (Is.fa=c isb1) (cong (λ k → Q←F fa k) (lemma10 refl )) } )
                 ... | yes isb = refl
                 lem25 : 2 ≤ suc (count-B j)
                 lem25 = begin
                    2 ≡⟨ cong suc (sym lem14) ⟩
                    suc (count-B 0) ≤⟨ s≤s (count-B-mono {0} {j} z≤n) ⟩
                    suc (count-B j)  ∎ where open ≤-Reasoning
            lem20 (suc i) zero () i<fa j<fa bi bj
            lem20 (suc i) (suc j) (s≤s i<j) i<fa j<fa bi bj = lem21 where
                 --
                 --                    i  <     suc i  ≤    j
                 --    cb i <  suc (cb i) < cb (suc i) ≤ cb j
                 --
                 lem23 : suc (count-B j) ≡ count-B (suc j)
                 lem23 with <-cmp (finite fa) (suc j)
                 ... | tri< a ¬b ¬c = ⊥-elim (¬c j<fa)
                 ... | tri≈ ¬a b ¬c = ⊥-elim (¬c j<fa)
                 ... | tri> ¬a ¬b c with is-B (Q←F fa (fromℕ< c))
                 ... | yes _ = refl
                 ... | no nisa = ⊥-elim ( nisa record { a = Is.a bj ; fa=c = lem26 } ) where
                     lem26 : f (Is.a bj) ≡ Q←F fa (fromℕ< c)
                     lem26 = trans (Is.fa=c bj) (cong (Q←F fa) (fromℕ<-cong _ _ refl j<fa c) )
                 lem21 : count-B (suc i) < count-B (suc j)
                 lem21 = sx≤py→x≤y ( begin
                     suc (suc (count-B (suc i))) ≤⟨ s≤s ( s≤s ( count-B-mono i<j )) ⟩
                     suc (suc (count-B j)) ≡⟨ cong suc lem23 ⟩
                     suc (count-B (suc j))   ∎ ) where
                        open ≤-Reasoning

            lem08 : i ≡ j
            lem08 with <-cmp i j
            ... | tri< a ¬b ¬c = ⊥-elim (nat-≡< eq ( lem20 i j a i<fa j<fa bi bj  ))
            ... | tri≈ ¬a b ¬c = b
            ... | tri> ¬a ¬b c₁ = ⊥-elim (nat-≡< (sym eq) ( lem20 j i c₁ j<fa i<fa bj bi ))

        lem09 : (i j : ℕ) →  suc n ≤ j → j ≡ count-B i →  CountB n
        lem09 0 (suc j) (s≤s le) eq with is-B (Q←F fa (fromℕ< {0} 0<fa ))
        ... | no nisb = ⊥-elim ( nat-≡< (sym eq) (s≤s z≤n) )
        ... | yes isb with ≤-∨ (s≤s le)
        ... | case1 eq2 = record { b = Is.a isb ; cb = 0 ; b=cn = lem10 ; cb=n = trans lem14 (sym (trans eq2 eq))
                ; cb-inject = λ cb1 c1<fa b1 eq → lem06 0 cb1 0<fa c1<fa isb b1 eq } where
             lem14 : count-B 0 ≡ 1
             lem14 with is-B (Q←F fa ( fromℕ< 0<fa ))
             ... | no ne = ⊥-elim (ne record {a = Is.a isb ; fa=c = trans (Is.fa=c isb) (cong (λ k → Q←F fa k) (lemma10 refl )) } )
             ... | yes isb = refl
             lem10 : 0 ≡ toℕ (F←Q fa (f (Is.a isb)))
             lem10 = begin
                0 ≡⟨ sym ( toℕ-fromℕ< 0<fa ) ⟩
                toℕ (fromℕ< {0} 0<fa ) ≡⟨ cong toℕ (sym (finiso← fa _))  ⟩
                toℕ (F←Q fa (Q←F fa (fromℕ< {0} 0<fa )))  ≡⟨ cong (λ k → toℕ ((F←Q fa k))) (sym (Is.fa=c isb)) ⟩
                toℕ (F←Q fa (f (Is.a isb))) ∎ where open ≡-Reasoning
        ... | case2 (s≤s lt) = ⊥-elim ( nat-≡< (sym eq) (s≤s (<-transʳ z≤n lt)  ))
        lem09 (suc i) (suc j) (s≤s le) eq with <-cmp (finite fa) (suc i)
        ... | tri< a ¬b ¬c = lem09 i (suc j) (s≤s le) eq
        ... | tri≈ ¬a b ¬c = lem09 i (suc j) (s≤s le) eq
        ... | tri> ¬a ¬b c with is-B (Q←F fa (fromℕ< c))
        ... | no nisb = lem09 i (suc j) (s≤s le) eq
        ... | yes isb with ≤-∨ (s≤s le)
        ... | case1 eq2 = record { b = Is.a isb ; cb = suc i ;  b=cn = lem11 ; cb=n = trans lem14 (sym (trans eq2 eq ))
                ; cb-inject = λ cb1 c1<fa b1 eq → lem06 (suc i) cb1 c c1<fa isb b1 eq } where
              lem14 : count-B (suc i) ≡ suc (count-B i)
              lem14 with <-cmp (finite fa) (suc i)
              ... | tri< a₂ ¬b₂ ¬c₂ = ⊥-elim (¬c₂ c)
              ... | tri≈ ¬a₂ b₂ ¬c₂ = ⊥-elim (¬c₂ c)
              ... | tri> ¬a₂ ¬b₂ c₂ with is-B (Q←F fa ( fromℕ< c₂ ))
              ... | yes isb = refl
              ... | no ne = ⊥-elim (ne record {a = Is.a isb ; fa=c = trans (Is.fa=c isb) (cong (λ k → Q←F fa k) (lemma10 refl )) } )
              lem11 : suc i ≡ toℕ (F←Q fa (f (Is.a isb)))
              lem11 = begin
                suc i ≡⟨ sym ( toℕ-fromℕ< c) ⟩
                toℕ (fromℕ< c)  ≡⟨ cong toℕ (sym (finiso← fa _)) ⟩
                toℕ (F←Q fa (Q←F fa (fromℕ< c )))  ≡⟨ cong (λ k → toℕ ((F←Q fa k))) (sym (Is.fa=c isb)) ⟩
                toℕ (F←Q fa (f (Is.a isb))) ∎ where open ≡-Reasoning
        ... | case2 (s≤s lt) = lem09 i j lt (cong pred eq)

    iso0 : (x : Fin maxb) → fromℕ< (cb<mb (CountB.b (cb00 (toℕ x) (fin<n _)))) ≡ x
    iso0 x = begin
         fromℕ< (cb<mb (CountB.b (cb00 (toℕ x) (fin<n _)))) ≡⟨ fromℕ<-cong _ _ ( begin
            pred (count-B (toℕ (F←Q fa (f (CountB.b (cb00 (toℕ x) (fin<n _)))))))  ≡⟨ sym (cong (λ k → pred (count-B k)) (CountB.b=cn CB)) ⟩
            pred (count-B (CountB.cb CB))   ≡⟨ cong pred (CountB.cb=n CB) ⟩
            pred (suc (toℕ x))  ≡⟨ refl ⟩
            toℕ x ∎ ) (cb<mb (CountB.b CB)) (fin<n _) ⟩
         fromℕ< (fin<n {_} x) ≡⟨ fromℕ<-toℕ _ (fin<n {_} x) ⟩
         x ∎ where
             open ≡-Reasoning
             CB = cb00 (toℕ x) (fin<n _)

    iso1 : (b : B) → CountB.b (cb00 (toℕ (fromℕ< (cb<mb b))) (fin<n _)) ≡ b
    iso1 b = begin
         CountB.b CB ≡⟨ InjectiveF.inject fi (F←Q-inject fa (toℕ-injective (begin
            toℕ (F←Q fa (f (CountB.b CB))) ≡⟨ sym (CountB.b=cn CB) ⟩
            CountB.cb CB ≡⟨ CountB.cb-inject CB _ (fin<n _) isb lem30 ⟩
            toℕ (F←Q fa (f b)) ∎ ) ))  ⟩
         b ∎ where
             open ≡-Reasoning
             CB = cb00 (toℕ (fromℕ< (cb<mb b))) (fin<n _)
             isb : Is B A f (Q←F fa (fromℕ< (fin<n {_} (F←Q fa (f b)) )))
             isb = record { a = b ; fa=c = lem33 } where
                 lem33 : f b ≡ Q←F fa (fromℕ< (fin<n (F←Q fa (f b))))
                 lem33 = begin
                     f b ≡⟨ sym (finiso→ fa _) ⟩
                     Q←F fa (F←Q fa (f b))  ≡⟨ cong (Q←F fa) (sym (fromℕ<-toℕ _ (fin<n (F←Q fa (f b))))) ⟩
                     Q←F fa (fromℕ< (fin<n (F←Q fa (f b))))  ∎
             lem30 : count-B (CountB.cb CB) ≡ count-B (toℕ (F←Q fa (InjectiveF.f fi b)))
             lem30 = begin
                 count-B (CountB.cb CB) ≡⟨ CountB.cb=n CB ⟩
                 suc (toℕ (fromℕ< (cb<mb b)))  ≡⟨ cong suc (toℕ-fromℕ< (cb<mb b)) ⟩
                 suc (pred (count-B (toℕ (F←Q fa (f b))))) ≡⟨ sucprd (lem31 b) ⟩
                 count-B (toℕ (F←Q fa (f b))) ∎


-- end
