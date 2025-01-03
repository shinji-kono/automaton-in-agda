{-# OPTIONS --cubical-compatible  --safe #-}

module finiteSetUtil  where

open import Data.Nat hiding ( _≟_ )
open import Data.Fin renaming ( _<_ to _<<_ ; _>_ to _f>_ ; _≟_ to _f≟_ ) hiding (_≤_ ; pred ; _+_ ; _-_ )
open import Data.Fin.Properties hiding ( <-trans ; ≤-trans ; ≤-refl ; <-irrelevant ) renaming ( <-cmp to <-fcmp )
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import logic
open import nat
open import finiteSet
open import fin 
open import bijection 
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
     equal?-refl {x} with <-cmp (toℕ (F←Q x)) (toℕ (F←Q x))
     ... | tri< a ¬b ¬c = ⊥-elim (¬b refl)
     ... | tri≈ ¬a b ¬c = refl
     ... | tri> ¬a ¬b c = ⊥-elim (¬b refl)
     equal→refl  : { x y : Q } → equal? x y ≡ true → x ≡ y
     equal→refl {q0} {q1} eq with <-cmp (toℕ (F←Q q0)) (toℕ (F←Q q1))
     ... | tri< a ¬b ¬c = ⊥-elim (¬-bool refl eq )
     ... | tri≈ ¬a b ¬c = begin
           q0 ≡⟨ sym ( finiso→ q0) ⟩
           Q←F (F←Q q0) ≡⟨ cong (λ k → Q←F k ) (toℕ-injective b) ⟩
           Q←F (F←Q q1) ≡⟨  finiso→   q1 ⟩
           q1 ∎  where open ≡-Reasoning
     ... | tri> ¬a ¬b c = ⊥-elim (¬-bool refl eq)
     eqP : (x y : Q) → Dec0 ( x ≡ y )
     eqP x y  with <-cmp (toℕ (F←Q x)) (toℕ (F←Q y))
     ... | tri< a ¬b ¬c = no0 (λ eq → ¬b (cong (λ k → toℕ (F←Q k)) eq))
     ... | tri≈ ¬a b ¬c = yes0 (subst₂ (λ j k → j ≡ k ) (finiso→ x) (finiso→ y) (cong Q←F (toℕ-injective b)))
     ... | tri> ¬a ¬b c = no0 (λ eq → ¬b (cong (λ k → toℕ (F←Q k)) eq))
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
         found1 (suc m)  m<n end | yes0 eq = subst (λ k → k \/ exists1 m (<to≤  m<n) p ≡ true ) (sym eq) (bool-or-4 {exists1 m (<to≤  m<n) p} )
         found1 (suc m)  m<n end | no0 np = begin
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
         found2 (suc m)  m<n end | yes0 eq = record { found-q = Q←F (fromℕ< m<n) ; found-p = eq }
         found2 (suc m)  m<n end | no0 np =
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
   Q←F f with <-cmp 0 (toℕ f) 
   ... | tri< a ¬b ¬c = case2 ( FiniteSet.Q←F fb (fin-1 f a ))
   ... | tri≈ ¬a b₁ ¬c = case1 one
   ... | tri> ¬a ¬b ()
   F←Q : One ∨ B → Fin (suc b)
   F←Q (case1 one) = zero
   F←Q (case2 f ) = suc (FiniteSet.F←Q fb f)
   finiso→ : (q : One ∨ B) → Q←F (F←Q q) ≡ q
   finiso→ (case1 one) with <-cmp 0 (toℕ (F←Q (case1 one)))
   ... | tri< a ¬b ¬c = refl
   ... | tri≈ ¬a b₁ ¬c = refl
   ... | tri> ¬a ¬b ()
   finiso→ (case2 q) with <-cmp 0 (toℕ (F←Q (case2 q)))
   ... | tri< a ¬b ¬c = cong case2 ( begin
        FiniteSet.Q←F fb (fin-1 (suc (FiniteSet.F←Q fb q)) (s≤s z≤n)) ≡⟨ cong ( FiniteSet.Q←F fb ) (fin-1-sx _ ) ⟩
        FiniteSet.Q←F fb (FiniteSet.F←Q fb q) ≡⟨ FiniteSet.finiso→ fb q ⟩
        q ∎ ) where open ≡-Reasoning
   ... | tri≈ ¬a () ¬c
   ... | tri> ¬a ¬b ()
   finiso← : (q : Fin (suc b)) → F←Q (Q←F q) ≡ q
   finiso← q with <-cmp 0 (toℕ q)
   ... | tri< a ¬b ¬c = trans ( cong suc ( FiniteSet.finiso← fb (fin-1 q a) ) ) (fin-1-xs _ a )
   ... | tri≈ ¬a b₁ ¬c = toℕ-injective b₁
   ... | tri> ¬a ¬b ()

fin-∨1-finite : {B : Set} → (fb : FiniteSet B ) → FiniteSet.finite (fin-∨1 fb) ≡ suc (FiniteSet.finite fb) 
fin-∨1-finite {B} fb = refl

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
 fun← iso (case1 x) with <-cmp 0 (toℕ x)
 ... | tri< a ¬b ¬c = case2 (case1 (fin-1 x a))
 ... | tri≈ ¬a b ¬c = case1 one
 ... | tri> ¬a ¬b ()
 fun← iso (case2 b) = case2 (case2 b)
 fun→ iso (case1 one) = case1 zero
 fun→ iso (case2 (case1 f)) = case1 (suc f)
 fun→ iso (case2 (case2 b)) = case2 b
 fiso← iso (case1 one) = refl
 fiso← iso (case2 (case1 x)) with <-cmp 0 (toℕ x)
 ... | tri< a ¬b ¬c = cong (λ k → case2 (case1 k)) (fin-1-sx x )
 ... | tri≈ ¬a b ¬c = cong (λ k → case2 (case1 k)) (fin-1-sx x )
 ... | tri> ¬a ¬b ()
 fiso← iso (case2 (case2 x)) = refl
 fiso→ iso (case1 x) with <-cmp 0 (toℕ x)
 ... | tri< a ¬b ¬c = cong case1 (fin-1-xs x a)
 ... | tri≈ ¬a b ¬c = cong case1 (toℕ-injective b)
 ... | tri> ¬a ¬b ()
 fiso→ iso (case2 x) = refl

fin-∨2-finite : {B : Set} → (a : ℕ ) → (fb : FiniteSet B ) → FiniteSet.finite (fin-∨2 a fb) ≡ a + FiniteSet.finite fb
fin-∨2-finite {B} zero fb = refl
fin-∨2-finite {B} (suc a) fb = cong suc (fin-∨2-finite {B} a fb )

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

fin-∨-finite : {A B : Set} →  (fa : FiniteSet A ) → (fb : FiniteSet B ) → FiniteSet.finite (fin-∨ fa fb) ≡  FiniteSet.finite fa + FiniteSet.finite fb
fin-∨-finite fa fb =  fin-∨2-finite (FiniteSet.finite fa) fb 

open import Data.Product hiding ( map )

fin-× : {A B : Set} → FiniteSet A → FiniteSet B → FiniteSet (A × B)
fin-× {A} {B}  fa fb = iso-fin (fin-×-f a ) iso-1 where
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
   fun← iso-2 (x , b ) with <-cmp 0 (toℕ x)
   ... | tri< a ¬b ¬c = case2 ( fin-1 x a , b  )
   ... | tri≈ ¬a eq ¬c = case1 b
   ... | tri> ¬a ¬b ()
   fun→ iso-2 (case1 b) = ( zero , b )
   fun→ iso-2 (case2 (a , b )) = ( suc a , b )
   fiso← iso-2 (case1 x) = refl
   fiso← iso-2 (case2 (zero , b)) = refl
   fiso← iso-2 (case2 (suc x , b)) = cong (λ k → case2 (suc k , b)) (sym (toℕ→fromℕ< (fin<n x) x refl ))
   fiso→ iso-2 (x , b ) with <-cmp 0 (toℕ x)
   ... | tri< a ¬b ¬c = cong (λ k → (k , b)) (fin-1-xs x a)
   ... | tri≈ ¬a eq ¬c = cong (λ k → (k , b)) (toℕ-injective eq)
   ... | tri> ¬a ¬b ()

   fin-×-f : ( a  : ℕ ) → FiniteSet ((Fin a) × B)
   fin-×-f zero = record { Q←F = λ () ; F←Q = λ () ; finiso→ = λ () ; finiso← = λ () ; finite = 0 }
   fin-×-f (suc a) = iso-fin ( fin-∨ fb ( fin-×-f a ) ) iso-2

open _∧_

fin-∧ : {A B : Set} → FiniteSet A → FiniteSet B → FiniteSet (A ∧ B)
fin-∧ {A} {B} fa fb = iso-fin (fin-× fa fb) record {
     fun← = λ x → (proj1 x , proj2 x)
   ; fun→ = λ x → ⟪ proj₁ x , proj₂ x ⟫
   ; fiso← = λ x → refl
   ; fiso→ = λ x → refl
   }

-- import Data.Nat.DivMod

open import Data.Vec hiding ( map ; length )
open import Data.Vec.Properties as VP
open import Data.List as DL hiding ( head ; tail )
import Data.Product

exp2 : (n : ℕ ) → exp 2 (suc n) ≡ exp 2 n + exp 2 n
exp2 n = begin
      exp 2 (suc n)
   ≡⟨⟩
      2 * ( exp 2 n )
   ≡⟨ *-comm 2 (exp 2 n)  ⟩
      ( exp 2 n ) * 2
   ≡⟨ *-suc ( exp 2 n ) 1 ⟩
      (exp 2 n ) + ( exp 2 n ) * 1
   ≡⟨ cong ( λ k →  (exp 2 n ) +  k ) (proj₂ *-identity (exp 2 n) ) ⟩
      exp 2 n + exp 2 n
   ∎  where
       open ≡-Reasoning
       open Data.Product

cast-iso : {n m : ℕ } → (eq : n ≡ m ) → (f : Fin m ) → Data.Fin.cast eq ( Data.Fin.cast (sym eq ) f)  ≡ f
cast-iso refl zero =  refl
cast-iso refl (suc f) = cong ( λ k → suc k ) ( cast-iso refl f )

--  cubical compatibliity des not allow 
--
--   finiso→ : (q : Q) → [] ≡ q
--   finiso→ [] = refl
--
--  we need Path to justify the equality which requires cubical
--    F2L-iso : { Q : Set } → (fin : FiniteSet Q ) → (x : Vec Bool (FiniteSet.finite fin) ) → F2L fin a<sa (λ q _ → List2Func fin a<sa x q ) ≡ x
--  requires functional extensionality, it is better to give up Vec Bool n

F2V : {n : ℕ } → (Fin n → Bool ) → Vec Bool n
F2V {n} f = lem n a<sa  where
  lem : (i : ℕ) →  i < suc n → Vec Bool i
  lem zero i<n = []
  lem (suc i) i<n = f (fromℕ< (px≤py i<n )) ∷ lem i (<-trans a<sa i<n )

V2F : {n : ℕ } → Vec Bool n → (Fin n → Bool )
V2F {zero} x f = ⊥-elim ( nat-≤> z≤n (fin<n f) )
V2F {suc n} x f with <-cmp 0 (toℕ f)
... | tri< a ¬b ¬c = V2F (tail x) (fin-1 f a)
... | tri≈ ¬a b ¬c = head x
... | tri> ¬a ¬b ()

Fin2Finite : ( n : ℕ ) → FiniteSet (Fin n)
Fin2Finite n = record { finite = n ; F←Q = λ x → x ; Q←F = λ x → x ; finiso← = λ q → refl ; finiso→ = λ q → refl }

--
--  Fin n → Bool is a finite set
--
fin→iso : {A B F : Set } → FiniteSetF F A → Bijection A B → FiniteSetF F B
fin→iso {A} {B} {F} fa ab = record {
     fin = iso-fin (FiniteSetF.fin fa) ab
     ; F←Q = λ f → Bijection.fun→ ab (FiniteSetF.F←Q fa f)
     ; Q←F = λ b → FiniteSetF.Q←F fa (Bijection.fun← ab b)
     ; finiso← = λ f {g} eq → trans (cong (fun→ ab) (FiniteSetF.finiso← fa (fun← ab f) eq )) (fiso→ ab _ )
     ; finiso→ = λ f q → trans (cong (λ k →  FiniteSetF.Q←F fa k q) (fiso← ab _)) (FiniteSetF.finiso→ fa  f q) 
     }
   
∨-bi : {e1 e2 : ℕ } → Bijection (Fin (e1 + e2)) (Fin e1 ∨ Fin e2) 
∨-bi {e1} {e2} = subst (λ k → Bijection (Fin k) (Fin e1 ∨ Fin e2)) (fin-∨-finite (Fin2Finite e1) (Fin2Finite e2)) (
   FiniteSet→Fin ( fin-∨ {Fin e1} {Fin e2} (Fin2Finite e1) (Fin2Finite e2) ))

fin→ : {n : ℕ} → FiniteSetF (Fin n) (Fin (exp 2 n))
fin→ {zero} = record { fin = Fin2Finite  (exp 2 0) ; F←Q = λ _ → # 0 ; Q←F = λ z () ; finiso← = λ f _ →  fin1≡0 f ; finiso→ = λ f () } 
fin→ {suc n} = fin→iso record { 
         fin = fin-∨ (Fin2Finite e2) (Fin2Finite e2) 
       ; F←Q = F←Q 
       ; Q←F = Q←F 
       ; finiso← = finiso← 
       ; finiso→ = finiso→  } 
            (subst (λ k → Bijection (Fin e2 ∨ Fin e2) (Fin k)) (cong (λ k → e2 + k) (+-comm 0 _ )) (bi-sym _ _ (∨-bi {e2} {e2}))) where
    e2 : ℕ
    e2 = exp 2 n
    fin : FiniteSetF (Fin n) ( Fin (exp 2 n ))
    fin = fin→ {n}
    f00 : (Fin (suc n) → Bool) → (Fin n → Bool) ∨ (Fin n → Bool)
    f00 f  with f (fromℕ< a<sa )
    ... | true  = case1 (λ y → f (fromℕ< (<-trans (fin<n y) a<sa ) ))
    ... | false = case2 (λ y → f (fromℕ< (<-trans (fin<n y) a<sa ) ))
    f01 : (Fin n → Bool) ∨ (Fin n → Bool) → (Fin (suc n) → Bool) 
    f01 (case1 f) x with <-cmp (toℕ x) n
    ... | tri< a ¬b ¬c = f (fromℕ< a ) 
    ... | tri≈ ¬a b ¬c = true
    ... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> c (fin<n x) )
    f01 (case2 f) x with <-cmp (toℕ x) n
    ... | tri< a ¬b ¬c = f (fromℕ< a ) 
    ... | tri≈ ¬a b ¬c = false
    ... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> c (fin<n x) )
    F←Q : (Fin (suc n) → Bool) → Fin e2 ∨ Fin e2
    F←Q f with f00 f 
    ... | case1 f1 = case1 (FiniteSetF.F←Q fin f1)
    ... | case2 f1 = case2 (FiniteSetF.F←Q fin f1)
    Q←F : Fin e2 ∨ Fin e2 → Fin (suc n) → Bool
    Q←F (case1 x) y = f01 (case1 (FiniteSetF.Q←F fin x)) y
    Q←F (case2 x) y = f01 (case2 (FiniteSetF.Q←F fin x)) y

    finiso→ :  (f : Fin (suc n) → Bool) (q : Fin (suc n)) → Q←F (F←Q f) q ≡ f q
    finiso→ f x = finiso→0 where
        lem01 : (a  : toℕ x < n ) → 
           FiniteSetF.Q←F fin→ (FiniteSetF.F←Q fin→ (λ (y  : Fin n) → f (fromℕ< (<-trans (fin<n y) a<sa )))) (fromℕ< a) ≡ f x
        lem01  a = begin
            FiniteSetF.Q←F fin (FiniteSetF.F←Q fin→ (λ (y  : Fin n) → f (fromℕ< (<-trans (fin<n y) a<sa )))) (fromℕ< a) 
               ≡⟨ FiniteSetF.finiso→ fin (λ (y  : Fin n) → f (fromℕ< (<-trans (fin<n y) a<sa ))) (fromℕ<  a) ⟩
            f (fromℕ< (<-trans (fin<n (fromℕ<  a)) a<sa )) ≡⟨ cong f (begin
                fromℕ< (<-trans (fin<n (fromℕ< a)) a<sa )  ≡⟨ fromℕ<-cong _ _ (toℕ-fromℕ< a) (<-trans (fin<n (fromℕ< a)) a<sa ) (fin<n x)  ⟩
                fromℕ< (fin<n x)  ≡⟨ sym ( toℕ→fromℕ< (fin<n x) x refl )  ⟩
                x ∎ ) ⟩
            f x ∎ where open ≡-Reasoning
        lem00 : (b : toℕ x ≡ n) (t : Bool ) (eq : f (fromℕ< a<sa) ≡ t ) → t ≡ f x
        lem00 b t eq = begin
             t ≡⟨ sym eq ⟩
             f _ ≡⟨ cong f ( begin
                fromℕ< a<sa  ≡⟨ fromℕ<-cong _ _ (sym b) a<sa (fin<n x)  ⟩
                fromℕ< (fin<n x)  ≡⟨ sym ( toℕ→fromℕ< (fin<n x) x refl )  ⟩
                x ∎ ) ⟩
             f x ∎ where open ≡-Reasoning
        finiso→0 :  Q←F (F←Q f) x ≡ f x
        finiso→0 with f00 f  | f (fromℕ< a<sa ) in eq
        ... | case1 f1 | true with <-cmp (toℕ x) n
        ... | tri< a ¬b ¬c = lem01 a 
        ... | tri≈ ¬a b ¬c = lem00 b true eq 
        ... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> c (fin<n x) )
        finiso→0 | case1 f1 | false with <-cmp (toℕ x) n
        ... | tri< a ¬b ¬c = lem01 a 
        ... | tri≈ ¬a b ¬c = lem00 b false eq 
        ... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> c (fin<n x) )
        finiso→0 | case2 f1 | true with <-cmp (toℕ x) n
        ... | tri< a ¬b ¬c = lem01 a 
        ... | tri≈ ¬a b ¬c = lem00 b true eq
        ... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> c (fin<n x) )
        finiso→0 | case2 f1 | false with <-cmp (toℕ x) n
        ... | tri< a ¬b ¬c = lem01 a 
        ... | tri≈ ¬a b ¬c = lem00 b false eq
        ... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> c (fin<n x) )

    f-inject :  (p q :  Fin e2 ∨ Fin e2) → ((x : Fin (suc n)) → Q←F p x ≡ Q←F q x) → p ≡ q 
    f-inject (case1 p) (case1 q) EQ = lem00  where
        fn : (p : Fin e2) (x : Fin (suc n)) → Bool
        fn p x = f01 (case1 (FiniteSetF.Q←F fin p)) x
        lem02 : ((x : Fin (suc n)) → fn p x ≡ fn q x ) →  (x : Fin (suc n)) → (x<n : toℕ x < n  )
            → FiniteSetF.Q←F fin p (fromℕ< x<n) ≡  FiniteSetF.Q←F fin q (fromℕ< x<n)
        lem02 eq1 x x<n with <-cmp (toℕ x) n | eq1 x
        ... | tri< a ¬b ¬c | eq2 = eq2
        ... | tri≈ ¬a b ¬c | eq2 = ⊥-elim ( nat-≡< b x<n )
        ... | tri> ¬a ¬b c | eq2 = ⊥-elim ( nat-<> x<n c )
        lem01 : ((x : Fin (suc n)) → fn p x ≡ fn q x ) →  (x : Fin n) → FiniteSetF.Q←F fin p x ≡  FiniteSetF.Q←F fin q x
        lem01 eq1 x = begin
            FiniteSetF.Q←F fin p x ≡⟨ cong (FiniteSetF.Q←F fin p) (toℕ→fromℕ< (fin+1eq< _ (fin<n x)) _ (fin+1eq-≡ℕ _ (fin<n x) ) )  ⟩ 
            FiniteSetF.Q←F fin p (fromℕ< _) ≡⟨ lem02 eq1 (fromℕ< (<-trans (fin<n x) a<sa)) (fin+1eq< _ (fin<n x) ) ⟩
            FiniteSetF.Q←F fin q (fromℕ< _) ≡⟨ sym (cong (FiniteSetF.Q←F fin q) (toℕ→fromℕ< (fin+1eq< _ (fin<n x)) _ (fin+1eq-≡ℕ _ (fin<n x) ) ) ) ⟩ 
            FiniteSetF.Q←F fin q x ∎ where open ≡-Reasoning
        lem00 : case1 p ≡ case1 q
        lem00 = cong case1 ( FiniteSetF.injective-Q←F fin p q (lem01 EQ) )
    f-inject (case1 p) (case2 q) EQ = ⊥-elim (¬-bool (lem02 EQ (fromℕ< a<sa) fin<asa)  refl ) where
        fnp : (x : Fin (suc n)) → Bool
        fnp x = f01 (case1 (FiniteSetF.Q←F fin p)) x
        fnq : (x : Fin (suc n)) → Bool
        fnq x = f01 (case2 (FiniteSetF.Q←F fin q)) x
        lem02 : ((x : Fin (suc n)) → fnp x ≡ fnq x ) →  (x : Fin (suc n)) → (x=n : toℕ x ≡ n  )
            → true ≡ false
        lem02 eq x x=n with <-cmp (toℕ x) n | eq x
        ... | tri< a ¬b ¬c | eq2 = ⊥-elim (¬b x=n)
        ... | tri≈ ¬a b ¬c | eq2 = eq2
        ... | tri> ¬a ¬b c | eq2 = ⊥-elim (¬b x=n)
    f-inject (case2 p) (case1 q) EQ = ⊥-elim (¬-bool (lem02 EQ (fromℕ< a<sa) fin<asa)  refl ) where
        fnp : (x : Fin (suc n)) → Bool
        fnp x = f01 (case2 (FiniteSetF.Q←F fin p)) x
        fnq : (x : Fin (suc n)) → Bool
        fnq x = f01 (case1 (FiniteSetF.Q←F fin q)) x
        lem02 : ((x : Fin (suc n)) → fnp x ≡ fnq x ) →  (x : Fin (suc n)) → (x=n : toℕ x ≡ n  )
            → true ≡ false
        lem02 eq x x=n with <-cmp (toℕ x) n | eq x
        ... | tri< a ¬b ¬c | eq2 = ⊥-elim (¬b x=n)
        ... | tri≈ ¬a b ¬c | eq2 = sym eq2
        ... | tri> ¬a ¬b c | eq2 = ⊥-elim (¬b x=n)
    f-inject (case2 p) (case2 q) EQ = lem00 where
        fn : (p : Fin e2) (x : Fin (suc n)) → Bool
        fn p x = f01 (case2 (FiniteSetF.Q←F fin p)) x
        lem02 : ((x : Fin (suc n)) → fn p x ≡ fn q x ) →  (x : Fin (suc n)) → (x<n : toℕ x < n  )
            → FiniteSetF.Q←F fin p (fromℕ< x<n) ≡  FiniteSetF.Q←F fin q (fromℕ< x<n)
        lem02 eq1 x x<n with <-cmp (toℕ x) n | eq1 x
        ... | tri< a ¬b ¬c | eq2 = eq2
        ... | tri≈ ¬a b ¬c | eq2 = ⊥-elim ( nat-≡< b x<n )
        ... | tri> ¬a ¬b c | eq2 = ⊥-elim ( nat-<> x<n c )
        lem01 : ((x : Fin (suc n)) → fn p x ≡ fn q x ) →  (x : Fin n) → FiniteSetF.Q←F fin p x ≡  FiniteSetF.Q←F fin q x
        lem01 eq1 x = begin
            FiniteSetF.Q←F fin p x ≡⟨ cong (FiniteSetF.Q←F fin p) (toℕ→fromℕ< (fin+1eq< _ (fin<n x)) _ (fin+1eq-≡ℕ _ (fin<n x) ) )  ⟩ 
            FiniteSetF.Q←F fin p (fromℕ< _) ≡⟨ lem02 eq1 (fromℕ< (<-trans (fin<n x) a<sa)) (fin+1eq< _ (fin<n x) ) ⟩
            FiniteSetF.Q←F fin q (fromℕ< _) ≡⟨ sym (cong (FiniteSetF.Q←F fin q) (toℕ→fromℕ< (fin+1eq< _ (fin<n x)) _ (fin+1eq-≡ℕ _ (fin<n x) ) ) ) ⟩ 
            FiniteSetF.Q←F fin q x ∎ where open ≡-Reasoning
        lem00 : case2 p ≡ case2 q
        lem00 = cong case2 ( FiniteSetF.injective-Q←F fin p q (lem01 EQ) )

    finiso← : (f : Fin e2 ∨ Fin e2) {g : Fin (suc n) → Bool} → ((q : Fin (suc n)) → g q ≡ Q←F f q) → F←Q g ≡ f
    finiso← f {g} EQ = f-inject (F←Q g) f (λ x → trans (finiso→ g x ) (EQ x ))


--
-- fin→ is in finiteFunc.agda
--      we excludeit becauase it uses f-extensionarityhh

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
   → (is-B : (a : A ) → Dec0 (Is B A (InjectiveF.f fi) a)  )
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
    0<fa = <-≤-trans (s≤s z≤n) pfa<fa

    count-B : ℕ → ℕ
    count-B zero with is-B (Q←F fa ( fromℕ< {0} 0<fa ))
    ... | yes0 isb = 1
    ... | no0 nisb = 0
    count-B (suc n) with <-cmp (finite fa) (suc n)
    ... | tri< a ¬b ¬c = count-B n
    ... | tri≈ ¬a b ¬c = count-B n
    ... | tri> ¬a ¬b c with is-B (Q←F fa (fromℕ< c))
    ... | yes0 isb = suc (count-B n)
    ... | no0 nisb = count-B n

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
    ... | case2 i<j = cb02 _ _ i<j where
        cb01 : (i : ℕ) → 0 < i → (count-B (Data.Nat.pred i) ≡ count-B i) ∨ (suc (count-B (Data.Nat.pred i)) ≡ count-B i)
        cb01 zero ()
        cb01 (suc i) 0<i with <-cmp (finite fa) (suc i)
        ... | tri< a ¬b ¬c = case1 refl
        ... | tri≈ ¬a b ¬c = case1 refl
        ... | tri> ¬a ¬b c with is-B (Q←F fa (fromℕ< c))
        ... | yes0 isb = case2 refl
        ... | no0 nisb = case1 refl
        lem01 : (j : ℕ) → 0 < j  → count-B (Data.Nat.pred j) ≤ count-B j
        lem01 j 0<j with cb01 j 0<j
        ... | case1 eq = subst (λ k → count-B (Data.Nat.pred j) ≤ k ) eq (≤-refl)
        ... | case2 eq = subst (λ k → count-B (Data.Nat.pred j) ≤ k ) eq a≤sa
        cb02 : (i j : ℕ) → i < j  → count-B i ≤ count-B j
        cb02 i zero ()
        cb02 i (suc j) lt     =  ≤-trans (count-B-mono (x<sy→x≤y lt) ) (lem01 (suc j ) (≤-trans (s≤s z≤n) lt))


    lem31 : (b : B) → 0 < count-B (toℕ (F←Q fa (f b)))
    lem31 b = lem32 (toℕ (F←Q fa (f b))) refl where
        lem32 : (i : ℕ) → toℕ (F←Q fa (f b)) ≡ i → 0 < count-B i
        lem32 zero   eq with is-B (Q←F fa ( fromℕ< {0} 0<fa ))
        ... | yes0 isb = s≤s z≤n
        ... | no0 nisb = ⊥-elim ( nisb record { a = b ; fa=c = lem33 } ) where
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
        ... | yes0 isb = s≤s z≤n
        ... | no0 nisb = ⊥-elim ( nisb record { a = b ; fa=c = lem33 } ) where
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
    cb00 n n<cb = lem09 (finite fa) (count-B (finite fa)) (<-≤-trans a<sa n<cb) refl where
        lem06 : (i j : ℕ) → (i<fa : i < finite fa) (j<fa : j < finite fa)
            →  Is B A f (Q←F fa (fromℕ< i<fa)) → Is B A f (Q←F fa (fromℕ< j<fa)) → count-B i ≡ count-B j → i ≡ j
        lem06 i j i<fa j<fa bi bj eq = lem08 where
            lem20 : (i j : ℕ) → i < j → (i<fa : i < finite fa) (j<fa : j < finite fa)
                →  Is B A f (Q←F fa (fromℕ< i<fa)) → Is B A f (Q←F fa (fromℕ< j<fa)) → count-B i < count-B j
            lem20 zero zero () i<fa j<fa bi bj
            lem20 zero (suc j) i<j i<fa j<fa bi bj with <-cmp (finite fa) (suc j)
            ... | tri< a ¬b ¬c = ⊥-elim (¬c j<fa)
            ... | tri≈ ¬a b ¬c = ⊥-elim (¬c j<fa)
            ... | tri> ¬a ¬b c with  is-B (Q←F fa ( fromℕ< 0<fa )) |  is-B (Q←F fa (fromℕ< c))
            ... | no0 nisc  | _ = ⊥-elim (nisc record { a = Is.a bi ; fa=c = lem26 } ) where
                 lem26 : f (Is.a bi) ≡ Q←F fa (fromℕ< 0<fa)
                 lem26 = trans (Is.fa=c bi) (cong (Q←F fa) (fromℕ<-cong _ _ refl i<fa 0<fa) )
            ... |  yes0 _ | no0 nisc = ⊥-elim (nisc record { a = Is.a bj ; fa=c = lem26 } ) where
                 lem26 : f (Is.a bj) ≡ Q←F fa (fromℕ< c)
                 lem26 = trans (Is.fa=c bj) (cong (Q←F fa) (fromℕ<-cong _ _ refl j<fa c) )
            ... | yes0 isb1 |  yes0 _ = lem25 where
                 lem14 : count-B 0 ≡ 1
                 lem14 with is-B (Q←F fa ( fromℕ< 0<fa ))
                 ... | no0 ne = ⊥-elim (ne record {a = Is.a isb1 ; fa=c = trans (Is.fa=c isb1) (cong (λ k → Q←F fa k) (lemma10 refl i<fa i<fa )) } )
                 ... | yes0 isb = refl
                 lem25 : 2 ≤ suc (count-B j)
                 lem25 = begin
                    2 ≡⟨ cong suc (sym lem14) ⟩
                    suc (count-B 0) ≤⟨ s≤s (count-B-mono {0} {j} z≤n) ⟩
                    suc (count-B j)  ∎ where open ≤-Reasoning
            lem20 (suc i) zero () i<fa j<fa bi bj
            lem20 (suc i) (suc j) lt i<fa j<fa bi bj = lem21 where
                 --
                 --                    i  <     suc i  ≤    j
                 --    cb i <  suc (cb i) < cb (suc i) ≤ cb j
                 --
                 lem23 : suc (count-B j) ≡ count-B (suc j)
                 lem23 with <-cmp (finite fa) (suc j)
                 ... | tri< a ¬b ¬c = ⊥-elim (¬c j<fa)
                 ... | tri≈ ¬a b ¬c = ⊥-elim (¬c j<fa)
                 ... | tri> ¬a ¬b c with is-B (Q←F fa (fromℕ< c))
                 ... | yes0 _ = refl
                 ... | no0 nisa = ⊥-elim ( nisa record { a = Is.a bj ; fa=c = lem26 } ) where
                     lem26 : f (Is.a bj) ≡ Q←F fa (fromℕ< c)
                     lem26 = trans (Is.fa=c bj) (cong (Q←F fa) (fromℕ<-cong _ _ refl j<fa c) )
                 lem21 : count-B (suc i) < count-B (suc j)
                 lem21 = sx≤py→x≤y ( begin
                     suc (suc (count-B (suc i))) ≤⟨ s≤s ( s≤s ( count-B-mono (px≤py lt)  )) ⟩
                     suc (suc (count-B j)) ≡⟨ cong suc lem23 ⟩
                     suc (count-B (suc j))   ∎ ) where
                        open ≤-Reasoning

            lem08 : i ≡ j
            lem08 with <-cmp i j
            ... | tri< a ¬b ¬c = ⊥-elim (nat-≡< eq ( lem20 i j a i<fa j<fa bi bj  ))
            ... | tri≈ ¬a b ¬c = b
            ... | tri> ¬a ¬b c₁ = ⊥-elim (nat-≡< (sym eq) ( lem20 j i c₁ j<fa i<fa bj bi ))

        lem09 : (i j : ℕ) →  suc n ≤ j → j ≡ count-B i →  CountB n
        lem09 (suc i) 0 () eq
        lem09 0 0 () eq
        lem09 0 (suc j) le eq with is-B (Q←F fa (fromℕ< {0} 0<fa ))
        ... | no0 nisb = ⊥-elim ( nat-≡< (sym eq) (s≤s z≤n) )
        ... | yes0 isb with ≤-∨ (s≤s le)
        ... | case1 eq2 = record { b = Is.a isb ; cb = 0 ; b=cn = lem10 ; cb=n = trans lem14 (sym (trans (cong Data.Nat.pred eq2) eq))
                ; cb-inject = λ cb1 c1<fa b1 eq → lem06 0 cb1 0<fa c1<fa isb b1 eq } where
             lem14 : count-B 0 ≡ 1
             lem14 with is-B (Q←F fa ( fromℕ< 0<fa ))
             ... | no0 ne = ⊥-elim (ne record {a = Is.a isb ; fa=c = trans (Is.fa=c isb) (cong (λ k → Q←F fa k) (lemma10 refl 0<fa 0<fa )) } )
             ... | yes0 isb = refl
             lem10 : 0 ≡ toℕ (F←Q fa (f (Is.a isb)))
             lem10 = begin
                0 ≡⟨ sym ( toℕ-fromℕ< 0<fa ) ⟩
                toℕ (fromℕ< {0} 0<fa ) ≡⟨ cong toℕ (sym (finiso← fa _))  ⟩
                toℕ (F←Q fa (Q←F fa (fromℕ< {0} 0<fa )))  ≡⟨ cong (λ k → toℕ ((F←Q fa k))) (sym (Is.fa=c isb)) ⟩
                toℕ (F←Q fa (f (Is.a isb))) ∎ where open ≡-Reasoning
        ... | case2 lt = ⊥-elim (nat-≤> (sx≤py→x≤y lt) (subst (λ k → k < suc (suc n)) (sym eq) (s≤s (s≤s z≤n)) ))
        lem09 (suc i) (suc j) le eq with <-cmp (finite fa) (suc i)
        ... | tri< a ¬b ¬c = lem09 i (suc j) le eq
        ... | tri≈ ¬a b ¬c = lem09 i (suc j) le eq
        ... | tri> ¬a ¬b c with is-B (Q←F fa (fromℕ< c))
        ... | no0 nisb = lem09 i (suc j) le eq
        ... | yes0 isb with ≤-∨ le
        ... | case1 eq2 = record { b = Is.a isb ; cb = suc i ;  b=cn = lem11 ; cb=n = trans lem14 (sym (trans eq2 eq ))
                ; cb-inject = λ cb1 c1<fa b1 eq → lem06 (suc i) cb1 c c1<fa isb b1 eq } where
              lem14 : count-B (suc i) ≡ suc (count-B i)
              lem14 with <-cmp (finite fa) (suc i)
              ... | tri< a₂ ¬b₂ ¬c₂ = ⊥-elim (¬c₂ c)
              ... | tri≈ ¬a₂ b₂ ¬c₂ = ⊥-elim (¬c₂ c)
              ... | tri> ¬a₂ ¬b₂ c₂ with is-B (Q←F fa ( fromℕ< c₂ ))
              ... | yes0 isb = refl
              ... | no0 ne = ⊥-elim (ne record {a = Is.a isb ; fa=c = trans (Is.fa=c isb) (cong (λ k → Q←F fa k) (lemma10 refl c c )) } )
              lem11 : suc i ≡ toℕ (F←Q fa (f (Is.a isb)))
              lem11 = begin
                suc i ≡⟨ sym ( toℕ-fromℕ< c) ⟩
                toℕ (fromℕ< c)  ≡⟨ cong toℕ (sym (finiso← fa _)) ⟩
                toℕ (F←Q fa (Q←F fa (fromℕ< c )))  ≡⟨ cong (λ k → toℕ ((F←Q fa k))) (sym (Is.fa=c isb)) ⟩
                toℕ (F←Q fa (f (Is.a isb))) ∎ where open ≡-Reasoning
        ... | case2 lt = lem09 i j (px≤py lt) (cong pred eq)

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
