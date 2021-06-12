{-# OPTIONS --allow-unsolved-metas #-} 

module finiteSetUtil  where

open import Data.Nat hiding ( _≟_ )
open import Data.Fin renaming ( _<_ to _<<_ ) hiding (_≤_)
open import Data.Fin.Properties
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import logic
open import nat
open import finiteSet
open import fin
open import Data.Nat.Properties as NatP  hiding ( _≟_ )
open import Relation.Binary.HeterogeneousEquality as HE using (_≅_ ) 

record Found ( Q : Set ) (p : Q → Bool ) : Set where
     field
       found-q : Q
       found-p : p found-q ≡ true

module _ {Q : Set } (F : FiniteSet Q) where
     open FiniteSet F
     equal→refl  : { x y : Q } → equal? x y ≡ true → x ≡ y
     equal→refl {q0} {q1} eq with F←Q q0 ≟ F←Q q1
     equal→refl {q0} {q1} refl | yes eq = begin
            q0
        ≡⟨ sym ( finiso→ q0) ⟩
            Q←F (F←Q q0)
        ≡⟨ cong (λ k → Q←F k ) eq ⟩
            Q←F (F←Q q1)
        ≡⟨ finiso→ q1 ⟩
            q1
        ∎  where open ≡-Reasoning
     End : (m : ℕ ) → (p : Q → Bool ) → Set
     End m p = (i : Fin finite) → m ≤ toℕ i → p (Q←F i )  ≡ false 
     first-end :  ( p : Q → Bool ) → End finite p
     first-end p i i>n = ⊥-elim (nat-≤> i>n (fin<n {finite} {i}) )
     next-end : {m : ℕ } → ( p : Q → Bool ) → End (suc m) p
              → (m<n : m < finite ) → p (Q←F (fromℕ< m<n )) ≡ false
              → End m p
     next-end {m} p prev m<n np i m<i with NatP.<-cmp m (toℕ i) 
     next-end p prev m<n np i m<i | tri< a ¬b ¬c = prev i a
     next-end p prev m<n np i m<i | tri> ¬a ¬b c = ⊥-elim ( nat-≤> m<i c )
     next-end {m} p prev m<n np i m<i | tri≈ ¬a b ¬c = subst ( λ k → p (Q←F k) ≡ false) (m<n=i i b m<n ) np where
              m<n=i : {n : ℕ } (i : Fin n) {m : ℕ } → m ≡ (toℕ i) → (m<n : m < n )  → fromℕ< m<n ≡ i
              m<n=i i eq m<n = {!!} -- toℕ-inject (fromℕ≤ ?) i (subst (λ k → k ≡ toℕ i) (sym (toℕ-fromℕ≤ m<n)) eq )
     found : { p : Q → Bool } → (q : Q ) → p q ≡ true → exists p ≡ true
     found {p} q pt = found1 finite  (NatP.≤-refl ) ( first-end p ) where
         found1 : (m : ℕ ) (m<n : m Data.Nat.≤ finite ) → ((i : Fin finite) → m ≤ toℕ i → p (Q←F i )  ≡ false ) →  exists1 m m<n p ≡ true
         found1 0 m<n end = ⊥-elim ( ¬-bool (subst (λ k → k ≡ false ) (cong (λ k → p k) (finiso→ q) ) (end (F←Q q) z≤n )) pt )
         found1 (suc m)  m<n end with bool-≡-? (p (Q←F (fromℕ< m<n))) true
         found1 (suc m)  m<n end | yes eq = subst (λ k → k \/ exists1 m (≤to<  m<n) p ≡ true ) (sym eq) (bool-or-4 {exists1 m (≤to<  m<n) p} ) 
         found1 (suc m)  m<n end | no np = begin
                 p (Q←F (fromℕ< m<n)) \/ exists1 m (≤to<  m<n) p
              ≡⟨ bool-or-1 (¬-bool-t np ) ⟩
                 exists1 m (≤to<  m<n) p
              ≡⟨ found1 m (≤to<  m<n) (next-end p end m<n (¬-bool-t np )) ⟩
                 true
              ∎  where open ≡-Reasoning



record ISO (A B : Set) : Set where
   field
     A←B : B → A
     B←A : A → B
     iso← : (q : A) → A←B ( B←A q ) ≡ q
     iso→ : (f : B) → B←A ( A←B f ) ≡ f

iso-fin : {A B : Set} → FiniteSet A  → ISO A B → FiniteSet B 
iso-fin {A} {B}  fin iso = record {
   Q←F = λ f → ISO.B←A iso ( FiniteSet.Q←F fin f )
 ; F←Q = λ b → FiniteSet.F←Q fin ( ISO.A←B iso b )
 ; finiso→ = finiso→ 
 ; finiso← = finiso← 
   } where
   finiso→ : (q : B) → ISO.B←A iso (FiniteSet.Q←F fin (FiniteSet.F←Q fin (ISO.A←B iso q))) ≡ q
   finiso→ q = begin
              ISO.B←A iso (FiniteSet.Q←F fin (FiniteSet.F←Q fin (ISO.A←B iso q))) 
           ≡⟨ cong (λ k → ISO.B←A iso k ) (FiniteSet.finiso→ fin _ ) ⟩
              ISO.B←A iso (ISO.A←B iso q)
           ≡⟨ ISO.iso→ iso _ ⟩
              q
           ∎  where
           open ≡-Reasoning
   finiso← : (f : Fin (FiniteSet.finite fin ))→ FiniteSet.F←Q fin (ISO.A←B iso (ISO.B←A iso (FiniteSet.Q←F fin f))) ≡ f
   finiso← f = begin
              FiniteSet.F←Q fin (ISO.A←B iso (ISO.B←A iso (FiniteSet.Q←F fin f))) 
           ≡⟨ cong (λ k → FiniteSet.F←Q fin k ) (ISO.iso← iso _) ⟩
              FiniteSet.F←Q fin (FiniteSet.Q←F fin f) 
           ≡⟨ FiniteSet.finiso← fin _  ⟩
              f
           ∎  where
           open ≡-Reasoning

data One : Set where
   one : One

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
   iso : ISO B (Fin zero ∨ B)
   iso =  record {
        A←B = A←B
      ; B←A = λ b → case2 b
      ; iso→ = iso→
      ; iso← = λ _ → refl
    } where
     A←B : Fin zero ∨ B → B
     A←B (case2 x) = x 
     iso→ : (f : Fin zero ∨ B ) → case2 (A←B f) ≡ f
     iso→ (case2 x)  = refl
fin-∨2 {B} (suc a) fb =  iso-fin (fin-∨1 (fin-∨2 a fb) ) iso
    where
  iso : ISO (One ∨ (Fin a ∨ B) ) (Fin (suc a) ∨ B)
  ISO.A←B iso (case1 zero) = case1 one
  ISO.A←B iso (case1 (suc f)) = case2 (case1 f)
  ISO.A←B iso (case2 b) = case2 (case2 b)
  ISO.B←A iso (case1 one) = case1 zero
  ISO.B←A iso (case2 (case1 f)) = case1 (suc f)
  ISO.B←A iso (case2 (case2 b)) = case2 b
  ISO.iso← iso (case1 one) = refl
  ISO.iso← iso (case2 (case1 x)) = refl
  ISO.iso← iso (case2 (case2 x)) = refl
  ISO.iso→ iso (case1 zero) = refl
  ISO.iso→ iso (case1 (suc x)) = refl
  ISO.iso→ iso (case2 x) = refl


FiniteSet→Fin : {A : Set} → (fin : FiniteSet A  ) → ISO (Fin (FiniteSet.finite fin)) A
ISO.A←B (FiniteSet→Fin fin) f = FiniteSet.F←Q fin f
ISO.B←A (FiniteSet→Fin fin) f = FiniteSet.Q←F fin f
ISO.iso← (FiniteSet→Fin fin) = FiniteSet.finiso← fin
ISO.iso→ (FiniteSet→Fin fin) =  FiniteSet.finiso→ fin
   

fin-∨ : {A B : Set} → FiniteSet A → FiniteSet B → FiniteSet (A ∨ B) 
fin-∨ {A} {B}  fa fb = iso-fin (fin-∨2 a  fb ) iso2 where
    a = FiniteSet.finite fa
    ia = FiniteSet→Fin fa
    iso2 : ISO (Fin a ∨ B ) (A ∨ B)
    ISO.A←B iso2 (case1 x) = case1 ( ISO.A←B ia x )
    ISO.A←B iso2 (case2 x) = case2 x
    ISO.B←A iso2 (case1 x) = case1 ( ISO.B←A ia x )
    ISO.B←A iso2 (case2 x) = case2 x
    ISO.iso← iso2 (case1 x) = cong ( λ k → case1 k ) (ISO.iso← ia x)
    ISO.iso← iso2 (case2 x) = refl
    ISO.iso→ iso2 (case1 x) = cong ( λ k → case1 k ) (ISO.iso→ ia x)
    ISO.iso→ iso2 (case2 x) = refl

open import Data.Product

fin-× : {A B : Set} → FiniteSet A → FiniteSet B → FiniteSet (A × B) 
fin-× {A} {B}  fa fb with FiniteSet→Fin fa
... | a=f = iso-fin (fin-×-f a ) iso-1 where
   a = FiniteSet.finite fa
   b = FiniteSet.finite fb
   iso-1 : ISO (Fin a × B) ( A × B )
   ISO.A←B iso-1 x = ( FiniteSet.F←Q fa (proj₁ x)  , proj₂ x) 
   ISO.B←A iso-1 x = ( FiniteSet.Q←F fa (proj₁ x)  , proj₂ x) 
   ISO.iso← iso-1 x  =  lemma  where
     lemma : (FiniteSet.F←Q fa (FiniteSet.Q←F fa (proj₁ x)) , proj₂ x) ≡ ( proj₁ x , proj₂ x )
     lemma = cong ( λ k → ( k ,  proj₂ x ) )  (FiniteSet.finiso← fa _ )
   ISO.iso→ iso-1 x = cong ( λ k → ( k ,  proj₂ x ) )  (FiniteSet.finiso→ fa _ )

   iso-2 : {a : ℕ } → ISO (B ∨ (Fin a × B)) (Fin (suc a) × B)
   ISO.A←B iso-2 (zero , b ) = case1 b
   ISO.A←B iso-2 (suc fst , b ) = case2 ( fst , b )
   ISO.B←A iso-2 (case1 b) = ( zero , b )
   ISO.B←A iso-2 (case2 (a , b )) = ( suc a , b )
   ISO.iso← iso-2 (case1 x) = refl
   ISO.iso← iso-2 (case2 x) = refl
   ISO.iso→ iso-2 (zero , b ) = refl
   ISO.iso→ iso-2 (suc a , b ) = refl

   fin-×-f : ( a  : ℕ ) → FiniteSet ((Fin a) × B) 
   fin-×-f zero = record { Q←F = λ () ; F←Q = λ () ; finiso→ = λ () ; finiso← = λ () ; finite = 0 }
   fin-×-f (suc a) = iso-fin ( fin-∨ fb ( fin-×-f a ) ) iso-2

open _∧_

fin-∧ : {A B : Set} → FiniteSet A → FiniteSet B → FiniteSet (A ∧ B) 
fin-∧ {A} {B} fa fb with FiniteSet→Fin fa    -- same thing for our tool
... | a=f = iso-fin (fin-×-f a ) iso-1 where
   a = FiniteSet.finite fa
   b = FiniteSet.finite fb
   iso-1 : ISO (Fin a ∧ B) ( A ∧ B )
   ISO.A←B iso-1 x = record { proj1 = FiniteSet.F←Q fa (proj1 x)  ; proj2 =  proj2 x} 
   ISO.B←A iso-1 x = record { proj1 = FiniteSet.Q←F fa (proj1 x)  ; proj2 =  proj2 x}
   ISO.iso← iso-1 x  =  lemma  where
     lemma : record { proj1 = FiniteSet.F←Q fa (FiniteSet.Q←F fa (proj1 x)) ; proj2 =  proj2 x} ≡ record {proj1 =  proj1 x ; proj2 =  proj2 x }
     lemma = cong ( λ k → record {proj1 = k ;  proj2 = proj2 x } )  (FiniteSet.finiso← fa _ )
   ISO.iso→ iso-1 x = cong ( λ k → record {proj1 =  k ; proj2 =  proj2 x } )  (FiniteSet.finiso→ fa _ )

   iso-2 : {a : ℕ } → ISO (B ∨ (Fin a ∧ B)) (Fin (suc a) ∧ B)
   ISO.A←B iso-2 (record { proj1 = zero ; proj2 =  b }) = case1 b
   ISO.A←B iso-2 (record { proj1 = suc fst ; proj2 =  b }) = case2 ( record { proj1 = fst ; proj2 =  b } )
   ISO.B←A iso-2 (case1 b) = record {proj1 =  zero ; proj2 =  b }
   ISO.B←A iso-2 (case2 (record { proj1 = a ; proj2 =  b })) = record { proj1 =  suc a ; proj2 =  b }
   ISO.iso← iso-2 (case1 x) = refl
   ISO.iso← iso-2 (case2 x) = refl
   ISO.iso→ iso-2 (record { proj1 = zero ; proj2 =  b }) = refl
   ISO.iso→ iso-2 (record { proj1 = suc a ; proj2 =  b }) = refl

   fin-×-f : ( a  : ℕ ) → FiniteSet ((Fin a) ∧ B) 
   fin-×-f zero = record { Q←F = λ () ; F←Q = λ () ; finiso→ = λ () ; finiso← = λ () ; finite = 0 }
   fin-×-f (suc a) = iso-fin ( fin-∨ fb ( fin-×-f a ) ) iso-2

-- import Data.Nat.DivMod

open import Data.Vec
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

cast-iso : {n m : ℕ } → (eq : n ≡ m ) → (f : Fin m ) → cast eq ( cast (sym eq ) f)  ≡ f
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
   iso : ISO (Vec Bool n ∨ Vec Bool n) (Vec Bool (suc n))
   iso = record { A←B = QtoR ; B←A = RtoQ ; iso← = isoQR ; iso→ = isoRQ  }

F2L : {Q : Set } {n : ℕ } → (fin : FiniteSet Q ) → n < suc (FiniteSet.finite fin) → ( (q : Q) → toℕ (FiniteSet.F←Q fin q ) < n  → Bool ) → Vec Bool n
F2L  {Q} {zero} fin _ Q→B = []
F2L  {Q} {suc n} fin (s≤s n<m) Q→B = Q→B (FiniteSet.Q←F fin (fromℕ< n<m)) lemma6 ∷ F2L {Q} fin (NatP.<-trans n<m a<sa ) qb1 where
   lemma6 : toℕ (FiniteSet.F←Q fin (FiniteSet.Q←F fin (fromℕ< n<m))) < suc n
   lemma6 = subst (λ k → toℕ k < suc n ) (sym (FiniteSet.finiso← fin _ )) (subst (λ k → k < suc n) (sym (toℕ-fromℕ< n<m ))  a<sa )
   qb1 : (q : Q) → toℕ (FiniteSet.F←Q fin q) < n → Bool
   qb1 q q<n = Q→B q (NatP.<-trans q<n a<sa)

List2Func : { Q : Set } → {n : ℕ } → (fin : FiniteSet Q ) → n < suc (FiniteSet.finite fin)  → Vec Bool n →  Q → Bool 
List2Func {Q} {zero} fin (s≤s z≤n) [] q = false
List2Func {Q} {suc n} fin (s≤s n<m) (h ∷ t) q with  FiniteSet.F←Q fin q ≟ fromℕ< n<m
... | yes _ = h
... | no _ = List2Func {Q} fin (NatP.<-trans n<m a<sa ) t q

open import Level renaming ( suc to Suc ; zero to Zero) 
open import Axiom.Extensionality.Propositional
postulate f-extensionality : { n : Level}  →  Axiom.Extensionality.Propositional.Extensionality n n 

F2L-iso : { Q : Set } → (fin : FiniteSet Q ) → (x : Vec Bool (FiniteSet.finite fin) ) → F2L fin a<sa (λ q _ → List2Func fin a<sa x q ) ≡ x
F2L-iso {Q} fin x = f2l m a<sa x where
  m = FiniteSet.finite fin
  f2l : (n : ℕ ) → (n<m : n < suc m )→ (x : Vec Bool n ) → F2L fin n<m (λ q q<n → List2Func fin n<m x q )  ≡ x 
  f2l zero (s≤s z≤n) [] = refl
  f2l (suc n) (s≤s n<m) (h ∷ t ) = lemma1 lemma2 lemma3f where
    lemma1 : {n : ℕ } → {h h1 : Bool } → {t t1 : Vec Bool n } → h ≡ h1 → t ≡ t1 →  h ∷ t ≡ h1 ∷ t1
    lemma1 refl refl = refl
    lemma2 : List2Func fin (s≤s n<m) (h ∷ t) (FiniteSet.Q←F fin (fromℕ< n<m)) ≡ h
    lemma2 with FiniteSet.F←Q fin (FiniteSet.Q←F fin (fromℕ< n<m))  ≟ fromℕ< n<m
    lemma2 | yes p = refl
    lemma2 | no ¬p = ⊥-elim ( ¬p (FiniteSet.finiso← fin _) )
    lemma4 : (q : Q ) → toℕ (FiniteSet.F←Q fin q ) < n → List2Func fin (s≤s n<m) (h ∷ t) q ≡ List2Func fin (NatP.<-trans n<m a<sa) t q
    lemma4 q _ with FiniteSet.F←Q fin q ≟ fromℕ< n<m 
    lemma4 q lt | yes p = ⊥-elim ( nat-≡< (toℕ-fromℕ< n<m) (lemma5 n lt (cong (λ k → toℕ k) p))) where 
        lemma5 : {j k : ℕ } → ( n : ℕ) → suc j ≤ n → j ≡ k → k < n
        lemma5 {zero} (suc n) (s≤s z≤n) refl = s≤s  z≤n
        lemma5 {suc j} (suc n) (s≤s lt) refl = s≤s (lemma5 {j} n lt refl)
    lemma4 q _ | no ¬p = refl
    lemma3f :  F2L fin (NatP.<-trans n<m a<sa) (λ q q<n → List2Func fin (s≤s n<m) (h ∷ t) q  ) ≡ t
    lemma3f = begin 
         F2L fin (NatP.<-trans n<m a<sa) (λ q q<n → List2Func fin (s≤s n<m) (h ∷ t) q )
       ≡⟨ cong (λ k → F2L fin (NatP.<-trans n<m a<sa) ( λ q q<n → k q q<n ))
              (f-extensionality ( λ q →  
              (f-extensionality ( λ q<n →  lemma4 q q<n )))) ⟩
         F2L fin (NatP.<-trans n<m a<sa) (λ q q<n → List2Func fin (NatP.<-trans n<m a<sa) t q )
       ≡⟨ f2l n (NatP.<-trans n<m a<sa ) t ⟩
         t
       ∎  where
         open ≡-Reasoning


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
     lemma13 {suc n} {suc nq} n<m nt (s≤s nq≤n) = s≤s (lemma13 {n} {nq} (NatP.<-trans a<sa n<m ) (λ eq → nt ( cong ( λ k → suc k ) eq )) nq≤n)
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
  l2f (suc n) (s≤s n<m) (s≤s n<q) | no ¬p = l2f n (NatP.<-trans n<m a<sa) (lemma11f n<m ¬p n<q)

fin→ : {A : Set} → FiniteSet A → FiniteSet (A → Bool ) 
fin→ {A}  fin = iso-fin fin2List iso where
    a = FiniteSet.finite fin
    iso : ISO (Vec Bool a ) (A → Bool)
    ISO.A←B iso x = F2L fin a<sa ( λ q _ → x q )
    ISO.B←A iso x = List2Func fin a<sa x 
    ISO.iso← iso x  =  F2L-iso fin x 
    ISO.iso→ iso x = lemma where
      lemma : List2Func fin a<sa (F2L fin a<sa (λ q _ → x q)) ≡ x
      lemma = f-extensionality ( λ q → L2F-iso fin x q )
    

Fin2Finite : ( n : ℕ ) → FiniteSet (Fin n) 
Fin2Finite n = record { F←Q = λ x → x ; Q←F = λ x → x ; finiso← = λ q → refl ; finiso→ = λ q → refl }

data fin-less { n : ℕ } { A : Set }  (fa : FiniteSet A ) (n<m : n < FiniteSet.finite fa ) : Set where
  elm1 : (elm : A ) → toℕ (FiniteSet.F←Q fa elm ) < n → fin-less fa n<m 

get-elm : { n : ℕ }  { A : Set } {fa : FiniteSet A } {n<m : n < FiniteSet.finite fa } → fin-less fa n<m → A
get-elm (elm1 a _ ) = a

get-< : { n : ℕ }  { A : Set } {fa : FiniteSet A } {n<m : n < FiniteSet.finite fa }→ (f : fin-less fa n<m ) → toℕ (FiniteSet.F←Q fa (get-elm f )) < n
get-< (elm1 _ b ) = b

fin-less-cong : { n : ℕ }  { A : Set } (fa : FiniteSet A ) (n<m : n < FiniteSet.finite fa )
   → (x y : fin-less fa n<m ) → get-elm {n} {A} {fa} x ≡ get-elm {n} {A} {fa} y → get-< x ≅  get-< y → x ≡ y
fin-less-cong fa n<m (elm1 elm x) (elm1 elm x) refl HE.refl = refl

fin-< : {A : Set} → { n : ℕ } → (fa : FiniteSet A ) → (n<m : n < FiniteSet.finite fa ) → FiniteSet (fin-less fa n<m ) 
fin-< {A}  {n} fa n<m = iso-fin (Fin2Finite n) iso where
    m = FiniteSet.finite fa
    iso : ISO (Fin n) (fin-less fa n<m )
    lemma8f : {i j n : ℕ } → ( i ≡ j ) → {i<n : i < n } → {j<n : j < n } → i<n ≅ j<n  
    lemma8f {zero} {zero} {suc n} refl {s≤s z≤n} {s≤s z≤n} = HE.refl
    lemma8f {suc i} {suc i} {suc n} refl {s≤s i<n} {s≤s j<n} = HE.cong (λ k → s≤s k ) ( lemma8f {i} {i}  refl  )
    lemma10f : {n i j  : ℕ } → ( i ≡ j ) → {i<n : i < n } → {j<n : j < n }  → fromℕ< i<n ≡ fromℕ< j<n
    lemma10f  refl  = HE.≅-to-≡ (HE.cong (λ k → fromℕ< k ) (lemma8f refl  ))
    lemma3f : {a b c : ℕ } → { a<b : a < b } { b<c : b < c } { a<c : a < c } → NatP.<-trans a<b b<c ≡ a<c
    lemma3f {a} {b} {c} {a<b} {b<c} {a<c} = HE.≅-to-≡ (lemma8f refl) 
    lemma11f : {n : ℕ } {x : Fin n } → (n<m : n < m ) → toℕ (fromℕ< (NatP.<-trans (toℕ<n x) n<m)) ≡ toℕ x
    lemma11f {n} {x} n<m  = begin
         toℕ (fromℕ< (NatP.<-trans (toℕ<n x) n<m))
      ≡⟨ toℕ-fromℕ< _ ⟩
         toℕ x
      ∎  where
          open ≡-Reasoning
    ISO.A←B iso (elm1 elm x) = fromℕ< x
    ISO.B←A iso x = elm1 (FiniteSet.Q←F fa (fromℕ< (NatP.<-trans x<n n<m ))) to<n where
      x<n : toℕ x < n
      x<n = toℕ<n x
      to<n : toℕ (FiniteSet.F←Q fa (FiniteSet.Q←F fa (fromℕ< (NatP.<-trans x<n n<m)))) < n
      to<n = subst (λ k → toℕ k < n ) (sym (FiniteSet.finiso← fa _ )) (subst (λ k → k < n ) (sym ( toℕ-fromℕ< (NatP.<-trans x<n n<m) )) x<n )
    ISO.iso← iso x  = lemma2 where
      lemma2 : fromℕ< (subst (λ k → toℕ k < n) (sym
       (FiniteSet.finiso← fa (fromℕ< (NatP.<-trans (toℕ<n x) n<m)))) (subst (λ k → k < n)
       (sym (toℕ-fromℕ< (NatP.<-trans (toℕ<n x) n<m))) (toℕ<n x))) ≡ x
      lemma2 = begin
        fromℕ< (subst (λ k → toℕ k < n) (sym
          (FiniteSet.finiso← fa (fromℕ< (NatP.<-trans (toℕ<n x) n<m)))) (subst (λ k → k < n)
               (sym (toℕ-fromℕ< (NatP.<-trans (toℕ<n x) n<m))) (toℕ<n x))) 
        ≡⟨⟩
           fromℕ< ( subst (λ k → toℕ ( k ) < n ) (sym (FiniteSet.finiso← fa _ )) lemma6 )
        ≡⟨ lemma10 (cong (λ k → toℕ k) (FiniteSet.finiso← fa _ ) ) ⟩
           fromℕ< lemma6
        ≡⟨ lemma10 (lemma11 n<m ) ⟩
           fromℕ< ( toℕ<n x )
        ≡⟨ fromℕ<-toℕ _ _ ⟩
           x 
        ∎  where
          open ≡-Reasoning
          lemma6 : toℕ (fromℕ< (NatP.<-trans (toℕ<n x) n<m)) < n
          lemma6 = subst ( λ k → k < n ) (sym (toℕ-fromℕ< (NatP.<-trans (toℕ<n x) n<m))) (toℕ<n x )
    ISO.iso→ iso (elm1 elm x) = fin-less-cong fa n<m _ _ lemma (lemma8 (cong (λ k → toℕ (FiniteSet.F←Q fa k) ) lemma ) ) where
      lemma13 : toℕ (fromℕ< x) ≡ toℕ (FiniteSet.F←Q fa elm)
      lemma13 = begin
            toℕ (fromℕ< x)
         ≡⟨ toℕ-fromℕ< _ ⟩
            toℕ (FiniteSet.F←Q fa elm)
         ∎  where open ≡-Reasoning
      lemma : FiniteSet.Q←F fa (fromℕ< (NatP.<-trans (toℕ<n (ISO.A←B iso (elm1 elm x))) n<m)) ≡ elm 
      lemma = begin
           FiniteSet.Q←F fa (fromℕ< (NatP.<-trans (toℕ<n (ISO.A←B iso (elm1 elm x))) n<m))
         ≡⟨⟩
           FiniteSet.Q←F fa (fromℕ< ( NatP.<-trans (toℕ<n ( fromℕ< x ) ) n<m))
         ≡⟨ cong (λ k → FiniteSet.Q←F fa k) (lemma10 lemma13 ) ⟩
            FiniteSet.Q←F fa (fromℕ< ( NatP.<-trans x n<m))
         ≡⟨ cong (λ k → FiniteSet.Q←F fa (fromℕ< k ))  {!!} ⟩
           FiniteSet.Q←F fa (fromℕ< ( toℕ<n (FiniteSet.F←Q fa elm)))
         ≡⟨ cong (λ k → FiniteSet.Q←F fa k ) ( fromℕ<-toℕ _ _ ) ⟩
           FiniteSet.Q←F fa (FiniteSet.F←Q fa elm )
         ≡⟨ FiniteSet.finiso→ fa _ ⟩
            elm 
         ∎  where open ≡-Reasoning

