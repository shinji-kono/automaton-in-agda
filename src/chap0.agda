module chap0 where

open import Data.List
open import Data.Nat hiding (_⊔_)
-- open import Data.Integer hiding (_⊔_ ;  _≟_ ; _+_ )
open import Data.Product

A : List ℕ
A = 1 ∷ 2 ∷ []

data Literal : Set where
    x : Literal
    y : Literal
    z : Literal

B : List Literal
B = x ∷ y ∷ z ∷ []


ListProduct : {A B : Set } → List A → List B → List ( A × B )
ListProduct  = {!!}

ex05 : List ( ℕ × Literal )
ex05 = ListProduct A B   -- (1 , x) ∷ (1 , y) ∷ (1 , z) ∷ (2 , x) ∷ (2 , y) ∷ (2 , z) ∷ [] 

ex06 : List ( ℕ × Literal × ℕ )
ex06 = ListProduct A (ListProduct B A)

ex07 : Set
ex07 =  ℕ × ℕ

data ex08-f : ℕ → ℕ → Set where
    ex08f0 : ex08-f 0 1
    ex08f1 : ex08-f 1 2
    ex08f2 : ex08-f 2 3
    ex08f3 : ex08-f 3 4
    ex08f4 : ex08-f 4 0

data ex09-g : ℕ → ℕ → ℕ → ℕ → Set where
    ex09g0 : ex09-g 0 1 2 3
    ex09g1 : ex09-g 1 2 3 0
    ex09g2 : ex09-g 2 3 0 1
    ex09g3 : ex09-g 3 0 1 2

open import Data.Nat.DivMod
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core
open import Data.Nat.Properties

-- _%_ : ℕ → ℕ → ℕ
-- _%_ a b with <-cmp a b
-- _%_ a b | tri< a₁ ¬b ¬c = a
-- _%_ a b | tri≈ ¬a b₁ ¬c = 0
-- _%_ a b | tri> ¬a ¬b c = _%_ (a - b) b

_≡7_ : ℕ → ℕ → Set
n ≡7 m = (n % 7) ≡ (m % 7 )

refl7 :  { n : ℕ} → n ≡7 n
refl7 = {!!}

sym7  : { n m : ℕ} → n ≡7 m → m ≡7 n
sym7  = {!!}

trans7 : { n m o : ℕ} → n ≡7 m → m ≡7 o → n ≡7 o
trans7 = {!!}

open import Level renaming ( zero to Zero ; suc to Suc )

record Graph  { v v' : Level } : Set (Suc v ⊔ Suc v' ) where
  field
    vertex : Set v
    edge : vertex  → vertex → Set v'

open Graph

-- open import Data.Fin hiding ( _≟_ )
open import Data.Empty
open import Relation.Nullary
open import Data.Unit  hiding ( _≟_ )


-- data Dec (P : Set) : Set where
--    yes :   P → Dec P
--    no  : ¬ P → Dec P
--
--  _≟_ :  (s t : ℕ ) → Dec ( s ≡ t )

-- ¬ A = A → ⊥

_n≟_ :  (s t : ℕ ) → Dec ( s ≡ t )
zero n≟ zero = yes refl
zero n≟ suc t = no (λ ())
suc s n≟ zero = no (λ ())
suc s n≟ suc t with s n≟ t 
... | yes refl = yes refl
... | no n = no (λ k → n (tt1 k) )  where
   tt1 : suc s ≡ suc t → s ≡ t
   tt1 refl = refl

open import Data.Bool  hiding ( _≟_ )

conn : List ( ℕ × ℕ ) → ℕ → ℕ → Bool
conn [] _ _ = false
conn ((n1 , m1 ) ∷ t ) n m  with n ≟ n1 | m ≟ m1
conn ((n1 , m1) ∷ t) n m | yes refl | yes refl  = true
conn ((n1 , m1) ∷ t) n m | _ | _ = conn t n m 

list012a : List ( ℕ × ℕ )
list012a = (1 , 2) ∷ (2 , 3) ∷ (3 , 4) ∷ (4 , 5) ∷ (5 , 1) ∷ [] 

graph012a : Graph {Zero} {Zero} 
graph012a = record { vertex = ℕ ; edge = λ s t → (conn list012a s t) ≡ true }

data edge012b :  ℕ → ℕ →  Set where
    e012b-1 : edge012b 1 2
    e012b-2 : edge012b 1 3
    e012b-3 : edge012b 1 4
    e012b-4 : edge012b 2 3
    e012b-5 : edge012b 2 4
    e012b-6 : edge012b 3 4

edge? : (E : ℕ → ℕ →  Set) → ( a b : ℕ ) → Set
edge? E a b = Dec ( E a b ) 

lemma3 : ( a b : ℕ ) → edge? edge012b a b
lemma3 1 2  = yes e012b-1
lemma3 1 3  = yes e012b-2
lemma3 1 4  = yes e012b-3
lemma3 2 3  = yes e012b-4
lemma3 2 4  = yes e012b-5
lemma3 3 4  = yes e012b-6
lemma3 1 1  = no ( λ () )
lemma3 2 1  = no ( λ () )
lemma3 2 2  = no ( λ () )
lemma3 3 1  = no ( λ () )
lemma3 3 2  = no ( λ () )
lemma3 3 3  = no ( λ () )
lemma3 0 _  = no ( λ () )
lemma3 _ 0  = no ( λ () )
lemma3 _ (suc (suc (suc (suc (suc _)))))  = no ( λ () )
lemma3 (suc (suc (suc (suc _)))) _  = no ( λ () )

graph012b : Graph {Zero} {Zero}
graph012b = record { vertex = ℕ  ; edge = edge012b }

data connected { V : Set } ( E : V -> V -> Set ) ( x y : V ) : Set  where
    direct :   E x y → connected E x y 
    indirect :  ( z : V  ) -> E x z  →  connected {V} E z y → connected E x y

lemma1 : connected ( edge graph012a ) 1 2
lemma1 = direct refl  where

lemma1-2 : connected ( edge graph012a ) 1 3
lemma1-2 = indirect 2 refl (direct refl ) 

lemma2 : connected ( edge graph012b ) 1 2
lemma2 = direct e012b-1 

reachable :  { V : Set } ( E : V -> V -> Set ) ( x y : V ) -> Set
reachable {V} E X Y = Dec ( connected {V} E X Y )

dag :  { V : Set } ( E : V -> V -> Set ) ->  Set
dag {V} E =  ∀ (n : V)  →  ¬ ( connected E n n )

open import Function

lemma4 : ¬ ( dag ( edge graph012a)  )
lemma4 neg = neg 1 $ indirect 2 refl $ indirect 3 refl $ indirect 4 refl $ indirect 5 refl $ direct refl 

dgree : List ( ℕ × ℕ ) → ℕ → ℕ 
dgree [] _ = 0
dgree ((e , e1) ∷ t) e0 with e0 ≟ e | e0 ≟ e1
dgree ((e , e1) ∷ t) e0 | yes _ | _ = 1 + (dgree t e0)
dgree ((e , e1) ∷ t) e0 | _ | yes p = 1 + (dgree t e0)
dgree ((e , e1) ∷ t) e0 | no _ | no _ = dgree t e0

dgree-c : {t : Set} → List ( ℕ × ℕ ) → ℕ → (ℕ → t)  → t 
dgree-c {t} [] e0 next = next 0
dgree-c {t} ((e , e1) ∷ tail ) e0 next with e0 ≟ e | e0 ≟ e1
... | yes _ | _ = dgree-c tail e0 ( λ n → next (n + 1 ))
... | _ | yes _ = dgree-c tail e0 ( λ n → next (n + 1 ))
... | no _ | no _ = dgree-c tail e0 next

lemma6 = dgree list012a 2
lemma7 = dgree-c list012a 2 ( λ n → n )

even2 : (n : ℕ ) → n % 2 ≡ 0 → (n + 2) % 2 ≡ 0 
even2 0 refl = refl
even2 1 () 
even2 (suc (suc n)) eq = trans ([a+n]%n≡a%n n _) eq -- [a+n]%n≡a%n : ∀ a n → (a + suc n) % suc n ≡ a % suc n

sum-of-dgree : ( g : List ( ℕ × ℕ )) → ℕ
sum-of-dgree [] = 0
sum-of-dgree ((e , e1) ∷ t) = 2 + sum-of-dgree t

dgree-even : ( g : List ( ℕ × ℕ )) → sum-of-dgree g % 2 ≡ 0
dgree-even [] = refl
dgree-even ((e , e1) ∷ t) = begin
       sum-of-dgree ((e , e1) ∷ t) % 2 
    ≡⟨⟩
       (2 + sum-of-dgree t ) % 2       
    ≡⟨ cong ( λ k → k % 2 ) ( +-comm 2 (sum-of-dgree t) )  ⟩
       (sum-of-dgree t + 2) % 2 
    ≡⟨ [a+n]%n≡a%n (sum-of-dgree t) _ ⟩
       sum-of-dgree t % 2
    ≡⟨ dgree-even t ⟩
       0
    ∎ where open ≡-Reasoning

