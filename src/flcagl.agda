open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
module flcagl
   (A : Set)
   ( _≟_ :  (a b : A) → Dec ( a ≡ b ) ) where

open import Data.Bool hiding ( _≟_ ) 
-- open import Data.Maybe
open import Level renaming ( zero to Zero ; suc to succ )
open import Size 

module List where

        data List (i : Size) (A : Set) : Set where
          [] : List i A
          _∷_ : {j : Size< i} (x : A) (xs : List j A) → List i A


        map : ∀{i A B} → (A → B) → List i A → List i B
        map f [] = []
        map f ( x ∷ xs)= f x ∷ map f xs

        foldr : ∀{i} {A B : Set} → (A → B → B) → B → List i A → B
        foldr c n [] = n
        foldr c n (x ∷ xs) = c x (foldr c n xs)

        any : ∀{i A} → (A → Bool) → List i A → Bool
        any p xs = foldr _∨_ false (map p xs)

module Lang where

        open List 

        record  Lang (i : Size)  : Set  where
           coinductive
           field
              ν : Bool
              δ : ∀{j : Size< i} → A → Lang j

        open Lang

        _∋_ : ∀{i} → Lang i → List i A → Bool
        l ∋ [] = ν l
        l ∋ ( a ∷ as ) = δ l a ∋ as

        trie : ∀{i}  (f : List i A → Bool) → Lang i
        ν (trie f) = f []
        δ (trie f) a = trie (λ as → f (a ∷ as))

        ∅ : ∀{i} → Lang i 
        ν ∅ = false
        δ ∅ x = ∅

        ε : ∀{i} → Lang i 
        ν ε = true
        δ ε x = ∅

        open import Relation.Nullary.Decidable

        char : ∀{i}  (a : A) → Lang i
        ν (char a) = false
        δ (char a) x = if ⌊ a ≟ x ⌋ then ε else ∅

        compl : ∀{i}  (l : Lang i) → Lang i
        ν (compl l) = not (ν l)
        δ (compl l) x = compl (δ l x)


        _∪_ : ∀{i} (k l : Lang i) → Lang i
        ν (k ∪ l) = ν k ∨ ν l
        δ (k ∪ l) x = δ k x ∪ δ l x


        _·_ : ∀{i}  (k l : Lang i) → Lang i
        ν (k · l) = ν k ∧ ν l
        δ (k · l) x = let k′l =  δ k x  · l in if ν k then k′l ∪ δ l x else k′l

        _*_ : ∀{i} (k l : Lang i )  → Lang i
        ν (k * l) = ν k ∧ ν l
        δ (_*_ {i} k  l) {j} x =
            let
                k′l : Lang j
                k′l  = _*_ {j} (δ k {j} x) l
            in  if ν k then _∪_ {j}  k′l (δ l {j} x) else k′l 

        _* : ∀{i} (l : Lang i) → Lang i
        ν (l *) = true
        δ (l *) x = δ l x · (l *)

        record _≅⟨_⟩≅_ (l : Lang ∞ ) i (k : Lang ∞) : Set  where
           coinductive
           field ≅ν : ν l ≡ ν k
                 ≅δ : ∀ {j : Size< i } (a : A ) → δ l a ≅⟨ j ⟩≅ δ k a

        open _≅⟨_⟩≅_

        ≅refl : ∀{i} {l : Lang ∞} → l ≅⟨ i ⟩≅ l
        ≅ν ≅refl = refl
        ≅δ ≅refl a = ≅refl


        ≅sym : ∀{i} {k l : Lang ∞} (p : l ≅⟨ i ⟩≅ k) → k ≅⟨ i ⟩≅ l
        ≅ν (≅sym p) = sym (≅ν p)
        ≅δ (≅sym p) a = ≅sym (≅δ p a)

        ≅trans : ∀{i} {k l m : Lang ∞}
           ( p : k ≅⟨ i ⟩≅ l ) ( q : l ≅⟨ i ⟩≅ m ) → k ≅⟨ i ⟩≅ m
        ≅ν (≅trans p q) = trans (≅ν p) (≅ν q)
        ≅δ (≅trans p q) a = ≅trans (≅δ p a) (≅δ q a)

        open import Relation.Binary

        ≅isEquivalence : ∀(i : Size) → IsEquivalence _≅⟨ i ⟩≅_
        ≅isEquivalence i = record { refl = ≅refl; sym = ≅sym; trans = ≅trans }

        Bis : ∀(i : Size) → Setoid _ _
        Setoid.Carrier (Bis i) = Lang ∞
        Setoid._≈_ (Bis i) = _≅⟨ i ⟩≅_
        Setoid.isEquivalence (Bis i) = ≅isEquivalence i

        import Relation.Binary.EqReasoning as EqR

        ≅trans′ : ∀ i (k l m : Lang ∞)
           ( p : k ≅⟨ i ⟩≅ l ) ( q : l ≅⟨ i ⟩≅ m ) → k ≅⟨ i ⟩≅ m
        ≅trans′ i k l m p q = begin
                k ≈⟨ p ⟩
                l ≈⟨ q ⟩
                m ∎ where open EqR (Bis i)

        open import Data.Bool.Properties

        union-assoc : ∀{i} (k {l m} : Lang ∞) → ((k ∪ l) ∪ m ) ≅⟨ i ⟩≅ ( k ∪ (l ∪ m) )
        ≅ν (union-assoc k) = ∨-assoc (ν k) _ _
        ≅δ (union-assoc k) a = union-assoc (δ k a)
        union-comm : ∀{i} (l k : Lang ∞) → (l ∪ k ) ≅⟨ i ⟩≅ ( k ∪ l )
        ≅ν (union-comm l k) = ∨-comm (ν l) _
        ≅δ (union-comm l k) a = union-comm (δ l a) (δ k a)
        union-idem : ∀{i} (l : Lang ∞) → (l ∪ l ) ≅⟨ i ⟩≅ l
        ≅ν (union-idem l) = ∨-idem _
        ≅δ (union-idem l) a = union-idem (δ l a)
        union-emptyl : ∀{i}{l : Lang ∞} → (∅ ∪ l ) ≅⟨ i ⟩≅ l
        ≅ν union-emptyl = refl
        ≅δ union-emptyl a = union-emptyl

        union-cong : ∀{i}{k k′ l l′ : Lang ∞}
             (p : k ≅⟨ i ⟩≅ k′) (q : l ≅⟨ i ⟩≅ l′ ) → ( k ∪ l ) ≅⟨ i ⟩≅ ( k′ ∪ l′ )
        ≅ν (union-cong p q) = cong₂ _∨_ (≅ν p) (≅ν q)
        ≅δ (union-cong p q) a = union-cong (≅δ p a) (≅δ q a)

        withExample : (P : Bool → Set) (p : P true) (q : P false) →
           {A : Set} (g : A → Bool) (x : A) → P (g x)
        withExample P p q g x with g x
        ... | true = p
        ... | false = q

        rewriteExample : {A : Set} {P : A → Set} {x : A} (p : P x)
            {g : A → A} (e : g x ≡ x) → P (g x)
        rewriteExample p e rewrite e = p

        infixr 6 _∪_
        infixr 7 _·_
        infix 5 _≅⟨_⟩≅_

        union-congl : ∀{i}{k k′ l : Lang ∞}
             (p : k ≅⟨ i ⟩≅ k′) → ( k ∪ l ) ≅⟨ i ⟩≅ ( k′ ∪ l )
        union-congl eq = union-cong eq ≅refl

        union-congr : ∀{i}{k l l′ : Lang ∞}
             (p : l ≅⟨ i ⟩≅ l′) → ( k ∪ l ) ≅⟨ i ⟩≅ ( k ∪ l′ )
        union-congr eq = union-cong ≅refl eq

        union-swap24 :   ∀{i} ({x y z w} : Lang ∞)  →  (x ∪ y) ∪ z ∪  w
                                              ≅⟨ i ⟩≅ (x ∪ z) ∪ y ∪ w
        union-swap24 {_} {x} {y} {z} {w} = begin
              (x ∪ y) ∪ z ∪ w
           ≈⟨ union-assoc x ⟩
               x ∪ y ∪ z ∪ w
           ≈⟨ union-congr (≅sym ( union-assoc y)) ⟩
              x ∪ ((y ∪ z) ∪ w)
           ≈⟨ ≅sym ( union-assoc x ) ⟩
              (x ∪ ( y ∪ z)) ∪ w
           ≈⟨ union-congl (union-congr (union-comm y z )) ⟩
              ( x ∪ (z ∪ y)) ∪ w
           ≈⟨  union-congl (≅sym ( union-assoc x )) ⟩
              ((x ∪ z) ∪ y) ∪ w
           ≈⟨ union-assoc (x ∪ z) ⟩
              (x ∪ z) ∪ y ∪ w
           ∎
               where open EqR (Bis _)

        concat-union-distribr : ∀{i} (k {l m} : Lang ∞) → k · ( l ∪ m ) ≅⟨ i ⟩≅ ( k · l ) ∪ ( k · m )
        ≅ν (concat-union-distribr k) =  ∧-distribˡ-∨ (ν k) _ _ 
        ≅δ (concat-union-distribr k) a with ν k
        ≅δ (concat-union-distribr k {l} {m}) a | true = begin
              δ k a · (l ∪ m) ∪ (δ l a ∪ δ m a)
           ≈⟨ union-congl (concat-union-distribr _) ⟩
              (δ k a · l ∪ δ k a · m) ∪ (δ l a ∪ δ m a)
           ≈⟨ union-swap24 ⟩
              (δ k a · l ∪ δ l a) ∪ (δ k a · m ∪ δ m a)
           ∎
               where open EqR (Bis _)
        ≅δ (concat-union-distribr k) a | false = concat-union-distribr (δ k a)

        concat-union-distribl : ∀{i} (k {l m} : Lang ∞) → ( k ∪ l ) · m ≅⟨ i ⟩≅ ( k · m ) ∪ ( l · m )
        ≅ν (concat-union-distribl k {l} {m}) = ∧-distribʳ-∨ _ (ν k) _ 
        ≅δ (concat-union-distribl k {l} {m}) a with ν k |  ν l 
        ≅δ (concat-union-distribl k {l} {m}) a | false | false = concat-union-distribl (δ k a)
        ≅δ (concat-union-distribl k {l} {m}) a | false | true = begin
              (if false ∨ true then (δ k a ∪ δ l a) · m ∪ δ m a else (δ k a ∪ δ l a) · m)
           ≈⟨ ≅refl ⟩
              ((δ k a ∪ δ l a) · m ) ∪ δ m a
           ≈⟨ union-congl (concat-union-distribl _) ⟩
               (δ k a · m ∪ δ l a · m) ∪ δ m a
           ≈⟨ union-assoc _ ⟩
              (δ k a · m) ∪ ( δ l a · m ∪ δ m a )
           ≈⟨ ≅refl ⟩
              (if false then δ k a · m ∪ δ m a else δ k a · m) ∪ (if true then δ l a · m ∪ δ m a else δ l a · m)
           ∎
               where open EqR (Bis _)
        ≅δ (concat-union-distribl k {l} {m}) a | true | false = begin
               (if true ∨ false then (δ k a ∪ δ l a) · m ∪ δ m a else (δ k a ∪ δ l a) · m) ≈⟨ ≅refl ⟩
               ((δ k a ∪ δ l a) · m ) ∪ δ m a ≈⟨ union-congl (concat-union-distribl _) ⟩
               (δ k a · m ∪ δ l a · m) ∪ δ m a ≈⟨  union-assoc _ ⟩
                δ k a · m ∪ ( δ l a · m ∪ δ m a ) ≈⟨  union-congr ( union-comm   _ _) ⟩
                δ k a · m ∪ δ m a ∪ δ l a · m ≈⟨ ≅sym ( union-assoc  _  ) ⟩
               (δ k a · m ∪ δ m a) ∪ δ l a · m ≈⟨ ≅refl ⟩
               ((if true then δ k a · m ∪ δ m a else δ k a · m) ∪ (if false then δ l a · m ∪ δ m a else δ l a · m))
           ∎
               where open EqR (Bis _)
        ≅δ (concat-union-distribl k {l} {m}) a | true | true = begin
               (if true ∨ true then (δ k a ∪ δ l a) · m ∪ δ m a else (δ k a ∪ δ l a) · m) ≈⟨ ≅refl ⟩
               (δ k a ∪ δ l a) · m ∪ δ m a ≈⟨ union-congl ( concat-union-distribl _ ) ⟩
               (δ k a · m ∪ δ l a · m) ∪ δ m a ≈⟨  union-assoc _ ⟩
                δ k a · m ∪ ( δ l a · m ∪ δ m a ) ≈⟨ ≅sym ( union-congr ( union-congr (  union-idem _ ) ) ) ⟩
                δ k a · m ∪ ( δ l a · m ∪ (δ m a  ∪ δ m a) ) ≈⟨  ≅sym ( union-congr ( union-assoc _ )) ⟩
                δ k a · m ∪ ( (δ l a · m ∪ δ m a  ) ∪ δ m a ) ≈⟨   union-congr (  union-congl  ( union-comm _  _) )   ⟩
                δ k a · m ∪ ( (δ m a  ∪ δ l a · m ) ∪ δ m a ) ≈⟨  ≅sym ( union-assoc  _  ) ⟩
               ( δ k a · m ∪  (δ m a  ∪ δ l a · m )) ∪ δ m a ≈⟨  ≅sym ( union-congl ( union-assoc _  ) ) ⟩
               ((δ k a · m ∪ δ m a) ∪ δ l a · m) ∪ δ m a ≈⟨  union-assoc _  ⟩
               (δ k a · m ∪ δ m a) ∪ δ l a · m ∪ δ m a ≈⟨ ≅refl ⟩
               ((if true then δ k a · m ∪ δ m a else δ k a · m) ∪ (if true then δ l a · m ∪ δ m a else δ l a · m))
           ∎
               where open EqR (Bis _)

        postulate
                concat-emptyl : ∀{i} l → ∅ · l ≅⟨ i ⟩≅ ∅
                concat-emptyr : ∀{i} l → l · ∅ ≅⟨ i ⟩≅ ∅
                concat-unitl : ∀{i} l → ε · l ≅⟨ i ⟩≅ l
                concat-unitr : ∀{i} l → l · ε ≅⟨ i ⟩≅ l
                star-empty : ∀{i} → ∅ * ≅⟨ i ⟩≅ ε

        concat-congl : ∀{i} {m l k : Lang ∞} → l ≅⟨ i ⟩≅ k → l · m ≅⟨ i ⟩≅ k · m
        ≅ν (concat-congl {i} {m} p ) =  cong (λ x →  x ∧  ( ν m ))  ( ≅ν p )
        ≅δ (concat-congl {i} {m} {l} {k} p ) a with ν k | ν l | ≅ν p
        ≅δ (concat-congl {i} {m} {l} {k} p) a | false | false | refl = concat-congl (≅δ p a)
        ≅δ (concat-congl {i} {m} {l} {k} p) a | true | true | refl = union-congl (concat-congl (≅δ p a)) 

        concat-congr : ∀{i} {m l k : Lang ∞} → l ≅⟨ i ⟩≅ k → m · l ≅⟨ i ⟩≅ m · k
        ≅ν (concat-congr {i} {m} {_} {k} p ) =  cong (λ x →  ( ν m ) ∧ x )  ( ≅ν p )
        ≅δ (concat-congr {i} {m} {l} {k} p ) a with ν m | ν k | ν l | ≅ν p
        ≅δ (concat-congr {i} {m} {l} {k} p) a | false | x | .x | refl = concat-congr p
        ≅δ (concat-congr {i} {m} {l} {k} p) a | true | x | .x | refl = union-cong (concat-congr p ) ( ≅δ p a )

        concat-assoc : ∀{i} (k {l m} : Lang ∞) → (k · l) · m ≅⟨ i ⟩≅ k · (l · m)
        ≅ν (concat-assoc {i} k {l} {m} ) =  ∧-assoc ( ν k ) ( ν l ) ( ν m )
        ≅δ (concat-assoc {i} k {l} {m} ) a with  ν k 
        ≅δ (concat-assoc {i} k {l} {m}) a | false  = concat-assoc _
        ≅δ (concat-assoc {i} k {l} {m}) a | true  with ν l
        ≅δ (concat-assoc {i} k {l} {m}) a | true | false =  begin
             ( if false then (δ k a · l ∪ δ l a) · m ∪ δ m a else (δ k a · l ∪ δ l a) · m )
          ≈⟨ ≅refl  ⟩
            (δ k a · l ∪ δ l a) · m
          ≈⟨ concat-union-distribl _ ⟩
            ((δ k a · l) · m ) ∪ ( δ l a · m )
          ≈⟨ union-congl (concat-assoc _) ⟩
             (δ k a · l · m ) ∪ ( δ l a · m )
          ≈⟨ ≅refl  ⟩
             δ k a · l · m ∪ (if false then δ l a · m ∪ δ m a else δ l a · m)
           ∎ where open EqR (Bis _)
        ≅δ (concat-assoc {i} k {l} {m}) a | true | true = begin
             (if true then (δ k a · l ∪ δ l a) · m ∪ δ m a else (δ k a · l ∪ δ l a) · m)
          ≈⟨ ≅refl  ⟩
             ((( δ k a · l ) ∪ δ l a) · m ) ∪ δ m a
          ≈⟨ union-congl (concat-union-distribl _   ) ⟩
             ((δ k a · l) · m   ∪ ( δ l a · m )) ∪ δ m a
          ≈⟨  union-congl (  union-congl (concat-assoc _))   ⟩
             (( δ k a · l · m ) ∪ ( δ l a · m )) ∪ δ m a 
          ≈⟨ union-assoc _ ⟩
             ( δ k a · l · m ) ∪ ( ( δ l a · m ) ∪ δ m a )
          ≈⟨ ≅refl  ⟩
             δ k a · l · m ∪ (if true then δ l a · m ∪ δ m a else δ l a · m)
           ∎ where open EqR (Bis _)

        star-concat-idem : ∀{i} (l : Lang ∞) → l * · l * ≅⟨ i ⟩≅ l *
        ≅ν (star-concat-idem l) = refl
        ≅δ (star-concat-idem l) a = begin
               δ ((l *) · (l *)) a ≈⟨ union-congl (concat-assoc _) ⟩
               δ l a · (l * · l *) ∪ δ l a · l * ≈⟨ union-congl (concat-congr (star-concat-idem _)) ⟩
               δ l a · l * ∪ δ l a · l * ≈⟨ union-idem _ ⟩
               δ (l *) a ∎ where open EqR (Bis _)

        star-idem : ∀{i} (l : Lang ∞) → (l *) * ≅⟨ i ⟩≅ l *
        ≅ν (star-idem l) = refl
        ≅δ (star-idem l) a = begin
                  δ ((l *) *) a  ≈⟨ concat-assoc (δ l a)  ⟩
                  δ l a · ((l *) · ((l *) *)) ≈⟨ concat-congr ( concat-congr (star-idem l )) ⟩
                  δ l a · ((l *) · (l *)) ≈⟨  concat-congr (star-concat-idem l ) ⟩
                  δ l a · l *
                ∎ where open EqR (Bis _)

        postulate
           star-rec : ∀{i} (l : Lang ∞) → l * ≅⟨ i ⟩≅ ε ∪ (l · l *)

        star-from-rec : ∀{i} (k {l m} : Lang ∞)
                → ν k ≡ false
                → l ≅⟨ i ⟩≅ k · l ∪ m
                → l ≅⟨ i ⟩≅ k * · m
        ≅ν (star-from-rec k n p) with ≅ν p
        ... | b rewrite n = b
        ≅δ (star-from-rec k {l} {m} n p) a with ≅δ p a
        ... | q rewrite n = begin
                   (δ l a)
                ≈⟨ q ⟩
                   δ k a · l ∪ δ m a
                ≈⟨ union-congl (concat-congr (star-from-rec k {l} {m} n p))  ⟩
                   (δ k a · (k * · m) ∪ δ m a)
                ≈⟨ union-congl (≅sym (concat-assoc _)) ⟩
                    (δ k a · (k *)) · m ∪ δ m a
                ∎ where open EqR (Bis _)


open List

record DA (S : Set) : Set where
    field ν : (s : S) → Bool
          δ : (s : S)(a : A) → S
    νs : ∀{i} (ss : List.List i S) → Bool
    νs ss = List.any ν ss
    δs : ∀{i} (ss : List.List i S) (a : A) → List.List i S
    δs ss a = List.map (λ s → δ s a) ss

open Lang 

lang : ∀{i} {S} (da : DA S) (s : S) → Lang i
Lang.ν (lang da s) = DA.ν da s
Lang.δ (lang da s) a = lang da (DA.δ da s a)

open import Data.Unit hiding ( _≟_ )

open DA

∅A : DA ⊤
ν ∅A s = false
δ ∅A s a = s

εA : DA Bool
ν εA b  = b
δ εA b a = false

open import Relation.Nullary.Decidable

data 3States : Set where
   init acc err : 3States

charA : (a : A) → DA 3States
ν (charA a) init = false
ν (charA a) acc = true
ν (charA a) err = false
δ (charA a) init x =
  if ⌊ a ≟  x ⌋ then acc else err
δ (charA a) acc x = err
δ (charA a) err x = err


complA : ∀{S} (da : DA S) → DA S
ν (complA da) s = not (ν da s)
δ (complA da) s a = δ da s a

open import Data.Product

_⊕_ : ∀{S1 S2} (da1 : DA S1) (da2 : DA S2) → DA (S1 × S2)
ν (da1 ⊕ da2) (s1 , s2) = ν da1 s1 ∨ ν da2 s2
δ (da1 ⊕ da2) (s1 , s2) a = δ da1 s1 a , δ da2 s2 a

powA : ∀{S} (da : DA S) → DA (List ∞ S)
ν (powA da) ss = νs da ss
δ (powA da) ss a = δs da ss a

open _≅⟨_⟩≅_ 

powA-nil : ∀{i S} (da : DA S) → lang (powA da) [] ≅⟨ i ⟩≅ ∅
≅ν (powA-nil da) = refl
≅δ (powA-nil da) a = powA-nil da

powA-cons : ∀{i S} (da : DA S) {s : S} {ss : List ∞ S} →
        lang (powA da) (s ∷ ss) ≅⟨ i ⟩≅ lang da s ∪ lang (powA da) ss
≅ν (powA-cons da) = refl
≅δ (powA-cons da) a = powA-cons da

composeA : ∀{S1 S2} (da1 : DA S1)(s2 : S2)(da2 : DA S2) → DA (S1 × List ∞ S2)
ν (composeA da1 s2 da2) (s1 , ss2) = (ν da1 s1 ∧ ν da2 s2) ∨ νs da2 ss2
δ (composeA da1 s2 da2) (s1 , ss2) a =
        δ da1 s1 a , δs da2 (if ν da1 s1 then s2 ∷ ss2 else ss2) a

import Relation.Binary.EqReasoning as EqR

composeA-gen : ∀{i S1 S2} (da1 : DA S1) (da2 : DA S2) → ∀(s1 : S1)(s2 : S2)(ss : List ∞ S2) →
        lang (composeA da1 s2 da2) (s1 , ss) ≅⟨ i ⟩≅ lang da1 s1 · lang da2 s2 ∪ lang (powA da2) ss
≅ν (composeA-gen da1 da2 s1 s2 ss) = refl
≅δ (composeA-gen da1 da2 s1 s2 ss) a with ν da1 s1
... | false = composeA-gen da1 da2 (δ da1 s1 a) s2 (δs da2 ss a)
... | true = begin
       lang (composeA da1 s2 da2) (δ da1 s1 a , δ da2 s2 a ∷ δs da2 ss a)
   ≈⟨ composeA-gen da1 da2 (δ da1 s1 a) s2 (δs da2 (s2 ∷ ss) a) ⟩
       lang da1 (δ da1 s1 a) · lang da2 s2 ∪ lang (powA da2) (δs da2 (s2 ∷ ss) a)
   ≈⟨ union-congr (powA-cons da2)  ⟩ 
       lang da1 (δ da1 s1 a) · lang da2 s2 ∪
          (lang da2 (δ da2 s2 a) ∪ lang (powA da2) (δs da2 ss a))
   ≈⟨ ≅sym  (union-assoc _)  ⟩
       (lang da1 (δ da1 s1 a) · lang da2 s2 ∪ lang da2 (δ da2 s2 a)) ∪ lang (powA da2) (δs da2 ss a)
   ∎ where open EqR (Bis _)

postulate
  composeA-correct : ∀{i S1 S2} (da1 : DA S1) (da2 : DA S2) s1 s2 →
     lang (composeA da1 s2 da2) (s1 , []) ≅⟨ i ⟩≅ lang da1 s1 · lang da2 s2


open import Data.Maybe

acceptingInitial : ∀{S} (s0 : S) (da : DA S) → DA (Maybe S)
ν (acceptingInitial s0 da) (just s) = ν da s
δ (acceptingInitial s0 da) (just s) a = just (δ da s a)
ν (acceptingInitial s0 da) nothing = true
δ (acceptingInitial s0 da) nothing a = just (δ da s0 a)



finalToInitial : ∀{S} (da : DA (Maybe S)) → DA (List ∞ (Maybe S))
ν (finalToInitial da) ss = νs da ss
δ (finalToInitial da) ss a =
        let ss′ = δs da ss a
        in if νs da ss then δ da nothing a ∷ ss′ else ss′


starA : ∀{S}(s0 : S)(da : DA S) → DA (List ∞(Maybe S))
starA s0 da = finalToInitial (acceptingInitial s0 da)


postulate
 acceptingInitial-just : ∀{i S} (s0 : S) (da : DA S) {s : S} →
   lang (acceptingInitial s0 da) (just s) ≅⟨ i ⟩≅ lang da s
 acceptingInitial-nothing : ∀{i S} (s0 : S) (da : DA S) →
        lang (acceptingInitial s0 da) nothing ≅⟨ i ⟩≅ ε ∪ lang da s0
 starA-lemma : ∀{i S}(da : DA S)(s0 : S)(ss : List ∞ (Maybe S))→
        lang (starA s0 da) ss ≅⟨ i ⟩≅ 
                lang (powA (acceptingInitial s0 da)) ss · (lang da s0) *
 starA-correct : ∀{i S} (da : DA S) (s0 : S) →
   lang (starA s0 da) (nothing ∷ []) ≅⟨ i ⟩≅ (lang da s0) *

record NAutomaton ( Q : Set ) ( Σ : Set  )
           : Set  where
        field
              Nδ : Q → Σ → Q → Bool
              Nstart : Q → Bool
              Nend  :  Q → Bool

postulate
   exists : { S : Set} → ( S → Bool ) → Bool

nlang : ∀{i} {S} (nfa : NAutomaton S A ) (s : S → Bool ) → Lang i
Lang.ν (nlang nfa s) = exists ( λ x → (s x ∧ NAutomaton.Nend nfa x ))
Lang.δ (nlang nfa s) a = nlang nfa (λ x → s x ∧ (NAutomaton.Nδ nfa x a) x) 

nlang1 : ∀{i} {S} (nfa : NAutomaton S A ) (s : S → Bool ) → Lang i
Lang.ν (nlang1 nfa s) = NAutomaton.Nend nfa  {!!}
Lang.δ (nlang1 nfa s) a = nlang1 nfa (λ x → s x ∧ (NAutomaton.Nδ nfa x a) x) 

-- nlang' : ∀{i} {S} (nfa : DA (S → Bool) ) (s : S → Bool ) → Lang i
-- Lang.ν (nlang' nfa s) = DA.ν nfa  s
-- Lang.δ (nlang' nfa s) a = nlang' nfa (DA.δ nfa s a)

