module lang-text where

open import Data.List
open import Data.String
open import Data.Char
-- open import Data.Char.Unsafe
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import logic

split : {Σ : Set} → (List Σ → Bool)
      → ( List Σ → Bool) → List Σ → Bool
split x y  [] = x [] /\ y []
split x y (h  ∷ t) = (x [] /\ y (h  ∷ t)) \/
  split (λ t1 → x (  h ∷ t1 ))  (λ t2 → y t2 ) t

contains : String → String → Bool
contains x y = contains1 (toList x ) ( toList y ) where
   contains1 : List Char → List Char → Bool
   contains1 []  [] = false
   contains1 [] ( cx ∷ ly ) = false
   contains1  (cx ∷ lx)  [] = true
   contains1 (cx ∷ lx ) ( cy ∷ ly ) with cx ≟ cy
   ... | yes refl = contains1 lx ly
   ... | no n = false

-- w does not contain the substring ab
ex15a : Set
ex15a = (w : String ) → ¬ (contains w "ab"  ≡ true )

-- w does not contains substring baba
ex15b : Set
ex15b = (w : String ) → ¬ (contains w "baba"  ≡ true )

-- w contains neither the substing ab nor ba
ex15c : Set

-- w is any string not in a*b*
ex15c = (w : String ) → ( ¬ (contains w "ab"  ≡ true ))  /\ ( ¬ (contains w "ba"  ≡ true ) ) 

ex15d : ?
ex15d = ?

ex15e : ?
ex15e = ?

ex15f : ?
ex15f = ?

ex15g : ?
ex15g = ?

ex15h : ?
ex15h = ?
