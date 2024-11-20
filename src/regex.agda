{-# OPTIONS --cubical-compatible --safe #-}

-- {-# OPTIONS --allow-unsolved-metas #-}
module regex where

open import Level renaming ( suc to succ ; zero to Zero )
open import Data.Fin hiding ( pred )
open import Data.Nat hiding ( _≟_ )
open import Data.List hiding ( any ;  [_] )
-- import Data.Bool using ( Bool ; true ; false ; _∧_ )
-- open import Data.Bool using ( Bool ; true ; false ; _∧_ ; _∨_ )
open import  Relation.Binary.PropositionalEquality as RBF hiding ( [_] ) 
open import Relation.Nullary using (¬_; Dec; yes; no)
open import logic
open import regular-language

--  (abc|d.*)
--  any = < a > || < b > || < c > || < d >
--  ( < a > & < b > & < c > ) || ( <d > & ( any * ) )

data Regex ( Σ : Set) : Set  where
  ε     : Regex Σ                -- empty
  φ     : Regex Σ               -- fail
  _*    : Regex Σ → Regex Σ 
  _&_   : Regex Σ → Regex Σ → Regex Σ
  _||_  : Regex Σ → Regex Σ → Regex Σ
  <_>   : Σ → Regex Σ

infixr 40 _&_ _||_

-- Meaning of regular expression

regex-language : {Σ : Set} → Regex Σ → ((x y : Σ ) → Dec0 (x ≡ y))  →  List Σ → Bool
regex-language φ cmp _ = false
regex-language ε cmp [] = true
regex-language ε cmp (_ ∷ _) = false
regex-language (x *) cmp y = repeat ( regex-language x cmp  ) []  y
regex-language (x & y) cmp w  = split ( λ z → regex-language x  cmp z ) (regex-language y  cmp  )  w
regex-language (x || y) cmp w = ( regex-language x  cmp w )  \/  ( regex-language y  cmp w)
regex-language < h > cmp  [] = false
regex-language < h > cmp  (h1  ∷ [] ) with cmp h h1
... | yes0 _ = true
... | no0 _  = false
regex-language < h >  _ (_ ∷ _ ∷ _)  = false

