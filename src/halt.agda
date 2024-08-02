{-# OPTIONS --cubical-compatible --safe #-}

module halt where

open import Level renaming ( zero to Zero ; suc to Suc )
open import Data.Nat
open import Data.Maybe
open import Data.List hiding ([_])
open import Data.Nat.Properties
open import Relation.Nullary
open import Data.Empty
open import Data.Unit
open import  Relation.Binary.Core hiding (_⇔_)
open import  Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality

open import logic

--
--     (R → Bool) <-> S 
--
record FBijection {n m : Level} (R : Set n) (S : Set m) : Set (n Level.⊔ m)  where
   field
       ffun←  :  S → R → Bool
       ffun→  :  (R → Bool) → S
       ffiso← : (f : R → Bool ) → (x : R)  → ffun← ( ffun→ f ) x ≡ f x 

--       ffiso→ : (x : S)  → ffun→  ( ffun←  x ) ≡ x -- , if we have functional extensionality  but it is unsafe

open FBijection 

--  S <-> S → Bool 
-- 
--  S   0 1 2 3 .... 
--  0   t f t f .... 
--  1   t f t f .... 
--  2   t f t f .... 
--  3   t t t t .....
--  ..
-- counter exmpple
--      f t f f ...

fdiag : {S : Set }  (b : FBijection  S S) → S → Bool
fdiag b n = not (ffun← b n n)

--
--  ffun→ b (fiag b) is some S
--  ffun← b (ffun→ b (fdiag b) ) is a function S → Bool
--     is pointwise equal to fdiag b , which means not (ffun← b (ffun→ b (fdiag b) ) x ≡ (fdiag b) x )
--     but is also means not (fdiag b) x ≡ (fdiag b) x , contradiction

--   ¬  (S → Bool) <-> S 
--
fdiagonal : { S : Set } → ¬ FBijection  S S
fdiagonal {S} b =  ¬t=f _ (trans ff4 (sym (ff3 _) ) ) where
    ff1 : S
    ff1 = ffun→ b (fdiag b)
    ff2 : S → Bool
    ff2 = ffun← b (ffun→ b (fdiag b) ) 
    ff3 : (x : S) → ffun← b (ffun→ b (fdiag b) ) x ≡ fdiag b x
    ff3 x = ffiso← b (fdiag b) x
    ff4 : not ( ffun← b (ffun→ b (fdiag b) ) (ffun→ b (fdiag b))) ≡ fdiag b (ffun→ b (fdiag b))
    ff4  = refl   -- definition of fdiag b

record TM : Set where
   field
      tm : List Bool → Maybe Bool

open TM

record UTM : Set where
   field
      utm : TM
      encode : TM → List Bool
      is-tm : (t : TM) → (x : List Bool) → tm utm (encode t ++ x ) ≡ tm t x

open UTM 

open _∧_

record Halt : Set where
   field
      halt :  (t : TM ) → (x : List Bool ) → Bool
      is-halt :     (t : TM ) → (x : List Bool ) → (halt t x ≡ true )  ⇔ ( (just true ≡ tm t x ) ∨ (just false ≡ tm t x ) )
      is-not-halt : (t : TM ) → (x : List Bool ) → (halt t x ≡ false ) ⇔ ( nothing ≡ tm t x )

open Halt

--
--   List boot <-> ( List Bool → Bool )
--
TNLF : (halt : Halt ) → (utm : UTM) → FBijection (List Bool) (List Bool)
TNLF halt utm = record {
       ffun←  = λ tm x → Halt.halt halt (UTM.utm utm) (tm ++ x)
     ; ffun→  = λ h  → encode utm record { tm = h1 h } 
     ; ffiso← = λ h y → TN1 h y 
  } where
     open ≡-Reasoning
     h1 : (h : List Bool → Bool) → (x : List Bool ) → Maybe Bool
     h1 h x with h x
     ... | true =  just true
     ... | false = nothing
     tenc : (h : List Bool → Bool) → (y : List Bool) → List Bool
     tenc h y = encode utm (record { tm = λ x → h1 h x }) ++ y
     h-nothing : (h : List Bool → Bool) → (y : List Bool) → h y ≡ false → h1 h y ≡ nothing
     h-nothing h y eq with h y
     h-nothing h y eq | false = refl
     h-just : (h : List Bool → Bool) → (y : List Bool) → h y ≡ true → h1 h y ≡ just true
     h-just h y eq with h y
     h-just h y eq | true = refl
     TN1 :  (h : List Bool → Bool) → (y : List Bool ) → Halt.halt halt (UTM.utm utm) (tenc h y) ≡ h y
     TN1 h y with h y in eq1
     ... | true  = begin
        Halt.halt halt (UTM.utm utm)  (tenc h y) ≡⟨ proj2 (is-halt halt (UTM.utm utm) (tenc h y) ) (case1 (sym tm-tenc)) ⟩
        true ∎  where
          tm-tenc :  tm (UTM.utm utm) (tenc h y) ≡ just true
          tm-tenc = begin
              tm (UTM.utm utm) (tenc h y)  ≡⟨  is-tm utm _ y ⟩
              h1 h y ≡⟨ h-just h y eq1  ⟩
              just true  ∎  
     ... | false = begin
        Halt.halt halt (UTM.utm utm)  (tenc h y) ≡⟨ proj2 (is-not-halt halt (UTM.utm utm) (tenc h y) ) (sym tm-tenc) ⟩
        false ∎  where
          tm-tenc :  tm (UTM.utm utm) (tenc h y) ≡ nothing
          tm-tenc = begin
              tm (UTM.utm utm) (tenc h y)  ≡⟨  is-tm utm _ y ⟩
              h1 h y ≡⟨  h-nothing h y eq1 ⟩
              nothing  ∎  
     -- the rest of bijection means encoding is unique, but we don't need it
     -- fiso→ :  (y : List Bool ) → encode utm record { tm = λ x →  h1 (λ tm → Halt.halt halt (UTM.utm utm) tm  ) x } ≡ y
          
TNLF1 : UTM → ¬ Halt 
TNLF1 utm halt = fdiagonal ( TNLF halt utm )

