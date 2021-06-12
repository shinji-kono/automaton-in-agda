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

record HBijection {n m : Level} (R : Set n) (S : Set m) : Set (n Level.⊔ m)  where
   field
       fun←  :  S → R
       fun→  :  R → S
       fiso← : (x : R)  → fun← ( fun→ x )  ≡ x 
--  normal bijection required below, but we don't need this to show the inconsistency
--     fiso→ : (x : S ) → fun→ ( fun← x )  ≡ x 

injection :  {n m : Level} (R : Set n) (S : Set m) (f : R → S ) → Set (n Level.⊔ m)
injection R S f = (x y : R) → f x ≡ f y → x ≡ y

open HBijection 

diag : {S : Set }  (b : HBijection  ( S → Bool ) S) → S → Bool
diag b n = not (fun← b n n)

diagonal : { S : Set } → ¬ HBijection  ( S → Bool ) S
diagonal {S} b = diagn1 (fun→ b (diag b) ) refl where
    diagn1 : (n : S ) → ¬ (fun→ b (diag b) ≡ n ) 
    diagn1 n dn = ¬t=f (diag b n ) ( begin
           not (diag b n)
        ≡⟨⟩
           not (not fun← b n n)
        ≡⟨ cong (λ k → not (k  n) ) (sym (fiso← b _)) ⟩
           not (fun← b (fun→ b (diag b))  n)
        ≡⟨ cong (λ k → not (fun← b k n) ) dn ⟩
           not (fun← b n n)
        ≡⟨⟩
           diag b n 
        ∎ ) where open ≡-Reasoning

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

open import Axiom.Extensionality.Propositional
postulate f-extensionality : { n : Level}  → Axiom.Extensionality.Propositional.Extensionality n n 

record Halt : Set where
   field
      halt :  (t : TM ) → (x : List Bool ) → Bool
      is-halt :     (t : TM ) → (x : List Bool ) → (halt t x ≡ true )  ⇔ ( (just true ≡ tm t x ) ∨ (just false ≡ tm t x ) )
      is-not-halt : (t : TM ) → (x : List Bool ) → (halt t x ≡ false ) ⇔ ( nothing ≡ tm t x )

open Halt

TNL : (halt : Halt ) → (utm : UTM) → HBijection (List Bool → Bool) (List Bool)
TNL halt utm = record {
       fun←  = λ tm x → Halt.halt halt (UTM.utm utm) (tm ++ x)
     ; fun→  = λ h  → encode utm record { tm = h1 h } 
     ; fiso← = λ h →  f-extensionality (λ y → TN1 h y )
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
     h-nothing h y refl | false = refl
     h-just : (h : List Bool → Bool) → (y : List Bool) → h y ≡ true → h1 h y ≡ just true
     h-just h y eq with h y
     h-just h y refl | true = refl
     TN1 :  (h : List Bool → Bool) → (y : List Bool ) → Halt.halt halt (UTM.utm utm) (tenc h y) ≡ h y
     TN1 h y with h y | inspect h y
     ... | true  | record { eq = eq1 } = begin
        Halt.halt halt (UTM.utm utm)  (tenc h y) ≡⟨ proj2 (is-halt halt (UTM.utm utm) (tenc h y) ) (case1 (sym tm-tenc)) ⟩
        true ∎  where
          tm-tenc :  tm (UTM.utm utm) (tenc h y) ≡ just true
          tm-tenc = begin
              tm (UTM.utm utm) (tenc h y)  ≡⟨  is-tm utm _ y ⟩
              h1 h y ≡⟨ h-just h y eq1  ⟩
              just true  ∎  
     ... | false | record { eq = eq1 } = begin
        Halt.halt halt (UTM.utm utm)  (tenc h y) ≡⟨ proj2 (is-not-halt halt (UTM.utm utm) (tenc h y) ) (sym tm-tenc) ⟩
        false ∎  where
          tm-tenc :  tm (UTM.utm utm) (tenc h y) ≡ nothing
          tm-tenc = begin
              tm (UTM.utm utm) (tenc h y)  ≡⟨  is-tm utm _ y ⟩
              h1 h y ≡⟨  h-nothing h y eq1 ⟩
              nothing  ∎  
     -- the rest of bijection means encoding is unique
     -- fiso→ :  (y : List Bool ) → encode utm record { tm = λ x →  h1 (λ tm → Halt.halt halt (UTM.utm utm) tm  ) x } ≡ y
          
