{-# OPTIONS --cubical-compatible --safe #-}
-- {-# OPTIONS --allow-unsolved-metas #-}
module turing where

open import Level renaming ( suc to succ ; zero to Zero )
open import Data.Nat -- hiding ( erase )
open import Data.List
open import Data.Maybe hiding ( map )
-- open import Data.Bool using ( Bool ; true ; false ) renaming ( not to negate )
open import  Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Level renaming ( suc to succ ; zero to Zero )
open import Data.Product hiding ( map )
open import logic 


data Write   (  Σ : Set  ) : Set  where
   write   : Σ → Write  Σ
   wnone   : Write  Σ
   --   erase write tnone

data Move : Set  where
   left   : Move  
   right  : Move  
   mnone  : Move  

-- at tδ both stack is poped

-- write S      push S  , push SR
-- erase        push SL , push tone 
-- none         push SL , push SR 
-- left         push SR , pop      
-- right        pop     , push SL      

move : {Q Σ : Set } → { tnone : Σ} → {tδ : Q →  Σ → Q × ( Write  Σ ) ×  Move } → (q : Q ) ( L : List  Σ ) ( L : List   Σ ) → ( Q × List  Σ × List  Σ )
move {Q} {Σ} {tnone} {tδ} q ( LH  ∷ LT ) ( RH ∷ RT ) with  tδ q LH  
... | nq , write x , left  = ( nq , ( RH ∷ x  ∷ LT ) , RT )
... | nq , write x , right = ( nq , LT , ( x  ∷ RH  ∷ RT ) )
... | nq , write x , mnone = ( nq , ( x  ∷ LT ) , (  RH ∷ RT ) )
... | nq , wnone , left    = ( nq , ( RH  ∷ LH  ∷ LT ) , RT  )
... | nq , wnone , right   = ( nq ,  LT , ( LH  ∷ RH  ∷ RT ) )
... | nq , wnone , mnone   = ( nq , ( LH  ∷ LT ) , (  RH ∷ RT )  )
move {Q} {Σ} {tnone} {tδ} q ( LH  ∷ LT ) [] with  tδ q LH  
... | nq , write x , left  = ( nq , ( tnone ∷ x  ∷ LT ) , [] )
... | nq , write x , right = ( nq , LT , ( x  ∷ tnone  ∷ [] ) )
... | nq , write x , mnone = ( nq , ( x  ∷ LT ) , (  tnone ∷ [] ) )
... | nq , wnone , left    = ( nq , ( tnone  ∷ LH  ∷ LT ) , []  )
... | nq , wnone , right   = ( nq ,  LT , ( LH  ∷ tnone  ∷ [] ) )
... | nq , wnone , mnone   = ( nq , ( LH  ∷ LT ) , (  tnone ∷ [] )  )
move {Q} {Σ} {tnone} {tδ} q [] ( RH ∷ RT ) with  tδ q tnone
... | nq , write x , left  = ( nq , ( RH ∷ x  ∷ [] ) , RT )
... | nq , write x , right = ( nq , [] , ( x  ∷ RH  ∷ RT ) )
... | nq , write x , mnone = ( nq , ( x  ∷ [] ) , (  RH ∷ RT ) )
... | nq , wnone , left    = ( nq , ( RH  ∷ tnone  ∷ [] ) , RT  )
... | nq , wnone , right   = ( nq ,  [] , ( tnone  ∷ RH  ∷ RT ) )
... | nq , wnone , mnone   = ( nq , ( tnone  ∷ [] ) , (  RH ∷ RT )  )
move {Q} {Σ} {tnone} {tδ} q [] [] with  tδ q tnone
... | nq , write x , left  = ( nq , ( tnone ∷ x  ∷ [] ) , [] )
... | nq , write x , right = ( nq , [] , ( x  ∷ tnone  ∷ [] ) )
... | nq , write x , mnone = ( nq , ( x  ∷ [] ) , (  tnone ∷ [] ) )
... | nq , wnone , left    = ( nq , ( tnone  ∷ tnone  ∷ [] ) , []  )
... | nq , wnone , right   = ( nq ,  [] , ( tnone  ∷ tnone  ∷ [] ) )
... | nq , wnone , mnone   = ( nq , ( tnone  ∷ [] ) , (  tnone ∷ [] )  )

move-loop : (i : ℕ) {Q Σ : Set } → {tend :  Q → Bool}  → { tnone : Σ} → {tδ : Q →  Σ → Q × ( Write  Σ ) ×  Move }
    → (q : Q ) ( L : List  Σ ) ( L : List   Σ ) → ( Q × List  Σ × List  Σ )
move-loop zero {Q} {Σ} {tend} {tnone} {tδ}  q L R = ( q , L , R )
move-loop (suc i) {Q} {Σ} {tend} {tnone} {tδ}  q L R with tend q
... | true = ( q , L , R )
... | flase = move-loop i {Q} {Σ} {tend} {tnone} {tδ} ( proj₁ next ) ( proj₁ ( proj₂ next ) )  ( proj₂  ( proj₂ next ) )
        where
        next = move {Q} {Σ} {tnone} {tδ} q  L  R 

move0 : {Q Σ : Set } ( tend : Q → Bool ) (tnone : Σ ) (tδ : Q →  Σ → Q × ( Write  Σ ) ×  Move)
   (q : Q ) ( L : List  Σ ) ( L : List   Σ ) → ( Q × List  Σ × List  Σ )
move0 tend tnone tδ  q ( LH  ∷ LT ) ( RH ∷ RT ) with  tδ q LH  
... | nq , write x , left  = nq , ( RH ∷ x  ∷ LT ) , RT 
... | nq , write x , right = nq , LT , ( x  ∷ RH  ∷ RT ) 
... | nq , write x , mnone = nq , ( x  ∷ LT ) , (  RH ∷ RT ) 
... | nq , wnone , left    = nq , ( RH  ∷ LH  ∷ LT ) , RT  
... | nq , wnone , right   = nq  , LT , ( LH  ∷ RH  ∷ RT ) 
... | nq , wnone , mnone   = ( q , ( LH  ∷ LT ) , (  RH ∷ RT )  )
move0 tend tnone tδ  q ( LH  ∷ LT ) [] with  tδ q LH  
... | nq , write x , left  = nq , ( tnone ∷ x  ∷ LT ) , [] 
... | nq , write x , right = nq , LT , ( x  ∷ tnone  ∷ [] ) 
... | nq , write x , mnone = nq , ( x  ∷ LT ) , (  tnone ∷ [] ) 
... | nq , wnone , left    = nq , ( tnone  ∷ LH  ∷ LT ) , []  
... | nq , wnone , right   = nq ,  LT , ( LH  ∷ tnone  ∷ [] ) 
... | nq , wnone , mnone   = nq , ( LH  ∷ LT ) , (  tnone ∷ [] )  
move0 tend tnone tδ  q [] ( RH ∷ RT ) with  tδ q tnone  
... | nq , write x , left  = nq , ( RH ∷ x  ∷ [] ) , RT 
... | nq , write x , right = nq , [] , ( x  ∷ RH  ∷ RT ) 
... | nq , write x , mnone = nq , ( x  ∷ [] ) , (  RH ∷ RT ) 
... | nq , wnone , left    = nq , ( RH  ∷ tnone  ∷ [] ) , RT  
... | nq , wnone , right   = nq ,  [] , ( tnone  ∷ RH  ∷ RT ) 
... | nq , wnone , mnone   = nq , ( tnone  ∷ [] ) , (  RH ∷ RT )  
move0 tend tnone tδ  q [] [] with  tδ q tnone  
... | nq , write x , left  = nq , ( tnone ∷ x  ∷ [] ) , [] 
... | nq , write x , right = nq , [] , ( x  ∷ tnone  ∷ [] ) 
... | nq , write x , mnone = nq , ( x  ∷ [] ) , (  tnone ∷ [] ) 
... | nq , wnone , left    = nq , ( tnone  ∷ tnone  ∷ [] ) , []  
... | nq , wnone , right   = nq ,  [] , ( tnone  ∷ tnone  ∷ [] ) 
... | nq , wnone , mnone   = nq , ( tnone  ∷ [] ) , (  tnone ∷ [] )  

record Turing ( Q : Set ) ( Σ : Set  ) 
       : Set  where
    field
        tδ : Q →  Σ → Q × ( Write  Σ ) ×  Move 
        tstart : Q
        tend : Q → Bool
        tnone :  Σ
    taccept : (i : ℕ ) → List  Σ → ( Q × List  Σ × List  Σ )
    taccept i L = tloop i tstart [] []  where
        tloop : (i : ℕ)  (q : Q ) ( L : List  Σ ) ( L : List   Σ ) → ( Q × List  Σ × List  Σ )
        tloop zero q L R = ( q , L , R )
        tloop (suc i) q L R with tend q
        ... | true = ( q , L , R )
        ... | false with move0 tend tnone tδ q L R 
        ... | nq , L , R = tloop i nq L R

open import automaton

-- ATuring : {Σ : Set } → Automaton (List Σ) Σ 
-- ATuring = record { δ = {!!} ; aend = {!!} }

open import automaton
open Automaton

move1 : {Q Σ : Set } (tnone : Σ ) (δ : Q →  Σ → Q ) (tδ : Q → Σ →  Write  Σ  ×  Move)
   (q : Q ) ( L : List  Σ ) ( R : List   Σ ) →  Q × List  Σ × List  Σ 
move1 tnone δ tδ  q ( LH  ∷ LT ) ( RH ∷ RT ) with tδ (δ q LH) LH
... |  write x , left  = (δ q LH) , ( RH ∷ x  ∷ LT ) , RT 
... |  write x , right = (δ q LH) , LT , ( x  ∷ RH  ∷ RT ) 
... |  write x , mnone = (δ q LH) , ( x  ∷ LT ) , (  RH ∷ RT ) 
... |  wnone , left    = (δ q LH) , ( RH  ∷ LH  ∷ LT ) , RT  
... |  wnone , right   = (δ q LH) ,  LT , ( LH  ∷ RH  ∷ RT ) 
... |  wnone , mnone   = (δ q LH) , ( LH  ∷ LT ) , (  RH ∷ RT )  
move1 tnone δ tδ  q ( LH  ∷ LT ) [] with tδ (δ q LH) LH
... |  write x , left  = (δ q LH) , ( tnone ∷ x  ∷ LT ) , [] 
... |  write x , right = (δ q LH) , LT , ( x  ∷ tnone  ∷ [] ) 
... |  write x , mnone = (δ q LH) , ( x  ∷ LT ) , (  tnone ∷ [] ) 
... |  wnone , left    = (δ q LH) , ( tnone  ∷ LH  ∷ LT ) , []  
... |  wnone , right   = (δ q LH) ,  LT , ( LH  ∷ tnone  ∷ [] ) 
... |  wnone , mnone   = (δ q LH) , ( LH  ∷ LT ) , (  tnone ∷ [] )  
move1 tnone δ tδ  q [] ( RH ∷ RT ) with tδ (δ q tnone) tnone
... |  write x , left  = (δ q tnone) , ( RH ∷ x  ∷ [] ) , RT 
... |  write x , right = (δ q tnone) , [] , ( x  ∷ RH  ∷ RT ) 
... |  write x , mnone = (δ q tnone) , ( x  ∷ [] ) , (  RH ∷ RT ) 
... |  wnone , left    = (δ q tnone) , ( RH  ∷ tnone  ∷ [] ) , RT  
... |  wnone , right   = (δ q tnone) ,  [] , ( tnone  ∷ RH  ∷ RT ) 
... |  wnone , mnone   = (δ q tnone) , ( tnone  ∷ [] ) , (  RH ∷ RT )  
move1 tnone δ tδ  q [] [] with tδ (δ q tnone) tnone
... |  write x , left  = (δ q tnone) , ( tnone ∷ x  ∷ [] ) , [] 
... |  write x , right = (δ q tnone) , [] , ( x  ∷ tnone  ∷ [] ) 
... |  write x , mnone = (δ q tnone) , ( x  ∷ [] ) , (  tnone ∷ [] ) 
... |  wnone , left    = (δ q tnone) , ( tnone  ∷ tnone  ∷ [] ) , []  
... |  wnone , right   = (δ q tnone) ,  [] , ( tnone  ∷ tnone  ∷ [] ) 
... |  wnone , mnone   = (δ q tnone) , ( tnone  ∷ [] ) , (  tnone ∷ [] )  

record TM ( Q : Set ) ( Σ : Set  ) 
       : Set  where
    field
        automaton : Automaton  Q Σ
        tδ : Q → Σ → Write  Σ  ×  Move 
        tnone :  Σ
    taccept : (i : ℕ) → Q → List  Σ → ( Q × List  Σ × List  Σ )
    taccept i q L = tloop i q L []  where
        tloop : (i : ℕ) → (q : Q ) ( L : List  Σ ) ( R : List   Σ ) →  Q × List  Σ × List  Σ 
        tloop i q L R with aend automaton q
        ... | true = ( q , L , R )
        tloop zero q L R  | false = ( q , L , R )
        tloop (suc i) q L R  | false with move1 tnone (δ automaton) tδ q L R
        ... | q' , L' , R' = tloop i q' L' R'

data CopyStates : Set where
   s1 : CopyStates
   s2 : CopyStates
   s3 : CopyStates
   s4 : CopyStates
   s5 : CopyStates
   H  : CopyStates


Copyδ :  CopyStates →  ℕ  → CopyStates × ( Write  ℕ ) × Move 
Copyδ s1 0  = H    , wnone       , mnone 
Copyδ s1 1  = s2   , write 0 , right 
Copyδ s2 0  = s3   , write 0 , right 
Copyδ s2 1  = s2   , write 1 , right 
Copyδ s3 0  = s4   , write 1 , left 
Copyδ s3 1  = s3   , write 1 , right 
Copyδ s4 0  = s5   , write 0 , left 
Copyδ s4 1  = s4   , write 1 , left 
Copyδ s5 0  = s1   , write 1 , right 
Copyδ s5 1  = s5   , write 1 , left 
Copyδ H  _  = H    , wnone   , mnone 
Copyδ _  (suc (suc _))      = H    , wnone       , mnone 

copyMachine : Turing CopyStates ℕ
copyMachine = record {
        tδ = Copyδ
     ;  tstart = s1
     ;  tend = tend
     ;  tnone =  0
  } where
      tend : CopyStates →  Bool
      tend H = true
      tend _ = false

copyTM : TM CopyStates ℕ
copyTM = record {
        automaton = record { δ = λ q i → proj₁ (Copyδ q i) ; aend = tend }
     ;  tδ = λ q i → proj₂ (Copyδ q i )
     ;  tnone =  0
  } where
      tend : CopyStates →  Bool
      tend H = true
      tend _ = false

test1 : CopyStates × ( List  ℕ ) × ( List  ℕ )
test1 = Turing.taccept copyMachine  10 ( 1  ∷ 1  ∷ 0  ∷ 0  ∷  0 ∷ []  )

test2 : ℕ  → CopyStates × ( List  ℕ ) × ( List  ℕ )
test2 n  = loop n (Turing.tstart copyMachine) ( 1  ∷ 1  ∷ 0  ∷ 0  ∷  0 ∷ []  ) []
  where
        loop :  ℕ → CopyStates → ( List  ℕ ) → ( List  ℕ ) → CopyStates × ( List  ℕ ) × ( List  ℕ )
        loop zero q L R = ( q , L , R )
        loop (suc n) q L R = loop n ( proj₁ t1 ) ( proj₁ ( proj₂ t1 ) )  ( proj₂  ( proj₂ t1 ) )
          where
              t1 = move {CopyStates} {ℕ} {0} {Copyδ} q L R

-- testn = map (\ n -> test2 n) ( 0 ∷  1 ∷  2 ∷  3 ∷  4 ∷  5 ∷  6 ∷  [] )

testn : ℕ →  List ( CopyStates × ( List  ℕ ) × ( List  ℕ ) )
testn 0 = test2 0 ∷ []
testn (suc n)  = test2 n ∷ testn n

