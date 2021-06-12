{-# OPTIONS --allow-unsolved-metas #-}
module turing where

open import Level renaming ( suc to succ ; zero to Zero )
open import Data.Nat -- hiding ( erase )
open import Data.List
open import Data.Maybe hiding ( map )
open import Data.Bool using ( Bool ; true ; false ) renaming ( not to negate )
open import  Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Level renaming ( suc to succ ; zero to Zero )
open import Data.Product hiding ( map )


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

{-# TERMINATING #-}
move : {Q Σ : Set } → { tnone : Σ} → {tδ : Q →  Σ → Q × ( Write  Σ ) ×  Move } → (q : Q ) ( L : List  Σ ) ( L : List   Σ ) → ( Q × List  Σ × List  Σ )
move {Q} {Σ} {tnone} {tδ} q L [] = move {Q} {Σ} {tnone} {tδ} q  L  ( tnone  ∷ [] ) 
move {Q} {Σ} {tnone} {tδ} q [] R = move {Q} {Σ} {tnone} {tδ} q  ( tnone  ∷ [] )  R 
move {Q} {Σ} {tnone} {tδ} q ( LH  ∷ LT ) ( RH ∷ RT ) with  tδ q LH  
... | nq , write x , left  = ( nq , ( RH ∷ x  ∷ LT ) , RT )
... | nq , write x , right = ( nq , LT , ( x  ∷ RH  ∷ RT ) )
... | nq , write x , mnone = ( nq , ( x  ∷ LT ) , (  RH ∷ RT ) )
... | nq , wnone , left    = ( nq , ( RH  ∷ LH  ∷ LT ) , RT  )
... | nq , wnone , right   = ( nq ,  LT , ( LH  ∷ RH  ∷ RT ) )
... | nq , wnone , mnone   = ( nq , ( LH  ∷ LT ) , (  RH ∷ RT )  )
{-# TERMINATING #-}
move-loop : {Q Σ : Set } → {tend :  Q → Bool}  → { tnone : Σ} → {tδ : Q →  Σ → Q × ( Write  Σ ) ×  Move }
    → (q : Q ) ( L : List  Σ ) ( L : List   Σ ) → ( Q × List  Σ × List  Σ )
move-loop {Q} {Σ} {tend} {tnone} {tδ}  q L R with tend q
... | true = ( q , L , R )
... | flase = move-loop {Q} {Σ} {tend} {tnone} {tδ} ( proj₁ next ) ( proj₁ ( proj₂ next ) )  ( proj₂  ( proj₂ next ) )
        where
        next = move {Q} {Σ} {tnone} {tδ} q  L  R 

{-# TERMINATING #-}
move0 : {Q Σ : Set } ( tend : Q → Bool ) (tnone : Σ ) (tδ : Q →  Σ → Q × ( Write  Σ ) ×  Move)
   (q : Q ) ( L : List  Σ ) ( L : List   Σ ) → ( Q × List  Σ × List  Σ )
move0 tend tnone tδ  q L R with tend q
... | true = ( q , L , R )
move0 tend tnone tδ  q L [] | false = move0 tend tnone tδ  q  L  ( tnone  ∷ [] ) 
move0 tend tnone tδ  q [] R | false = move0 tend tnone tδ  q  ( tnone  ∷ [] )  R 
move0 tend tnone tδ  q ( LH  ∷ LT ) ( RH ∷ RT ) | false with  tδ q LH  
... | nq , write x , left  = move0 tend tnone tδ  nq ( RH ∷ x  ∷ LT ) RT 
... | nq , write x , right = move0 tend tnone tδ  nq LT ( x  ∷ RH  ∷ RT ) 
... | nq , write x , mnone = move0 tend tnone tδ  nq ( x  ∷ LT ) (  RH ∷ RT ) 
... | nq , wnone , left    = move0 tend tnone tδ  nq ( RH  ∷ LH  ∷ LT ) RT  
... | nq , wnone , right   = move0 tend tnone tδ  nq  LT ( LH  ∷ RH  ∷ RT ) 
... | nq , wnone , mnone   = move0 tend tnone tδ  nq ( LH  ∷ LT ) (  RH ∷ RT )  

record Turing ( Q : Set ) ( Σ : Set  ) 
       : Set  where
    field
        tδ : Q →  Σ → Q × ( Write  Σ ) ×  Move 
        tstart : Q
        tend : Q → Bool
        tnone :  Σ
    taccept : List  Σ → ( Q × List  Σ × List  Σ )
    taccept L = move0 tend tnone tδ tstart L []

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

test1 : CopyStates × ( List  ℕ ) × ( List  ℕ )
test1 = Turing.taccept copyMachine  ( 1  ∷ 1  ∷ 0  ∷ 0  ∷  0 ∷ []  )

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

