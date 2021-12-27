module cfg where

open import Level renaming ( suc to succ ; zero to Zero )
open import Data.Nat  hiding ( _≟_ )
open import Data.Fin
open import Data.Product
open import Data.List
open import Data.Maybe
open import Data.Bool using ( Bool ; true ; false ; _∧_ ; _∨_ )
open import  Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Nullary using (¬_; Dec; yes; no)
-- open import Data.String

data IsTerm (Token : Set) : Set where
    isTerm :  Token → IsTerm Token
    noTerm  : IsTerm Token

record CFGGrammer  (Token Node : Set) : Set (succ Zero) where
   field
      cfg : Node → List ( List ( Node ) )
      cfgtop : Node
      term? :  Node → IsTerm Token
      tokensz : ℕ
      tokenid : Token → Fin tokensz

open CFGGrammer 

-----------------
--
-- CGF language
--
-----------------

split : {Σ : Set} → (List Σ → Bool)
      → ( List Σ → Bool) → List Σ → Bool
split x y  [] = x [] ∧ y []
split x y (h  ∷ t) = (x [] ∧ y (h  ∷ t)) ∨
  split (λ t1 → x (  h ∷ t1 ))  (λ t2 → y t2 ) t


cfg-language0 :  {Node  Token : Set} → CFGGrammer  Token Node  → List (List Node ) →  List Token → Bool

{-# TERMINATING #-}
cfg-language2 :  {Node  Token : Set} → CFGGrammer  Token Node  → Node →  List Token → Bool
cfg-language2 cg _ [] = false
cfg-language2 cg x (h1  ∷ [] ) with term? cg x
cfg-language2 cg x (h1 ∷ []) | isTerm t with tokenid cg h1 ≟ tokenid cg t
cfg-language2 cg x (h1 ∷ []) | isTerm t | yes p = true
cfg-language2 cg x (h1 ∷ []) | isTerm t | no ¬p = false
cfg-language2 cg x (h1 ∷ []) | noTerm = cfg-language0 cg (cfg cg x) ( h1 ∷ [] )
cfg-language2 cg x In with term? cg x
cfg-language2 cg x In | isTerm t = false
cfg-language2 cg x In | noTerm =  cfg-language0 cg (cfg cg x ) In

cfg-language1 :  {Node  Token : Set} → CFGGrammer  Token Node  → List Node →  List Token → Bool
cfg-language1 cg [] [] = true
cfg-language1 cg [] _ = false
cfg-language1 cg (node ∷ T) = split ( cfg-language2 cg node ) ( cfg-language1 cg T )

cfg-language0 cg [] [] = true
cfg-language0 cg [] _ = false
cfg-language0 cg (node ∷ T) In = cfg-language1 cg node In ∨ cfg-language0 cg T In 

cfg-language :  {Node  Token : Set} → CFGGrammer  Token Node  →  List Token → Bool
cfg-language cg = cfg-language0 cg (cfg cg (cfgtop cg))

-----------------

data IFToken : Set where
   t:EA : IFToken
   t:EB : IFToken
   t:EC : IFToken
   t:IF : IFToken
   t:THEN : IFToken
   t:ELSE : IFToken
   t:SA : IFToken
   t:SB : IFToken
   t:SC : IFToken

IFtokenid : IFToken → Fin 9
IFtokenid t:EA = # 0
IFtokenid t:EB = # 1
IFtokenid t:EC = # 2
IFtokenid t:IF = # 3
IFtokenid t:THEN = # 4
IFtokenid t:ELSE = # 5
IFtokenid t:SA = # 6
IFtokenid t:SB = # 7
IFtokenid t:SC = # 8

data IFNode (T : Set) : Set where
   Token : T → IFNode T
   expr : IFNode T
   statement : IFNode T

IFGrammer : CFGGrammer IFToken (IFNode IFToken) 
IFGrammer = record {
      cfg = cfg'
    ; cfgtop = statement
    ; term? = term?'
    ; tokensz = 9
    ; tokenid = IFtokenid
   } where
     term?' : IFNode IFToken → IsTerm IFToken
     term?' (Token x) = isTerm x
     term?' _ = noTerm
     cfg' :  IFNode IFToken → List ( List (IFNode IFToken) )
     cfg' (Token t) = ( (Token t)  ∷ [] ) ∷ [] 
     cfg' expr  =  ( Token t:EA  ∷ [] )  ∷
                  ( Token t:EB  ∷ [] )  ∷
                  ( Token t:EC  ∷ [] )  ∷ [] 
     cfg' statement = ( Token t:SA   ∷ [] ) ∷ 
                     ( Token t:SB   ∷ [] ) ∷ 
                     ( Token t:SC   ∷ [] ) ∷ 
                     ( Token t:IF ∷ expr ∷ statement ∷ [] ) ∷ 
                     ( Token t:IF ∷ expr ∷ statement ∷ Token t:ELSE ∷ statement ∷ [] ) ∷  [] 


cfgtest1 = cfg-language IFGrammer (  t:SA ∷ [] ) 

cfgtest2 = cfg-language2 IFGrammer (Token t:SA) (  t:SA ∷ [] ) 

cfgtest3 = cfg-language1 IFGrammer (Token t:SA  ∷ []  ) (  t:SA ∷ [] ) 

cfgtest4 = cfg-language IFGrammer  (t:IF  ∷ t:EA ∷ t:SA ∷ [] ) 

cfgtest5 = cfg-language1 IFGrammer (Token t:IF ∷ expr ∷ statement ∷ []) (t:IF  ∷ t:EA ∷ t:EA ∷ [] ) 
cfgtest6 = cfg-language2 IFGrammer statement (t:IF  ∷ t:EA ∷ t:SA ∷ [] ) 
cfgtest7 = cfg-language1 IFGrammer (Token t:IF ∷ expr ∷ statement ∷ Token t:ELSE  ∷ statement  ∷ []) (t:IF  ∷ t:EA ∷ t:SA ∷ t:ELSE  ∷ t:SB  ∷ [] ) 

cfgtest8 = cfg-language IFGrammer  (t:IF  ∷ t:EA ∷ t:IF ∷ t:EB ∷ t:SA ∷ t:ELSE  ∷ t:SB  ∷ [] ) 

