module cfg1 where

open import Level renaming ( suc to succ ; zero to Zero )
open import Data.Nat  hiding ( _≟_ )
open import Data.Fin
open import Data.Product
open import Data.List
open import Data.Maybe
open import Data.Bool using ( Bool ; true ; false ; _∧_ ; _∨_ )
open import  Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Nullary using (¬_; Dec; yes; no)

--
--   Java → Java Byte Code
--
--   CFG    Stack Machine (PDA)
--


data Node (Symbol  : Set) : Set where
    T : Symbol → Node Symbol 
    N : Symbol → Node Symbol 

data Seq (Symbol  : Set) : Set where
    _，_   :  Symbol  → Seq Symbol  → Seq Symbol 
    _．    :  Symbol  → Seq Symbol 
    Error    :  Seq Symbol 

data Body (Symbol  : Set) : Set where
    _｜_   :  Seq Symbol  → Body Symbol  → Body Symbol 
    _；    :  Seq Symbol  → Body Symbol 

record CFGGrammer  (Symbol  : Set) : Set where
   field
      cfg : Symbol → Body Symbol 
      top : Symbol
      eq? : Symbol → Symbol → Bool
      typeof : Symbol →  Node Symbol

infixr  80 _｜_
infixr  90 _；
infixr  100 _，_
infixr  110 _．

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


cfg-language0 :  {Symbol  : Set} → CFGGrammer Symbol   → Body Symbol  →  List Symbol → Bool

{-# TERMINATING #-}
cfg-language1 :  {Symbol  : Set} → CFGGrammer Symbol   → Seq Symbol  →  List Symbol → Bool
cfg-language1 cg Error x = false
cfg-language1 cg (S ， seq) x with typeof cg S
cfg-language1 cg (_ ， seq) (x' ∷ t) | T x =  eq? cg x x' ∧ cfg-language1 cg seq t
cfg-language1 cg (_ ， seq) [] | T x = false
cfg-language1 cg (_ ， seq) x | N nonTerminal = split (cfg-language0 cg (cfg cg nonTerminal) )(cfg-language1 cg seq ) x
cfg-language1 cg (S ．) x with typeof cg S
cfg-language1 cg (_ ．) (x' ∷ []) | T x =  eq? cg x x'
cfg-language1 cg (_ ．) _ | T x = false
cfg-language1 cg (_ ．) x | N nonTerminal = cfg-language0 cg (cfg cg nonTerminal) x

cfg-language0 cg _ [] = false
cfg-language0 cg (rule ｜ b) x =
     cfg-language1 cg rule x  ∨ cfg-language0 cg b x  
cfg-language0 cg (rule ；) x = cfg-language1 cg rule x  

cfg-language :  {Symbol  : Set} → CFGGrammer Symbol   → List Symbol → Bool
cfg-language cg = cfg-language0 cg (cfg cg (top cg )) 


data IFToken : Set where
   EA : IFToken
   EB : IFToken
   EC : IFToken
   IF : IFToken
   THEN : IFToken
   ELSE : IFToken
   SA : IFToken
   SB : IFToken
   SC : IFToken
   expr : IFToken
   statement : IFToken

token-eq? : IFToken → IFToken → Bool
token-eq? EA EA = true
token-eq? EB EB = true
token-eq? EC EC =  true
token-eq? IF IF =  true
token-eq? THEN THEN =  true
token-eq? ELSE ELSE = true
token-eq? SA SA =  true
token-eq? SB SB =  true
token-eq? SC SC = true
token-eq? expr expr = true
token-eq? statement statement = true
token-eq? _ _ = false

typeof-IFG : IFToken → Node IFToken 
typeof-IFG expr = N expr
typeof-IFG statement = N statement
typeof-IFG x = T x

IFGrammer : CFGGrammer IFToken 
IFGrammer = record {
      cfg = cfg'
    ; top = statement
    ; eq? = token-eq?
    ; typeof = typeof-IFG 
   } where
     cfg' : IFToken → Body IFToken 
     cfg' expr =  EA ． ｜  EB ．  ｜   EC ． ； 
     cfg' statement = 
           SA ． ｜   SB ．  ｜   SC ．
         ｜  IF ，  expr ， THEN ， statement ．
         ｜  IF ，  expr ， THEN ， statement  ，  ELSE  ，  statement ．
         ； 
     cfg' x =  Error  ；   

cfgtest1 = cfg-language IFGrammer (  SA ∷ [] ) 

cfgtest2 = cfg-language1 IFGrammer ( SA   ．) (  SA ∷ [] ) 

cfgtest3 = cfg-language1 IFGrammer ( SA    ．  ) (  SA ∷ [] ) 

cfgtest4 = cfg-language IFGrammer  (IF  ∷ EA ∷ THEN  ∷ SA ∷ [] ) 

cfgtest5 = cfg-language1 IFGrammer ( IF  ，  expr  ， THEN ，  statement  ． ) (IF  ∷ EA ∷ THEN  ∷ SA ∷ [] ) 
cfgtest6 = cfg-language1 IFGrammer ( statement  ．)(IF  ∷ EA ∷ SA ∷ [] ) 
cfgtest7 = cfg-language1 IFGrammer ( IF   ，   expr   ， THEN   ，   statement   ，   ELSE    ，   statement   ． )
    (IF  ∷ EA ∷ THEN   ∷ SA ∷ ELSE  ∷ SB  ∷ [] ) 
cfgtest8 = cfg-language IFGrammer  (IF ∷ EA ∷ THEN  ∷ IF ∷ EB ∷ THEN  ∷ SA ∷ ELSE  ∷ SB  ∷ [] ) 
cfgtest9 = cfg-language IFGrammer  (IF ∷ EB ∷ THEN ∷ SA ∷ ELSE  ∷ SB  ∷ [] ) 

data E1Token : Set where
   e1 : E1Token
   e[ : E1Token
   e] : E1Token
   expr : E1Token
   term : E1Token

E1-token-eq? : E1Token → E1Token → Bool
E1-token-eq? e1 e1 = true
E1-token-eq? e[ e] = true
E1-token-eq? e] e] = true
E1-token-eq? expr expr = true
E1-token-eq? term term = true
E1-token-eq? _ _ = false

typeof-E1 : E1Token → Node E1Token
typeof-E1 expr = N expr
typeof-E1 term = N term
typeof-E1 x = T x

E1Grammer : CFGGrammer E1Token
E1Grammer = record {
      cfg = cfgE
    ; top = expr
    ; eq? = E1-token-eq?
    ; typeof = typeof-E1
   } where
     cfgE : E1Token → Body E1Token
     cfgE expr = term ．
       ；
     cfgE term = e1  ．
       ｜   e[   ， expr  ，  e]   ．
       ；
     cfgE x = Error  ；

ecfgtest1 = cfg-language E1Grammer (  e1 ∷ [] )
ecfgtest2 = cfg-language E1Grammer (  e[ ∷ e1 ∷ e] ∷ [] )
ecfgtest3 = cfg-language E1Grammer (  e[ ∷ e[ ∷ e1 ∷ e] ∷ e] ∷ [] )

