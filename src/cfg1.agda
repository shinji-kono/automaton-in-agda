module cfg1 where

open import Level renaming ( suc to succ ; zero to Zero )
open import Data.Nat  hiding ( _≟_ )
-- open import Data.Fin
-- open import Data.Product
open import Data.List
open import Data.Maybe
-- open import Data.Bool using ( Bool ; true ; false ; _∧_ ; _∨_ )
open import  Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Nullary using (¬_; Dec; yes; no)
open import logic

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
split x y  [] = x [] /\ y []
split x y (h  ∷ t) = (x [] /\ y (h  ∷ t)) \/
  split (λ t1 → x (  h ∷ t1 ))  (λ t2 → y t2 ) t


cfg-language0 :  {Symbol  : Set} → CFGGrammer Symbol   → Body Symbol  →  List Symbol → Bool

{-# TERMINATING #-}
cfg-language1 :  {Symbol  : Set} → CFGGrammer Symbol   → Seq Symbol  →  List Symbol → Bool
cfg-language1 cg Error x = false
cfg-language1 cg (S ， seq) x with typeof cg S
cfg-language1 cg (_ ， seq) (x' ∷ t) | T x =  eq? cg x x' /\ cfg-language1 cg seq t
cfg-language1 cg (_ ， seq) [] | T x = false
cfg-language1 cg (_ ， seq) x | N nonTerminal = split (cfg-language0 cg (cfg cg nonTerminal) )(cfg-language1 cg seq ) x
cfg-language1 cg (S ．) x with typeof cg S
cfg-language1 cg (_ ．) (x' ∷ []) | T x =  eq? cg x x'
cfg-language1 cg (_ ．) _ | T x = false
cfg-language1 cg (_ ．) x | N nonTerminal = cfg-language0 cg (cfg cg nonTerminal) x

cfg-language0 cg _ [] = false
cfg-language0 cg (rule ｜ b) x =
     cfg-language1 cg rule x  \/ cfg-language0 cg b x  
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
ecfgtest4 = cfg-language E1Grammer (  e[ ∷ e1 ∷ [] )

open import Function

left : {t : Set } → List E1Token → ( fail next : List E1Token → t ) → t
left ( e[ ∷ t ) fail next = next t
left t fail next = fail t 

right : {t : Set } → List E1Token → ( fail next : List E1Token → t ) → t
right ( e] ∷ t ) fail next = next t
right t fail next = fail t 


{-# TERMINATING #-}
expr1 : {t : Set } → List E1Token → ( fail next : List E1Token → t ) → t
expr1 ( e1 ∷ t ) fail next = next t
expr1 ( expr ∷ t ) fail next = next t
expr1 ( term  ∷ t ) fail next = next t
expr1 x fail next = left x fail $ λ x → expr1 x fail $ λ x → right x fail $ next
-- expr1 x fail next = left x fail ( λ x → expr1 x fail ( λ x → right x fail ( next )))

cfgtest01  = expr1 ( e[ ∷ e[ ∷ e1 ∷ e] ∷ e] ∷ [] ) (λ x → ⟪ false , x ⟫ ) (λ x → ⟪ true , x ⟫ ) 
cfgtest02  = expr1 ( e[ ∷ e[ ∷ e1 ∷ e] ∷ [] ) (λ x → ⟪ false , x ⟫ ) (λ x →  ⟪ true , x ⟫ )
cfgtest03  = expr1 ( e[ ∷ e[ ∷ e1 ∷ e] ∷ e] ∷ e] ∷ [] ) (λ x → ⟪ false , x ⟫ ) (λ x →  ⟪ true , x ⟫ )

open import pushdown

data CG1 : Set where
   ce : CG1
   c1 : CG1

pd  : CG1 → E1Token → CG1 → CG1 ∧ PushDown CG1
pd c1 e[ s = ⟪ c1 , push c1 ⟫
pd c1 e] c1 = ⟪ c1 , pop ⟫
pd c1 e1 c1 = ⟪ c1 , none ⟫
pd s expr s1 = ⟪ c1 , none ⟫
pd s term s1 = ⟪ c1 , none ⟫
pd s _ s1 = ⟪ ce , none ⟫

pok  : CG1 → Bool
pok c1  = true
pok s  = false

pnc : PushDownAutomaton CG1 E1Token CG1
pnc = record {
         pδ  = pd
      ;  pempty = ce
      ;  pok = pok
   }  

pda-ce-test1 = PushDownAutomaton.paccept pnc c1 ( e[ ∷ e[ ∷ e1 ∷ e] ∷ e] ∷ [] ) []
pda-ce-test2 = PushDownAutomaton.paccept pnc c1 ( e[ ∷ e[ ∷ e1 ∷ e] ∷ [] ) []
pda-ce-test3 = PushDownAutomaton.paccept pnc c1 ( e[ ∷ e1 ∷ e] ∷ e1 ∷ [] ) []

record PNC (accept : Bool )  : Set where
  field
    orig-x : List E1Token
    pnc-q : CG1
    pnc-st : List CG1
    pnc-p : CG1 → List CG1 → Bool 
    success : accept ≡ true  → pnc-p pnc-q pnc-st ≡ true  → PushDownAutomaton.paccept pnc c1 orig-x []  ≡ true
    failure : accept ≡ false → pnc-p pnc-q pnc-st ≡ false → PushDownAutomaton.paccept pnc c1 orig-x [] ≡ false

open import Data.Unit

{-# TERMINATING #-}
expr1P : {n : Level } {t : Set n } → (x : List E1Token ) → PNC true 
    → ( fail : List E1Token → PNC false → t ) → ( next : List E1Token → PNC true → t ) → t
expr1P x _ _ _ = {!!}

expr1P-test : (x : List E1Token ) →  ⊤
expr1P-test x = expr1P x record { orig-x = x ; pnc-q = c1 ; pnc-st = []
      ; pnc-p = λ q st → PushDownAutomaton.paccept pnc q x st ; success = λ _ p → p ; failure = λ _ p → p }
      (λ x p → {!!} ) (λ x p → {!!} )

----
--
--  CFG to PDA
--

cfg→pda-state :  {Symbol  : Set} → CFGGrammer Symbol → Set 
cfg→pda-state cfg = {!!}

cfg→pda-start :  {Symbol  : Set} → (cfg : CFGGrammer Symbol) → cfg→pda-state cfg
cfg→pda-start cfg = {!!}

cfg→pda :  {Symbol  : Set} → (cfg : CFGGrammer Symbol) → PDA (cfg→pda-state cfg) Symbol (cfg→pda-state cfg)
cfg→pda cfg = {!!}

cfg->pda : {Symbol  : Set} → (input : List Symbol)
    → (cfg : CFGGrammer Symbol)
    → PDA.paccept (cfg→pda cfg ) (cfg→pda-start cfg) input [] ≡  cfg-language cfg input
cfg->pda = {!!}

----
--
--  PDA to CFG 
--
open import pushdown

pda→cfg :  {Symbol  : Set} { Q : Set} → (pda : PDA Q Symbol Q) → CFGGrammer Symbol
pda→cfg pda = record {
      cfg = {!!}
    ; top = {!!}
    ; eq? = {!!}
    ; typeof = {!!}
   } 

pda->cfg : {Symbol  : Set} { Q : Set} → (start : Q) →  (input : List Symbol)
    → (pda : PDA  Q Symbol Q)
    → PDA.paccept pda start input [] ≡  cfg-language (pda→cfg pda) input
pda->cfg = {!!}

record CDGGrammer  (Symbol  : Set) : Set where
   field
      cdg : Seq Symbol  → Body Symbol 
      top : Symbol
      eq? : Symbol → Symbol → Bool
      typeof : Symbol →  Node Symbol

