module utm where

open import turing
open import Data.Product
-- open import Data.Bool
open import Data.List
open import Data.Nat
open import logic

data utmStates : Set where
     reads : utmStates
     read0 : utmStates
     read1 : utmStates
     read2 : utmStates
     read3 : utmStates
     read4 : utmStates
     read5 : utmStates
     read6 : utmStates
     
     loc0 : utmStates
     loc1 : utmStates
     loc2 : utmStates
     loc3 : utmStates
     loc4 : utmStates
     loc5 : utmStates
     loc6 : utmStates
     
     fetch0 : utmStates
     fetch1 : utmStates
     fetch2 : utmStates
     fetch3 : utmStates
     fetch4 : utmStates
     fetch5 : utmStates
     fetch6 : utmStates
     fetch7 : utmStates
     
     print0 : utmStates
     print1 : utmStates
     print2 : utmStates
     print3 : utmStates
     print4 : utmStates
     print5 : utmStates
     print6 : utmStates
     print7 : utmStates
     
     mov0 : utmStates
     mov1 : utmStates
     mov2 : utmStates
     mov3 : utmStates
     mov4 : utmStates
     mov5 : utmStates
     mov6 : utmStates
     
     tidy0 : utmStates
     tidy1 : utmStates
     halt : utmStates

data utmΣ : Set where
    ０ : utmΣ
    １ : utmΣ
    B : utmΣ
    * : utmΣ
    $ : utmΣ
    ^ : utmΣ
    X : utmΣ
    Y : utmΣ
    Z : utmΣ
    ＠ : utmΣ
    b : utmΣ

utmδ :  utmStates →  utmΣ  → utmStates × (Write utmΣ) × Move
utmδ reads  x = read0 , wnone , mnone
utmδ read0  * = read1 , write * , left
utmδ read0  x = read0 , write x , right
utmδ read1  x = read2 , write ＠ , right
utmδ read2  ^ = read3 , write ^ , right
utmδ read2  x = read2 , write x , right
utmδ read3  ０ = read4 , write ０ , left
utmδ read3  １ = read5 , write １ , left
utmδ read3  b = read6 , write b , left
utmδ read4  ＠ = loc0 , write ０ , right
utmδ read4  x = read4 , write x , left
utmδ read5  ＠ = loc0 , write １ , right
utmδ read5  x = read5 , write x , left
utmδ read6  ＠ = loc0 , write B , right
utmδ read6  x = read6 , write x , left
utmδ loc0  ０ = loc0 , write X , left
utmδ loc0  １ = loc0 , write Y , left
utmδ loc0  B = loc0 , write Z , left
utmδ loc0  $ = loc1 , write $ , right
utmδ loc0  x = loc0 , write x , left
utmδ loc1  X = loc2 , write ０ , right
utmδ loc1  Y = loc3 , write １ , right
utmδ loc1  Z = loc4 , write B , right
utmδ loc1  * = fetch0 , write * , right
utmδ loc1  x = loc1 , write x , right
utmδ loc2  ０ = loc5 , write X , right
utmδ loc2  １ = loc6 , write Y , right
utmδ loc2  B = loc6 , write Z , right
utmδ loc2  x = loc2 , write x , right
utmδ loc3  １ = loc5 , write Y , right
utmδ loc3  ０ = loc6 , write X , right
utmδ loc3  B = loc6 , write Z , right
utmδ loc3  x = loc3 , write x , right
utmδ loc4  B = loc5 , write Z , right
utmδ loc4  ０ = loc6 , write X , right
utmδ loc4  １ = loc6 , write Y , right
utmδ loc4  x = loc4 , write x , right
utmδ loc5  $ = loc1 , write $ , right
utmδ loc5  x = loc5 , write x , left
utmδ loc6  $ = halt , write $ , right
utmδ loc6  * = loc0 , write * , left
utmδ loc6  x = loc6 , write x , right
utmδ fetch0  ０ = fetch1 , write X , left
utmδ fetch0  １ = fetch2 , write Y , left
utmδ fetch0  B = fetch3 , write Z , left
utmδ fetch0  x = fetch0 , write x , right
utmδ fetch1  $ = fetch4 , write $ , right
utmδ fetch1  x = fetch1 , write x , left
utmδ fetch2  $ = fetch5 , write $ , right
utmδ fetch2  x = fetch2 , write x , left
utmδ fetch3  $ = fetch6 , write $ , right
utmδ fetch3  x = fetch3 , write x , left
utmδ fetch4  ０ = fetch7 , write X , right
utmδ fetch4  １ = fetch7 , write X , right
utmδ fetch4  B = fetch7 , write X , right
utmδ fetch4  * = print0 , write * , left
utmδ fetch4  x = fetch4 , write x , right
utmδ fetch5  ０ = fetch7 , write Y , right
utmδ fetch5  １ = fetch7 , write Y , right
utmδ fetch5  B = fetch7 , write Y , right
utmδ fetch5  * = print0 , write * , left
utmδ fetch5  x = fetch5 , write x , right
utmδ fetch6  ０ = fetch7 , write Z , right
utmδ fetch6  １ = fetch7 , write Z , right
utmδ fetch6  B = fetch7 , write Z , right
utmδ fetch6  * = print0 , write * , left
utmδ fetch6  x = fetch6 , write x , right
utmδ fetch7  * = fetch0 , write * , right
utmδ fetch7  x = fetch7 , write x , right
utmδ print0  X = print1 , write X , right
utmδ print0  Y = print2 , write Y , right
utmδ print0  Z = print3 , write Z , right
utmδ print1  ^ = print4 , write ^ , right
utmδ print1  x = print1 , write x , right
utmδ print2  ^ = print5 , write ^ , right
utmδ print2  x = print2 , write x , right
utmδ print3  ^ = print6 , write ^ , right
utmδ print3  x = print3 , write x , right
utmδ print4  x = print7 , write ０ , left
utmδ print5  x = print7 , write １ , left
utmδ print6  x = print7 , write B , left
utmδ print7  X = mov0 , write X , right
utmδ print7  Y = mov1 , write Y , right
utmδ print7  x = print7 , write x , left
utmδ mov0  ^ = mov2 , write ^ , left
utmδ mov0  x = mov0 , write x , right
utmδ mov1  ^ = mov3 , write ^ , right
utmδ mov1  x = mov1 , write x , right
utmδ mov2  ０ = mov4 , write ^ , right
utmδ mov2  １ = mov5 , write ^ , right
utmδ mov2  B = mov6 , write ^ , right
utmδ mov3  ０ = mov4 , write ^ , left
utmδ mov3  １ = mov5 , write ^ , left
utmδ mov3  B = mov6 , write ^ , left
utmδ mov4  ^ = tidy0 , write ０ , left
utmδ mov5  ^ = tidy0 , write １ , left
utmδ mov6  ^ = tidy0 , write B , left
utmδ tidy0  $ = tidy1 , write $ , left
utmδ tidy0  x = tidy0 , write x , left
utmδ tidy1  X = tidy1 , write ０ , left
utmδ tidy1  Y = tidy1 , write １ , left
utmδ tidy1  Z = tidy1 , write B , left
utmδ tidy1  $ = reads , write $ , right
utmδ tidy1  x = tidy1 , write x , left
utmδ _  x = halt , write x , mnone

U-TM : Turing utmStates utmΣ
U-TM = record {
        tδ = utmδ
     ;  tstart = read0
     ;  tend = tend
     ;  tnone =  b
  } where
      tend : utmStates →  Bool
      tend halt = true
      tend _ = false

-- Copyδ :  CopyStates →  ℕ  → CopyStates × ( Write  ℕ ) × Move
-- Copyδ s1 0  = H    , wnone       , mnone
-- Copyδ s1 1  = s2   , write 0 , right
-- Copyδ s2 0  = s3   , write 0 , right
-- Copyδ s2 1  = s2   , write 1 , right
-- Copyδ s3 0  = s4   , write 1 , left
-- Copyδ s3 1  = s3   , write 1 , right
-- Copyδ s4 0  = s5   , write 0 , left
-- Copyδ s4 1  = s4   , write 1 , left
-- Copyδ s5 0  = s1   , write 1 , right
-- Copyδ s5 1  = s5   , write 1 , left
-- Copyδ H  _  = H    , wnone   , mnone
-- Copyδ _  (suc (suc _))      = H    , wnone       , mnone

Copyδ-encode : List utmΣ
Copyδ-encode = 
       ０  ∷ ０  ∷ １  ∷ ０  ∷  １ ∷ １ ∷ ０ ∷ ０ ∷ ０ ∷ ０ ∷   -- s1 0  = H    , wnone       , mnone
  *  ∷ ０  ∷ ０  ∷ １  ∷ １  ∷  ０ ∷ １ ∷ ０ ∷ ０ ∷ ０ ∷ １ ∷   -- s1 1  = s2   , write 0 , right
  *  ∷ ０  ∷ １  ∷ ０  ∷ ０  ∷  ０ ∷ １ ∷ １ ∷ ０ ∷ ０ ∷ １ ∷   -- s2 0  = s3   , write 0 , right
  *  ∷ ０  ∷ １  ∷ ０  ∷ １  ∷  ０ ∷ １ ∷ ０ ∷ １ ∷ ０ ∷ １ ∷   -- s2 1  = s2   , write 1 , right
  *  ∷ ０  ∷ １  ∷ １  ∷ ０  ∷  １ ∷ ０ ∷ ０ ∷ １ ∷ ０ ∷ ０ ∷   -- s3 0  = s4   , write 1 , left
  *  ∷ ０  ∷ １  ∷ １  ∷ １  ∷  ０ ∷ １ ∷ １ ∷ １ ∷ ０ ∷ １ ∷   -- s3 1  = s3   , write 1 , right
  *  ∷ １  ∷ ０  ∷ ０  ∷ ０  ∷  １ ∷ ０ ∷ １ ∷ ０ ∷ ０ ∷ ０ ∷   -- s4 0  = s5   , write 0 , left
  *  ∷ １  ∷ ０  ∷ ０  ∷ １  ∷  １ ∷ ０ ∷ ０ ∷ １ ∷ ０ ∷ ０ ∷   -- s4 1  = s4   , write 1 , left
  *  ∷ １  ∷ ０  ∷ １  ∷ ０  ∷  ０ ∷ ０ ∷ １ ∷ １ ∷ ０ ∷ １ ∷   -- s5 0  = s1   , write 1 , right
  *  ∷ １  ∷ ０  ∷ １  ∷ １  ∷  １ ∷ ０ ∷ １ ∷ １ ∷ ０ ∷ ０ ∷   -- s5 1  = s5   , write 1 , left
  []  
      

input-encode : List utmΣ
input-encode =  １  ∷ １  ∷ ０  ∷ ０  ∷  ０ ∷ []  

input+Copyδ : List utmΣ
input+Copyδ = ( $  ∷ ０  ∷ ０  ∷  ０ ∷  ０ ∷  * ∷  [] ) -- start state
        ++   Copyδ-encode
        ++ ( $ ∷ ^ ∷ input-encode )

short-input : List utmΣ
short-input = $  ∷ ０  ∷ ０  ∷  ０ ∷  * ∷
    ０  ∷ ０  ∷  ０ ∷  １  ∷ ０  ∷ １ ∷ １  ∷  * ∷
    ０  ∷ ０  ∷  １ ∷  ０  ∷ １  ∷ １ ∷ １  ∷  * ∷
    ０  ∷ １  ∷  B  ∷  １ ∷  ０  ∷ １ ∷ ０  ∷  * ∷
    １  ∷ ０  ∷  ０ ∷  ０ ∷  １  ∷ １ ∷ １  ∷  $ ∷
    ^   ∷ ０  ∷  ０ ∷  １  ∷ １ ∷ []  

utm-test1 : List  utmΣ → utmStates × ( List  utmΣ ) × ( List  utmΣ )
utm-test1 inp = Turing.taccept U-TM  inp

{-# TERMINATING #-}
utm-test2 : ℕ  → List  utmΣ  → utmStates × ( List  utmΣ ) × ( List  utmΣ )
utm-test2 n inp  = loop n (Turing.tstart U-TM) inp []
  where
        loop :  ℕ → utmStates → ( List  utmΣ ) → ( List  utmΣ ) → utmStates × ( List  utmΣ ) × ( List  utmΣ )
        loop zero q L R = ( q , L , R )
        loop (suc n) q L R with  move {utmStates} {utmΣ} {０} {utmδ} q L R | q
        ... | nq , nL , nR | reads = loop n nq nL nR
        ... | nq , nL , nR | _ = loop (suc n) nq nL nR

t1 = utm-test2 20 short-input 

t : (n : ℕ)  → utmStates × ( List  utmΣ ) × ( List  utmΣ )
-- t n = utm-test2 n input+Copyδ
t n = utm-test2 n short-input
