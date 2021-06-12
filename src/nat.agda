{-# OPTIONS --allow-unsolved-metas #-}
module nat where

open import Data.Nat 
open import Data.Nat.Properties
open import Data.Empty
open import Relation.Nullary
open import  Relation.Binary.PropositionalEquality
open import  Relation.Binary.Core
open import  Relation.Binary.Definitions
open import  logic


nat-<> : { x y : ℕ } → x < y → y < x → ⊥
nat-<>  (s≤s x<y) (s≤s y<x) = nat-<> x<y y<x

nat-≤> : { x y : ℕ } → x ≤ y → y < x → ⊥
nat-≤>  (s≤s x<y) (s≤s y<x) = nat-≤> x<y y<x

nat-<≡ : { x : ℕ } → x < x → ⊥
nat-<≡  (s≤s lt) = nat-<≡ lt

nat-≡< : { x y : ℕ } → x ≡ y → x < y → ⊥
nat-≡< refl lt = nat-<≡ lt

¬a≤a : {la : ℕ} → suc la ≤ la → ⊥
¬a≤a  (s≤s lt) = ¬a≤a  lt

a<sa : {la : ℕ} → la < suc la 
a<sa {zero} = s≤s z≤n
a<sa {suc la} = s≤s a<sa 

=→¬< : {x : ℕ  } → ¬ ( x < x )
=→¬< {zero} ()
=→¬< {suc x} (s≤s lt) = =→¬< lt

>→¬< : {x y : ℕ  } → (x < y ) → ¬ ( y < x )
>→¬< (s≤s x<y) (s≤s y<x) = >→¬< x<y y<x

<-∨ : { x y : ℕ } → x < suc y → ( (x ≡ y ) ∨ (x < y) )
<-∨ {zero} {zero} (s≤s z≤n) = case1 refl
<-∨ {zero} {suc y} (s≤s lt) = case2 (s≤s z≤n)
<-∨ {suc x} {zero} (s≤s ())
<-∨ {suc x} {suc y} (s≤s lt) with <-∨ {x} {y} lt
<-∨ {suc x} {suc y} (s≤s lt) | case1 eq = case1 (cong (λ k → suc k ) eq)
<-∨ {suc x} {suc y} (s≤s lt) | case2 lt1 = case2 (s≤s lt1)

max : (x y : ℕ) → ℕ
max zero zero = zero
max zero (suc x) = (suc x)
max (suc x) zero = (suc x)
max (suc x) (suc y) = suc ( max x y )

-- _*_ : ℕ → ℕ → ℕ
-- _*_ zero _ = zero
-- _*_ (suc n) m = m + ( n * m )

-- x ^ y
exp : ℕ → ℕ → ℕ
exp _ zero = 1
exp n (suc m) = n * ( exp n m )

div2 : ℕ → (ℕ ∧ Bool )
div2 zero =  ⟪ 0 , false ⟫
div2 (suc zero) =  ⟪ 0 , true ⟫
div2 (suc (suc n)) =  ⟪ suc (proj1 (div2 n)) , proj2 (div2 n) ⟫ where
    open _∧_

div2-rev : (ℕ ∧ Bool ) → ℕ
div2-rev ⟪ x , true ⟫ = suc (x + x)
div2-rev ⟪ x , false ⟫ = x + x

div2-eq : (x : ℕ ) → div2-rev ( div2 x ) ≡ x
div2-eq zero = refl
div2-eq (suc zero) = refl
div2-eq (suc (suc x)) with div2 x | inspect div2 x 
... | ⟪ x1 , true ⟫ | record { eq = eq1 } = begin -- eq1 : div2 x ≡ ⟪ x1 , true ⟫
     div2-rev ⟪ suc x1 , true ⟫ ≡⟨⟩
     suc (suc (x1 + suc x1)) ≡⟨ cong (λ k → suc (suc k )) (+-comm x1  _ ) ⟩
     suc (suc (suc (x1 + x1))) ≡⟨⟩    
     suc (suc (div2-rev ⟪ x1 , true ⟫)) ≡⟨ cong (λ k → suc (suc (div2-rev k ))) (sym eq1) ⟩ 
     suc (suc (div2-rev (div2 x)))      ≡⟨ cong (λ k → suc (suc k)) (div2-eq x) ⟩ 
     suc (suc x) ∎  where open ≡-Reasoning
... | ⟪ x1 , false ⟫ | record { eq = eq1 } = begin
     div2-rev ⟪ suc x1 , false ⟫ ≡⟨⟩
     suc (x1 + suc x1) ≡⟨ cong (λ k → (suc k )) (+-comm x1  _ ) ⟩
     suc (suc (x1 + x1)) ≡⟨⟩    
     suc (suc (div2-rev ⟪ x1 , false ⟫)) ≡⟨ cong (λ k → suc (suc (div2-rev k ))) (sym eq1) ⟩ 
     suc (suc (div2-rev (div2 x)))      ≡⟨ cong (λ k → suc (suc k)) (div2-eq x) ⟩ 
     suc (suc x) ∎  where open ≡-Reasoning

minus : (a b : ℕ ) →  ℕ
minus a zero = a
minus zero (suc b) = zero
minus (suc a) (suc b) = minus a b

_-_ = minus

m+= : {i j  m : ℕ } → m + i ≡ m + j → i ≡ j
m+= {i} {j} {zero} refl = refl
m+= {i} {j} {suc m} eq = m+= {i} {j} {m} ( cong (λ k → pred k ) eq )

+m= : {i j  m : ℕ } → i + m ≡ j + m → i ≡ j
+m= {i} {j} {m} eq = m+= ( subst₂ (λ j k → j ≡ k ) (+-comm i _ ) (+-comm j _ ) eq )

less-1 :  { n m : ℕ } → suc n < m → n < m
less-1 {zero} {suc (suc _)} (s≤s (s≤s z≤n)) = s≤s z≤n
less-1 {suc n} {suc m} (s≤s lt) = s≤s (less-1 {n} {m} lt)

sa=b→a<b :  { n m : ℕ } → suc n ≡ m → n < m
sa=b→a<b {0} {suc zero} refl = s≤s z≤n
sa=b→a<b {suc n} {suc (suc n)} refl = s≤s (sa=b→a<b refl)

minus+n : {x y : ℕ } → suc x > y  → minus x y + y ≡ x
minus+n {x} {zero} _ = trans (sym (+-comm zero  _ )) refl
minus+n {zero} {suc y} (s≤s ())
minus+n {suc x} {suc y} (s≤s lt) = begin
           minus (suc x) (suc y) + suc y
        ≡⟨ +-comm _ (suc y)    ⟩
           suc y + minus x y 
        ≡⟨ cong ( λ k → suc k ) (
           begin
                 y + minus x y 
              ≡⟨ +-comm y  _ ⟩
                 minus x y + y
              ≡⟨ minus+n {x} {y} lt ⟩
                 x 
           ∎  
           ) ⟩
           suc x
        ∎  where open ≡-Reasoning

0<s : {x : ℕ } → zero < suc x
0<s {_} = s≤s z≤n 

<-minus-0 : {x y z : ℕ } → z + x < z + y → x < y
<-minus-0 {x} {suc _} {zero} lt = lt
<-minus-0 {x} {y} {suc z} (s≤s lt) = <-minus-0 {x} {y} {z} lt

<-minus : {x y z : ℕ } → x + z < y + z → x < y
<-minus {x} {y} {z} lt = <-minus-0 ( subst₂ ( λ j k → j < k ) (+-comm x _) (+-comm y _ ) lt )

x≤x+y : {z y : ℕ } → z ≤ z + y
x≤x+y {zero} {y} = z≤n
x≤x+y {suc z} {y} = s≤s  (x≤x+y {z} {y})

<-plus : {x y z : ℕ } → x < y → x + z < y + z 
<-plus {zero} {suc y} {z} (s≤s z≤n) = s≤s (subst (λ k → z ≤ k ) (+-comm z _ ) x≤x+y  )
<-plus {suc x} {suc y} {z} (s≤s lt) = s≤s (<-plus {x} {y} {z} lt)

<-plus-0 : {x y z : ℕ } → x < y → z + x < z + y 
<-plus-0 {x} {y} {z} lt = subst₂ (λ j k → j < k ) (+-comm _ z) (+-comm _ z) ( <-plus {x} {y} {z} lt )

≤-plus : {x y z : ℕ } → x ≤ y → x + z ≤ y + z
≤-plus {0} {y} {zero} z≤n = z≤n
≤-plus {0} {y} {suc z} z≤n = subst (λ k → z < k ) (+-comm _ y ) x≤x+y 
≤-plus {suc x} {suc y} {z} (s≤s lt) = s≤s ( ≤-plus {x} {y} {z} lt )

≤-plus-0 : {x y z : ℕ } → x ≤ y → z + x ≤ z + y 
≤-plus-0 {x} {y} {zero} lt = lt
≤-plus-0 {x} {y} {suc z} lt = s≤s ( ≤-plus-0 {x} {y} {z} lt )

x+y<z→x<z : {x y z : ℕ } → x + y < z → x < z 
x+y<z→x<z {zero} {y} {suc z} (s≤s lt1) = s≤s z≤n
x+y<z→x<z {suc x} {y} {suc z} (s≤s lt1) = s≤s ( x+y<z→x<z {x} {y} {z} lt1 )

*≤ : {x y z : ℕ } → x ≤ y → x * z ≤ y * z 
*≤ lt = *-mono-≤ lt ≤-refl

*< : {x y z : ℕ } → x < y → x * suc z < y * suc z 
*< {zero} {suc y} lt = s≤s z≤n
*< {suc x} {suc y} (s≤s lt) = <-plus-0 (*< lt)

<to<s : {x y  : ℕ } → x < y → x < suc y
<to<s {zero} {suc y} (s≤s lt) = s≤s z≤n
<to<s {suc x} {suc y} (s≤s lt) = s≤s (<to<s {x} {y} lt)

<tos<s : {x y  : ℕ } → x < y → suc x < suc y
<tos<s {zero} {suc y} (s≤s z≤n) = s≤s (s≤s z≤n)
<tos<s {suc x} {suc y} (s≤s lt) = s≤s (<tos<s {x} {y} lt)

≤to< : {x y  : ℕ } → x < y → x ≤ y 
≤to< {zero} {suc y} (s≤s z≤n) = z≤n
≤to< {suc x} {suc y} (s≤s lt) = s≤s (≤to< {x} {y}  lt)

refl-≤s : {x : ℕ } → x ≤ suc x
refl-≤s {zero} = z≤n
refl-≤s {suc x} = s≤s (refl-≤s {x})

x<y→≤ : {x y : ℕ } → x < y →  x ≤ suc y
x<y→≤ {zero} {.(suc _)} (s≤s z≤n) = z≤n
x<y→≤ {suc x} {suc y} (s≤s lt) = s≤s (x<y→≤ {x} {y} lt)

open import Data.Product

minus<=0 : {x y : ℕ } → x ≤ y → minus x y ≡ 0
minus<=0 {0} {zero} z≤n = refl
minus<=0 {0} {suc y} z≤n = refl
minus<=0 {suc x} {suc y} (s≤s le) = minus<=0 {x} {y} le

minus>0 : {x y : ℕ } → x < y → 0 < minus y x 
minus>0 {zero} {suc _} (s≤s z≤n) = s≤s z≤n
minus>0 {suc x} {suc y} (s≤s lt) = minus>0 {x} {y} lt

open import Relation.Binary.Definitions

distr-minus-* : {x y z : ℕ } → (minus x y) * z ≡ minus (x * z) (y * z) 
distr-minus-* {x} {zero} {z} = refl
distr-minus-* {x} {suc y} {z} with <-cmp x y
distr-minus-* {x} {suc y} {z} | tri< a ¬b ¬c = begin
          minus x (suc y) * z
        ≡⟨ cong (λ k → k * z ) (minus<=0 {x} {suc y} (x<y→≤ a)) ⟩
           0 * z 
        ≡⟨ sym (minus<=0 {x * z} {z + y * z} le ) ⟩
          minus (x * z) (z + y * z) 
        ∎  where
            open ≡-Reasoning
            le : x * z ≤ z + y * z
            le  = ≤-trans lemma (subst (λ k → y * z ≤ k ) (+-comm _ z ) (x≤x+y {y * z} {z} ) ) where
               lemma : x * z ≤ y * z
               lemma = *≤ {x} {y} {z} (≤to< a)
distr-minus-* {x} {suc y} {z} | tri≈ ¬a refl ¬c = begin
          minus x (suc y) * z
        ≡⟨ cong (λ k → k * z ) (minus<=0 {x} {suc y} refl-≤s ) ⟩
           0 * z 
        ≡⟨ sym (minus<=0 {x * z} {z + y * z} (lt {x} {z} )) ⟩
          minus (x * z) (z + y * z) 
        ∎  where
            open ≡-Reasoning
            lt : {x z : ℕ } →  x * z ≤ z + x * z
            lt {zero} {zero} = z≤n
            lt {suc x} {zero} = lt {x} {zero}
            lt {x} {suc z} = ≤-trans lemma refl-≤s where
               lemma : x * suc z ≤   z + x * suc z
               lemma = subst (λ k → x * suc z ≤ k ) (+-comm _ z) (x≤x+y {x * suc z} {z}) 
distr-minus-* {x} {suc y} {z} | tri> ¬a ¬b c = +m= {_} {_} {suc y * z} ( begin
           minus x (suc y) * z + suc y * z
        ≡⟨ sym (proj₂ *-distrib-+ z  (minus x (suc y) )  _) ⟩
           ( minus x (suc y) + suc y ) * z
        ≡⟨ cong (λ k → k * z) (minus+n {x} {suc y} (s≤s c))  ⟩
           x * z 
        ≡⟨ sym (minus+n {x * z} {suc y * z} (s≤s (lt c))) ⟩
           minus (x * z) (suc y * z) + suc y * z
        ∎ ) where
            open ≡-Reasoning
            lt : {x y z : ℕ } → suc y ≤ x → z + y * z ≤ x * z
            lt {x} {y} {z} le = *≤ le 

minus- : {x y z : ℕ } → suc x > z + y → minus (minus x y) z ≡ minus x (y + z)
minus- {x} {y} {z} gt = +m= {_} {_} {z} ( begin
           minus (minus x y) z + z
        ≡⟨ minus+n {_} {z} lemma ⟩
           minus x y
        ≡⟨ +m= {_} {_} {y} ( begin
              minus x y + y 
           ≡⟨ minus+n {_} {y} lemma1 ⟩
              x
           ≡⟨ sym ( minus+n {_} {z + y} gt ) ⟩
              minus x (z + y) + (z + y)
           ≡⟨ sym ( +-assoc (minus x (z + y)) _  _ ) ⟩
              minus x (z + y) + z + y
           ∎ ) ⟩
           minus x (z + y) + z
        ≡⟨ cong (λ k → minus x k + z ) (+-comm _ y )  ⟩
           minus x (y + z) + z
        ∎  ) where
             open ≡-Reasoning
             lemma1 : suc x > y
             lemma1 = x+y<z→x<z (subst (λ k → k < suc x ) (+-comm z _ ) gt )
             lemma : suc (minus x y) > z
             lemma = <-minus {_} {_} {y} ( subst ( λ x → z + y < suc x ) (sym (minus+n {x} {y}  lemma1 ))  gt )

minus-* : {M k n : ℕ } → n < k  → minus k (suc n) * M ≡ minus (minus k n * M ) M
minus-* {zero} {k} {n} lt = begin
           minus k (suc n) * zero
        ≡⟨ *-comm (minus k (suc n)) zero ⟩
           zero * minus k (suc n) 
        ≡⟨⟩
           0 * minus k n 
        ≡⟨ *-comm 0 (minus k n) ⟩
           minus (minus k n * 0 ) 0
        ∎  where
        open ≡-Reasoning
minus-* {suc m} {k} {n} lt with <-cmp k 1
minus-* {suc m} {.0} {zero} lt | tri< (s≤s z≤n) ¬b ¬c = refl
minus-* {suc m} {.0} {suc n} lt | tri< (s≤s z≤n) ¬b ¬c = refl
minus-* {suc zero} {.1} {zero} lt | tri≈ ¬a refl ¬c = refl
minus-* {suc (suc m)} {.1} {zero} lt | tri≈ ¬a refl ¬c = minus-* {suc m} {1} {zero} lt 
minus-* {suc m} {.1} {suc n} (s≤s ()) | tri≈ ¬a refl ¬c
minus-* {suc m} {k} {n} lt | tri> ¬a ¬b c = begin
           minus k (suc n) * M
        ≡⟨ distr-minus-* {k} {suc n} {M}  ⟩
           minus (k * M ) ((suc n) * M)
        ≡⟨⟩
           minus (k * M ) (M + n * M  )
        ≡⟨ cong (λ x → minus (k * M) x) (+-comm M _ ) ⟩
           minus (k * M ) ((n * M) + M )
        ≡⟨ sym ( minus- {k * M} {n * M} (lemma lt) ) ⟩
           minus (minus (k * M ) (n * M)) M
        ≡⟨ cong (λ x → minus x M ) ( sym ( distr-minus-* {k} {n} )) ⟩
           minus (minus k n * M ) M
        ∎  where
             M = suc m
             lemma : {n k m : ℕ } → n < k  → suc (k * suc m) > suc m + n * suc m
             lemma {zero} {suc k} {m} (s≤s lt) = s≤s (s≤s (subst (λ x → x ≤ m + k * suc m) (+-comm 0 _ ) x≤x+y ))
             lemma {suc n} {suc k} {m} lt = begin
                         suc (suc m + suc n * suc m) 
                      ≡⟨⟩
                         suc ( suc (suc n) * suc m)
                      ≤⟨ ≤-plus-0 {_} {_} {1} (*≤ lt ) ⟩
                         suc (suc k * suc m)
                      ∎   where open ≤-Reasoning
             open ≡-Reasoning
