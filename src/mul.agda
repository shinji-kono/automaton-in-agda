{-# OPTIONS --cubical-compatible --safe #-}

module mul where

open import  Relation.Binary.PropositionalEquality

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

lemmm00 : ℕ
lemmm00 = suc (suc zero)

_+_ : ℕ → ℕ → ℕ
x + zero = x
x + (suc y) = suc (x + y)

_*_ : ℕ → ℕ → ℕ
x * zero  = zero
x * (suc y) = x + (x * y) 

lemmm01 : ℕ
lemmm01 = suc (suc zero) + suc (suc zero)

+-comm : ∀ x y → (x + y) ≡ (y + x)
+-comm zero zero = refl
+-comm zero (suc y) = cong suc (+-comm zero y)
+-comm (suc x) zero = cong suc (+-comm x zero)
+-comm (suc x) (suc y) = begin
   suc (suc x + y)   ≡⟨ cong suc (+-comm (suc x) y) ⟩
   suc (y + suc x)   ≡⟨ refl  ⟩
   suc (suc (y + x)) ≡⟨ cong suc (cong suc (+-comm y x )) ⟩
   suc (suc (x + y)) ≡⟨ refl ⟩
   suc (x + suc y)   ≡⟨ cong suc (+-comm x (suc y) ) ⟩
   suc (suc y + x)  ∎ where open ≡-Reasoning

+-assoc : ∀ x y z → (x + (y + z)) ≡ ((x + y) + z)
+-assoc x y zero = refl
+-assoc x y (suc z) = cong suc (+-assoc x y z)

*-distr-r : {x y z : ℕ } → (x * y) + (x * z) ≡ x * (y + z)
*-distr-r {x} {y} {zero} = refl
*-distr-r {x} {y} {suc z} = begin
    (x * y) + (x + (x * z)) ≡⟨ +-assoc (x * y) x _  ⟩
    ((x * y) + x) + (x * z) ≡⟨ cong (λ k → k + (x * z)) (+-comm (x * y) _ ) ⟩
    (x + (x * y) ) + (x * z) ≡⟨ sym (+-assoc x (x * y) _) ⟩
    (x + ((x * y) + (x * z))) ≡⟨ cong (λ k → x + k)(*-distr-r {x} {y} {z}) ⟩
     x + (x * (y + z)) ∎ where open ≡-Reasoning

*-distr-l : {x y z : ℕ } → (x * z) + (y * z) ≡ (x + y) * z 
*-distr-l {x} {y} {zero} = refl
*-distr-l {x} {y} {suc z} = begin
    (x + (x * z)) + (y + (y * z)) ≡⟨ +-assoc (x + (x * z)) y (y * z) ⟩
    ((x + (x * z)) + y) + (y * z) ≡⟨ cong (λ k → k + (y * z)) (sym (+-assoc x  (x * z) y)) ⟩
    (x + ((x * z) + y)) + (y * z) ≡⟨ cong (λ k → (x + k) + (y * z) ) (+-comm _ y) ⟩
    (x + (y + (x * z) )) + (y * z) ≡⟨ cong (λ k → k + (y * z)) (+-assoc x y (x * z)) ⟩
    ((x + y) + (x * z) ) + (y * z) ≡⟨ sym (+-assoc (x + y) (x * z) (y * z)) ⟩
    (x + y) + ((x * z)  + (y * z)) ≡⟨ cong (λ k → (x + y) + k) (*-distr-l {x} {y} {z}) ⟩
    (x + y) + ((x + y) * z) ∎ where open ≡-Reasoning

*-comm : ∀ x y → (x * y) ≡ (y * x)
*-comm zero zero = refl
*-comm zero (suc y) = trans (+-comm zero (zero * y)) (*-comm zero y)
*-comm (suc x) zero = trans (*-comm x zero) (+-comm (zero * x ) zero ) 
*-comm (suc x) (suc y) = lemma2  where
      lemma3 : (y : ℕ) → y ≡ (suc zero * y)
      lemma3 zero = refl
      lemma3 (suc y) = trans (cong suc (lemma3 y)) (+-comm _ (suc zero)) 
      lemma2 : (suc x * suc y) ≡ (suc y * suc x)
      lemma2 = begin
         (suc x * suc y) ≡⟨ sym ( *-distr-l {x} {suc zero} {suc y}) ⟩
         (x + (x * y)) + (suc zero + (suc zero * y)) ≡⟨ cong (λ k → (x + (x * y)) + k) (+-comm (suc zero) (suc zero * y)) ⟩
         (x + (x * y)) + suc (suc zero * y) ≡⟨ cong (λ k → (x + (x * y)) + k ) (cong suc (sym (lemma3 y))) ⟩
         (x + (x * y)) + suc y ≡⟨ refl ⟩
         (x * suc y) + suc y ≡⟨ +-comm _ (suc y) ⟩
         suc y + (x * suc y ) ≡⟨ cong (λ k → suc y + k) (*-comm x (suc y)) ⟩
         suc y + (suc y * x) ≡⟨ refl ⟩
         suc y * suc x ∎ where open ≡-Reasoning

*-assoc : ∀ x y z → (x * (y * z)) ≡ ((x * y) * z)
*-assoc x y zero = refl
*-assoc x y (suc z) = begin
    x * (y * suc z) ≡⟨ refl ⟩
    x * (y + (y * z)) ≡⟨ sym ( *-distr-r {x} {y} {y * z})  ⟩
    (x * y) + (x * (y * z)) ≡⟨ cong (λ k → (x * y) + k) (*-assoc x y z) ⟩
    (x * y) + ((x * y) * z) ∎ where open ≡-Reasoning



_∙_ : ℕ → ℕ → ℕ
zero ∙ zero  = zero
zero ∙ (suc y) = zero
(suc x) ∙ zero = zero
(suc x) ∙ (suc y) = suc (x + y) + (x ∙ y)

two = suc (suc zero)
five = suc (suc (suc (suc (suc zero))))

lemmm02 : two ∙ five ≡ five ∙ two
lemmm02 = refl

∙-comm : ∀ x y → (x ∙ y) ≡ (y ∙ x)
∙-comm zero zero = refl
∙-comm zero (suc y) = refl
∙-comm (suc x) zero = refl
∙-comm (suc x) (suc y) = begin
    (suc x) ∙ (suc y) ≡⟨ refl ⟩
    suc (x + y) + (x ∙ y) ≡⟨ cong₂ (λ j k → suc j + k) (+-comm x _) (∙-comm x y) ⟩
    suc (y + x) + (y ∙ x) ≡⟨ refl ⟩
    (suc y) ∙ (suc x) ∎ where open ≡-Reasoning

∙≡* : ∀ x y → (x ∙ y) ≡ (x * y)
∙≡* zero zero = refl
∙≡* (suc x) zero = refl
∙≡* zero (suc y) = trans (sym (*-comm zero y)) (+-comm _ zero)
∙≡* (suc x) (suc y) = begin
    (suc x) ∙ (suc y) ≡⟨ refl ⟩
    suc (x + y) + (x ∙ y) ≡⟨ cong (λ k → suc (x + y) + k ) (∙≡* x y) ⟩
    suc (x + y) + (x * y) ≡⟨ cong (λ k → k + (x * y)) ( begin
       suc (x + y) ≡⟨ cong suc (+-comm x y) ⟩
       suc (y + x) ≡⟨ refl ⟩
       y + suc x ≡⟨ +-comm y (suc x) ⟩
       suc x + y  ∎) ⟩
    (suc x + y) + (x * y) ≡⟨ sym (+-assoc (suc x) y (x * y)) ⟩
    suc x + (y + (x * y)) ≡⟨ cong (λ k → suc x + k) ( begin
       y + (x * y) ≡⟨ +-comm y (x * y) ⟩
       ((x * y) + y) ≡⟨ +-comm (x * y) y ⟩
       (y + (x * y) ) ≡⟨ cong (λ k → y + k) (*-comm x y) ⟩
       (y + (y * x) ) ≡⟨ refl ⟩
       (y * suc x) ≡⟨ *-comm y _ ⟩
       suc x * y ∎ ) ⟩
    (suc x) + ((suc x) * y)  ∎ where open ≡-Reasoning

∙≡*' : ∀ x y → (x ∙ y) ≡ (y * x)
∙≡*' x y = trans (∙≡* x y) (*-comm x y)

∙-distrl : ∀ x y z → (x ∙ (y + z)) ≡ (x ∙ y) + (x ∙ z)
∙-distrl x y z = begin
   x ∙ (y + z) ≡⟨ ∙≡* x (y + z) ⟩
   x * (y + z) ≡⟨ sym ( *-distr-r {x} {y} {z}) ⟩
   (x * y) + (x * z) ≡⟨ sym (cong₂ (λ j k → j + k) (∙≡* x y ) (∙≡* x z)) ⟩
   (x ∙ y) + (x ∙ z) ∎ where open ≡-Reasoning







