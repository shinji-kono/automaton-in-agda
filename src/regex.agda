module regex where

data Regex ( Σ : Set) : Set  where
  ε     : Regex Σ                -- empty
  φ     : Regex  Σ               -- fail
  _*    : Regex  Σ  → Regex  Σ 
  _&_   : Regex  Σ  → Regex  Σ → Regex Σ
  _||_  : Regex  Σ  → Regex  Σ → Regex Σ
  <_>   : Σ → Regex  Σ

infixr 40 _&_ _||_



