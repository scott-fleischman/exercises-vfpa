module ch5 where

open import bool
open import nat
open import eq
open import sum
open import vector

module braun-tree{ℓ} (A : Set ℓ) (_<A_ : A → A → 𝔹) where

  data braun-tree : (n : ℕ) → Set ℓ where
    bt-empty : braun-tree 0
    bt-node : ∀ {n m : ℕ} →
      A → braun-tree n → braun-tree m → 
      n ≡ m ∨ n ≡ suc m → 
      braun-tree (suc (n + m))
