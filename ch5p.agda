module ch5p where

open import nat
open import vector

data _<'_ : ℕ -> ℕ -> Set where
  zs : ∀ {m} -> zero <' (suc m)
  ss : ∀ {n m} -> n <' m -> suc n <' suc m

data _≮'_ : ℕ -> ℕ -> Set where
  rz : ∀ {n} -> n ≮' zero
  ss : ∀ {n m} -> n ≮' m -> suc n ≮' suc m

data _<Lookup_ : ℕ -> ℕ -> Set where
  true : ∀ {x y} -> x <' y -> x <Lookup y
  false : ∀ {x y} -> x ≮' y -> x <Lookup y

_<?_ : (x y : ℕ) -> x <Lookup y
_ <? zero = false rz
zero <? suc y = true zs
suc x <? suc y with x <? y
suc x <? suc y | true p = true (ss p)
suc x <? suc y | false p = false (ss p)

nth𝕍' : ∀ {ℓ} {A : Set ℓ} {m} -> ∀ n -> (p : n <' m) -> 𝕍 A m -> A
nth𝕍' _ () []
nth𝕍' zero _ (x :: _) = x
nth𝕍' (suc n) (ss p) (_ :: xs) = nth𝕍' n p xs 
