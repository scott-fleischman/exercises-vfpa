module ch1 where

open import bool
open import eq

ite-same' : ∀ {a} {A : Set a} → (b : 𝔹) (x : A) → (if b then x else x) ≡ x
ite-same' tt x = refl
ite-same' ff x = refl

&&-same : (b : _) → b && b ≡ b
&&-same tt = refl
&&-same ff = refl
