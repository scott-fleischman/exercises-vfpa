module ch4 where

open import level
open import bool
open import nat
open import eq
open import list

takeWhile : ∀ {l} {A : Set l} -> (A -> 𝔹) -> 𝕃 A -> 𝕃 A
takeWhile p [] = []
takeWhile p (x :: xs) with p x
takeWhile p (x :: xs) | tt = x :: takeWhile p xs
takeWhile p (x :: xs) | ff = []

proof1
  : ∀ {ℓ}
  -> {A : Set ℓ}
  -> (a : A)
  -> ∀ n
  -> (p : A -> 𝔹)
  -> p a ≡ tt
  -> takeWhile p (repeat n a) ≡ repeat n a
proof1 a zero p e = refl
proof1 a (suc n) p e with proof1 a n p e
proof1 a (suc n) p e | r rewrite e = cong (a ::_) r

take : ℕ -> ∀ {l} {A : Set l} -> 𝕃 A -> 𝕃 A
take zero _ = []
take (suc n) [] = []
take (suc n) (x :: xs) = x :: take n xs

proof2 :
  ∀ {ℓ}
  {A : Set ℓ}
  (xs : 𝕃 A)
  (n : ℕ)
  -> take n xs ++ nthTail n xs ≡ xs
proof2 _ zero = refl
proof2 [] (suc n) = refl
proof2 (x :: xs) (suc n) = cong (x ::_) (proof2 xs n)
