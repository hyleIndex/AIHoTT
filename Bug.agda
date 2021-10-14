{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat

data A : Type₁
f : ℕ → A → A

data A where
  s : A → A
  e : {k : ℕ} {n : A} → refl {x = f (suc zero) n} ≡ {!refl {x = s n}!}

f zero n = n
f (suc k) n = s (f k n)
