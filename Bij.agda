{-# OPTIONS --cubical #-}

module Bij where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Data.Nat
open import Data.Fin

data 𝔹 : Type₁ where
  obj : (n : ℕ) → 𝔹
  path : {m n : ℕ} → (p : Fin m ≡ Fin n) → obj m ≡ obj n
  id𝔹 : {n : ℕ} → path (refl {x = Fin n}) ≡ refl
  comp𝔹 : {m n o : ℕ} (p : Fin m ≡ Fin n) (q : Fin n ≡ Fin o) → path (p ∙ q) ≡ path p ∙ path q
  gpd𝔹 : {m n : ℕ} {p q : obj m ≡ obj n} (α β : p ≡ q) → α ≡ β

data Bij : Type₁
Bij-fromℕ : ℕ → Bij

data Bij where
  zero : Bij
  suc : Bij → Bij
  swap : (n : Bij) → suc (suc n) ≡ suc (suc n)
  -- * * k * * n
  -- xchg : {n k : ℕ} → cong (λ m → 2 + k + m) (swap n) ∙ swap (k + 2 + n) ≡ swap (k + 2 + n) ∙ cong (λ m → 2 + k + m) (swap n)
  gpd : {m n : ℕ} {p q : Bij-fromℕ m ≡ Bij-fromℕ n} (α β : p ≡ q) → α ≡ β

Bij-fromℕ zero = zero
Bij-fromℕ (suc n) = suc (Bij-fromℕ n)

thm : 𝔹 ≡ Bij
thm = {!!}
