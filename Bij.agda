{-# OPTIONS --cubical #-}

module Bij where

open import Agda.Builtin.Cubical.Path
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
ladd : ℕ → Bij → Bij
suc' : Bij → Bij

ladd zero n = n
ladd (suc k) n = suc' (ladd k n)

data Bij where
  zero : Bij
  suc : Bij → Bij
  swap : (n : Bij) → suc' (suc' n) ≡ suc' (suc' n)
  -- * * k * * n
  axiom : {k : ℕ} {n : Bij} → refl {x = ladd (suc zero) n} ≡ refl {x = suc' n}
  xchg : {k : ℕ} {n : Bij} →
         cong (ladd (suc (suc k))) (swap n) ∙ swap (ladd k (suc' (suc' n))) ≡
         swap (ladd k (suc' (suc' n))) ∙ cong (ladd (suc (suc k))) (swap n)
  gpd : {m n : ℕ} {p q : Bij-fromℕ m ≡ Bij-fromℕ n} (α β : p ≡ q) → α ≡ β

Bij-fromℕ zero = zero
Bij-fromℕ (suc n) = suc (Bij-fromℕ n)

suc' = suc

thm : 𝔹 ≡ Bij
thm = {!!}
