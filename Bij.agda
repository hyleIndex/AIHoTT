{-# OPTIONS --cubical #-}

module Bij where

open import Agda.Builtin.Cubical.Path
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Data.Nat
open import Cubical.Data.Fin

data 𝔹 : Type₁ where
  obj : (n : ℕ) → 𝔹
  path : {m n : ℕ} → (p : Fin m ≡ Fin n) → obj m ≡ obj n
  id𝔹 : {n : ℕ} → path (refl {x = Fin n}) ≡ refl
  comp𝔹 : {m n o : ℕ} (p : Fin m ≡ Fin n) (q : Fin n ≡ Fin o) → path (p ∙ q) ≡ path p ∙ path q
  gpd𝔹 : isGroupoid 𝔹

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
  inv  : (n : Bij) → swap n ∙ swap n ≡ refl
  xchg : {k : ℕ} {n : Bij} →
         cong (ladd (suc (suc k))) (swap n) ∙ swap (ladd k (suc' (suc' n))) ≡
         swap (ladd k (suc' (suc' n))) ∙ cong (ladd (suc (suc k))) (swap n)
  yb   : {n : Bij} → swap (suc' n) ∙ cong suc' (swap n) ∙ swap (suc' n) ≡ cong suc' (swap n) ∙ swap (suc' n) ∙ cong suc' (swap n)
  gpd : isGroupoid Bij

Bij-fromℕ zero = zero
Bij-fromℕ (suc n) = suc (Bij-fromℕ n)

suc' = suc

suc𝔹 : 𝔹 → 𝔹
suc𝔹 (obj n) = obj (suc n)
suc𝔹 (path {m = m}{n = n} p i) = {!(cong (λ x → obj (suc x)) (Fin-inj m n p))!}
suc𝔹 (id𝔹 {n = n} i j) = obj (suc n)
suc𝔹 (comp𝔹 p q i j) = {!!}
suc𝔹 (gpd𝔹 x y p q α β i j k) = {!!}

-- fromBij : Bij → 𝔹
-- fromBij zero = obj zero
-- fromBij (suc x) = suc𝔹 (fromBij x)
-- fromBij (swap x i) = suc𝔹 (suc𝔹 (fromBij x))
-- fromBij (axiom {n = n} i j) = suc𝔹 (fromBij n)
-- fromBij (xchg i j) = {!!}
-- fromBij (gpd x y p q α β i j k) = {!!}

thm : 𝔹 ≡ Bij
thm = {!!}
