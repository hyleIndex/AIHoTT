{-# OPTIONS --cubical #-}

module Bij where

open import Agda.Builtin.Cubical.Path
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Fin

data 𝔹 : Type₁ where
  obj : (n : ℕ) → 𝔹
  path : {m n : ℕ} → (p : Fin m ≡ Fin n) → obj m ≡ obj n
  id𝔹 : {n : ℕ} → path (refl {x = Fin n}) ≡ refl
  comp𝔹 : {m n o : ℕ} (p : Fin m ≡ Fin n) (q : Fin n ≡ Fin o) → path (p ∙ q) ≡ path p ∙ path q
  gpd𝔹 : isGroupoid 𝔹

data Bij : Type₁
ladd : ℕ → Bij → Bij
suc' : Bij → Bij

ladd zero n = n
ladd (suc k) n = suc' (ladd k n)

data Bij where
  zero : Bij
  suc  : Bij → Bij
  swap : (n : Bij) → suc' (suc' n) ≡ suc' (suc' n)
  inv  : (n : Bij) → swap n ∙ swap n ≡ refl
  xchg : {k : ℕ} {n : Bij} →
         cong (ladd (suc (suc k))) (swap n) ∙ swap (ladd k (suc' (suc' n))) ≡
         swap (ladd k (suc' (suc' n))) ∙ cong (ladd (suc (suc k))) (swap n)
  yb   : {n : Bij} → swap (suc' n) ∙ cong suc' (swap n) ∙ swap (suc' n) ≡ cong suc' (swap n) ∙ swap (suc' n) ∙ cong suc' (swap n)
  gpd  : isGroupoid Bij

suc' = suc

Bij-fromℕ : ℕ → Bij
Bij-fromℕ zero = zero
Bij-fromℕ (suc n) = suc (Bij-fromℕ n)

Bij-toℕ : Bij → ℕ
Bij-toℕ zero = zero
Bij-toℕ (suc x) = suc (Bij-toℕ x)
Bij-toℕ (swap x i) = refl {x = (suc (suc (Bij-toℕ x)))} i
Bij-toℕ (inv x i i₁) = {!isSetℕ (suc (suc (Bij-toℕ x))) (suc (suc (Bij-toℕ x))) (refl) (refl) i i₁!}
Bij-toℕ (xchg {k = k} {n = n} i i₁) = {!suc (suc (Bij-toℕ (ladd k (suc' (suc' n)))))!}
Bij-toℕ (yb i i₁) = {!!}
Bij-toℕ (gpd x x₁ x₂ y x₃ y₁ i i₁ x₄) = {!!}

-- SM: I am really not sure about how we should proceed to prove this one which
-- should be needed to show that Bij ≃ Σ ℕ (λ n → Sym n)
-- Peixin : I think we might could proceed this by define a function from Bij to ℕ
-- then we can show Bij-to(Bij-from n) ≡ n
-- then we can prove this one. But I because of the normalization system is too bad
-- I am not able to define Bij-toℕ. Actually I believe that Bij-toℕ shoule all be refl
-- for the equality things.
end : (m n : ℕ) → Bij-fromℕ m ≡ Bij-fromℕ n → m ≡ n
end m n = {!!}
-- -- SM: I would like to do something like the following but this is currently not
-- -- supported by Agda
-- end m n p i with p i
-- ... | x = {!!}


-- suc𝔹 : 𝔹 → 𝔹
-- suc𝔹 (obj n) = obj (suc n)
-- suc𝔹 (path {m = m}{n = n} p i) = {!(cong (λ x → obj (suc x)) (Fin-inj m n p))!}
-- suc𝔹 (id𝔹 {n = n} i j) = obj (suc n)
-- suc𝔹 (comp𝔹 p q i j) = {!!}
-- suc𝔹 (gpd𝔹 x y p q α β i j k) = {!!}

-- fromBij : Bij → 𝔹
-- fromBij zero = obj zero
-- fromBij (suc x) = suc𝔹 (fromBij x)
-- fromBij (swap x i) = suc𝔹 (suc𝔹 (fromBij x))
-- fromBij (axiom {n = n} i j) = suc𝔹 (fromBij n)
-- fromBij (xchg i j) = {!!}
-- fromBij (gpd x y p q α β i j k) = {!!}

-- thm : 𝔹 ≡ Bij
-- thm = {!!}
