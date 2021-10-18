{-# OPTIONS --cubical #-}

module Sym where

open import Agda.Builtin.Cubical.Path
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.HITs.SetTruncation
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Sigma

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

-- postulate Fin<Dec : {n : ℕ} → (i j : Fin n) → Dec (i < j)

S : (n : ℕ) → Type₀
S n = Fin n ≃ Fin n

nf : ℕ → Type₀
nf zero    = Unit
nf (suc n) = Fin (suc n) × nf n

-- TODO: "remove" (f 0)-th element
residual : {n : ℕ} → S (suc n) → S n
residual f = {!!}

S→nf : (n : ℕ) → S n → nf n
S→nf zero f = tt
S→nf (suc n) f = fst f fzero , S→nf n (residual f)

-- send 0-th element to i
send : {n : ℕ} → (i : Fin n) → S n
send {n} i = isoToEquiv (iso (f n {!!}) {!!} {!!} {!!})
  where
  f : (n : ℕ) → (i : ℕ) → Fin n → Fin n
  f n zero j = j
  f zero (suc i) (zero , j<n) = {!!} -- impossible because of j<n
  f (suc n) (suc i) (zero , j<n) = zero , j<n
  f zero (suc i) (suc j , j<n) = {!!} -- impossible because of j<n
  f (suc n) (suc i) (suc j , j<n) = fsuc (f n i (j , pred-≤-pred j<n))

nf→S : (n : ℕ) → nf n → S n
nf→S n = {!!}

-- S≃nf : (n : ℕ) → ∥ S n ∥₀ ≃ nf n
-- S≃nf n = isoToEquiv (iso {!!} {!!} {!!} {!!})
  -- where
  -- ρ : (n : ℕ) → ∥ S n ∥₀ → nf n
  -- ρ zero f = tt
  -- ρ (suc n) ∣ f ∣₀ = coe f fzero , {!!}
  -- ρ (suc n) (squash₀ f f₁ p q i i₁) = {!!}
  -- σ : nf n → ∥ S n ∥₀
  -- σ = {!!}
