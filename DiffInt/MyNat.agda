{-# OPTIONS --without-K #-}

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

data ⊥ : Set where

¬_ : Set → Set
¬ P = P → ⊥

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : ¬ P → Dec P

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

ℕ-discrete : (m n : ℕ) → Dec (m ≡ n)
ℕ-discrete zero zero = yes refl
ℕ-discrete zero (suc n) = no (λ ())
ℕ-discrete (suc m) zero = no (λ ())
ℕ-discrete (suc m) (suc n) with ℕ-discrete m n
... | yes refl = yes refl
... | no p = no λ { refl → p refl }
