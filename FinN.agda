{-# OPTIONS --cubical #-}
module FinN where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
import Cubical.Data.Empty as ⊥
import Cubical.Data.Unit as Unit
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; _⊎?_; inl; inr)

open import Cubical.Relation.Nullary

infixr 5 _∷_

data FMSet (A : Type₀) : Type₀ where
  [] : FMSet A
  _∷_ : (x : A) → (xs : FMSet A) → FMSet A
  comm : (x y : A) (xs : FMSet A) → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
  trunc : (xs ys : FMSet A) (p q : xs ≡ ys) → p ≡ q

Nat = FMSet Unit.Unit

Nat-isSet : isSet Nat
Nat-isSet = λ x y p q → trunc x y p q

fzero : Nat
fzero = []

fsuc : Nat → Nat
fsuc [] = Unit.tt ∷ []
fsuc (x ∷ xs) = Unit.tt ∷ (x ∷ xs)
fsuc (comm x y xs i) = cong (λ ys → Unit.tt ∷ ys) (comm x y xs) i
fsuc (trunc xs ys p q i j) = trunc (fsuc xs) (fsuc ys) (cong fsuc p) (cong fsuc q) i j

fromℕ : ℕ → Nat
fromℕ zero = fzero
fromℕ (suc x) = fsuc (fromℕ x)

toℕ : Nat → ℕ
toℕ [] = zero
toℕ (x ∷ xs) = suc (toℕ xs)
toℕ (comm x y xs i) = suc (suc (toℕ xs))
toℕ (trunc xs ys p q i j) = isSetℕ (toℕ xs) (toℕ ys) (cong toℕ p) (cong toℕ q) i j

-- i = i0 ⊢ toℕ-fsuc (p j) k
-- i = i1 ⊢ toℕ-fsuc (q j) k
-- j = i0 ⊢ toℕ-fsuc xs k
-- j = i1 ⊢ toℕ-fsuc ys k
-- k = i0 ⊢ isSetℕ (toℕ (fsuc xs)) (toℕ (fsuc ys))
--          (λ i₁ → toℕ (fsuc (p i₁))) (λ i₁ → toℕ (fsuc (q i₁))) i j
-- k = i1 ⊢ suc
--         (isSetℕ (toℕ xs) (toℕ ys) (λ i₁ → toℕ (p i₁)) (λ i₁ → toℕ (q i₁)) i
--          j)

toℕ-fsuc : (n : Nat) → toℕ (fsuc n) ≡ suc (toℕ n)
toℕ-fsuc [] = refl
toℕ-fsuc (x ∷ n) = refl
toℕ-fsuc (comm x y n i) = refl
toℕ-fsuc (trunc xs ys p q i j) k = {!!} -- isSetℕ (toℕ-fsuc xs k) (toℕ-fsuc ys k) (cong (λ zs → toℕ-fsuc zs k) p) (cong (λ zs → toℕ-fsuc zs k) q) i j

to-fromℕ : (n : ℕ) → toℕ (fromℕ n) ≡ n
to-fromℕ zero = refl
to-fromℕ (suc n) = toℕ-fsuc (fromℕ n) ∙ cong suc (to-fromℕ n)
