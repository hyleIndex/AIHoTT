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
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Order.Recursive using () renaming (_≤_ to _≤′_)
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; _⊎?_; inl; inr)

open import Cubical.Relation.Nullary

infixr 5 _∷_

data FMSet (A : Type) : Type where
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
fsuc (trunc xs ys p q i j) = isOfHLevel→isOfHLevelDep 2 (λ a xs ys p q → trunc xs ys p q) (fsuc xs) (fsuc ys) (cong fsuc p) (cong fsuc q) (trunc xs ys p q) i j

toNat : ℕ → Nat
toNat zero = fzero
toNat (suc x) = fsuc (toNat x)

toℕ : Nat → ℕ
toℕ [] = zero
toℕ (x ∷ xs) = suc (toℕ xs)
toℕ (comm x y xs i) = suc (suc (toℕ xs))
toℕ (trunc xs ys p q i j) = isOfHLevel→isOfHLevelDep 2 (λ _ → isSetℕ) (toℕ xs) (toℕ ys) (cong toℕ p) (cong toℕ q) (trunc xs ys p q) i j
