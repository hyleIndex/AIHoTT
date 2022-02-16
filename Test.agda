{-# OPTIONS --cubical #-}

open import Agda.Builtin.Cubical.Path
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma



rp : {A : Set} → (A → ¬ A) → ((¬ A) → A) → ⊥
