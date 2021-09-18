{-# OPTIONS --cubical #-}
module Diffint.Base where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Empty
open import Cubical.Data.Bool
open import Cubical.Data.Sum

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

open import Cubical.HITs.SetQuotients
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _*ℕ_)
open import Cubical.Data.Int renaming (ℤ to Int)


rel : (ℕ × ℕ) → (ℕ × ℕ) → Type₀
rel (a₀ , b₀) (a₁ , b₁) = x ≡ y
  where
    x = a₀ +ℕ b₁
    y = a₁ +ℕ b₀

ℤ = (ℕ × ℕ) / rel

_+ℕ'_ : (ℕ × ℕ) → (ℕ × ℕ) → (ℕ × ℕ)
(n₁ , n₂) +ℕ' (m₁ , m₂) = (n₁ +ℕ m₁ , n₂ +ℕ m₂)

+-assoc-6-1 : ∀ a b c d e f → c +ℕ f ≡ e +ℕ d → (a +ℕ c) +ℕ (b +ℕ f) ≡ (a +ℕ e) +ℕ (b +ℕ d)
+-assoc-6-1 a b c d e f p = {!!}
--  (a +ℕ c) +ℕ (b +ℕ f) ≡⟨ +-comm b f ⟩
--  (a +ℕ c) +ℕ (f +ℕ b) ≡⟨ +-assoc c f b ⟩
--  a +ℕ c +ℕ f +ℕ b     ≡⟨ +-assoc a c f⟩
--  a +ℕ (c +ℕ f) +ℕ b   ≡⟨ p ⟩
--  a +ℕ (e +ℕ d) +ℕ b   ≡⟨ +-assoc a e d ⟩
--  a +ℕ e +ℕ d +ℕ b     ≡⟨ +-assoc e d f ⟩
--  a +ℕ e +ℕ (d +ℕ b)   ≡⟨ +-comm d f ⟩
--  a +ℕ e +ℕ (b +ℕ d) ∎

+-assoc-6-2 : ∀ a b c d e f → a +ℕ d ≡ c +ℕ b → (a +ℕ e) +ℕ (d +ℕ f) ≡ (c +ℕ e) +ℕ (b +ℕ f)
+-assoc-6-2 a b c d e f p = {!!}
--  (a +ℕ e) +ℕ (d +ℕ f) ≡⟨ +-comm a e ⟩
--  (e +ℕ a) +ℕ (d +ℕ f) ≡⟨ +-assoc a d f ⟩
--  e +ℕ a +ℕ d +ℕ f     ≡⟨ +-assoc e a d⟩
--  e +ℕ (a +ℕ d) +ℕ f   ≡⟨ p ⟩
--  e +ℕ (c +ℕ b) +ℕ f   ≡⟨ +-assoc e c b ⟩
--  e +ℕ c +ℕ b +ℕ f     ≡⟨ +-assoc c b f ⟩
--  e +ℕ c +ℕ (b +ℕ f)   ≡⟨ +-comm e c ⟩
--  c +ℕ e +ℕ (b +ℕ f) ∎  
 
_+ℤ_ : ℤ → ℤ → ℤ
[ a ] +ℤ [ a₁ ] = [ a +ℕ' a₁ ]
[ a ] +ℤ eq/ a₁ b r i = eq/ (a +ℕ' a₁) (a +ℕ' b)
                            (+-assoc-6-1 (fst a) (snd a) (fst a₁) (snd a₁) (fst b) (snd b) r) i
[ a ] +ℤ squash/ c c₁ p q i i₁ = squash/ ( [ a ] +ℤ c) ([ a ] +ℤ c₁) {!!} {!!} i i₁
eq/ a b r i +ℤ [ a₁ ] = eq/ (a +ℕ' a₁) (b +ℕ' a₁)
                            (+-assoc-6-2 (fst a) (snd a) (fst b) (snd b) (fst a₁) (snd a₁) r) i
eq/ a b r i +ℤ eq/ a₁ b₁ r₁ i₁ = eq/ (a +ℕ' a₁) (b +ℕ' b₁) {!!} {!!}
eq/ a b r i +ℤ squash/ c c₁ p q i₁ i₂ = squash/ ([ a ] +ℤ c) ([ b ] +ℤ c₁) {!!} {!!} {!!} {!!}
squash/ a a₁ p q i i₁ +ℤ [ a₂ ] = squash/ (a +ℤ [ a₂ ]) (a₁ +ℤ [ a₂ ]) {!!} {!!} i i₁
squash/ a a₁ p q i i₁ +ℤ eq/ a₂ b r i₂ = squash/ (a +ℤ [ a₂ ]) (a₁ +ℤ [ b ]) {!!} {!!} {!!} {!!}
squash/ a a₁ p q i i₁ +ℤ squash/ c c₁ p₁ q₁ i₂ i₃ = squash/ (a +ℤ c) (a₁ +ℤ c₁) {!!} {!!} {!!} {!!}
