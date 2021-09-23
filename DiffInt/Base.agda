{-# OPTIONS --cubical #-}
module DiffInt.Base where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.HITs.SetQuotients
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.Data.Nat as ℕ renaming (_+_ to _+ℕ_ ; _·_ to _*ℕ_)
open import Cubical.Data.Int renaming (ℤ to Int)


rel : (ℕ × ℕ) → (ℕ × ℕ) → Type₀
rel (a₀ , b₀) (a₁ , b₁) = x ≡ y
  where
    x = a₀ +ℕ b₁
    y = a₁ +ℕ b₀

ℤ = (ℕ × ℕ) / rel

ℤ-isSet : isSet ℤ
ℤ-isSet m n p q = squash/ m n p q

ℤ-isGroupoid : isGroupoid ℤ
ℤ-isGroupoid = isSet→isGroupoid ℤ-isSet

_+ℕ'_ : (ℕ × ℕ) → (ℕ × ℕ) → (ℕ × ℕ)
(n₁ , n₂) +ℕ' (m₁ , m₂) = (n₁ +ℕ m₁ , n₂ +ℕ m₂)

+-assoc-3-1 : ∀ x y z → rel y z → rel (x +ℕ' y) (x +ℕ' z)
+-assoc-3-1 x y z  p =
  (fst x +ℕ fst y) +ℕ (snd x +ℕ snd z) ≡⟨ cong (λ x' → (fst x +ℕ fst y) +ℕ x') (ℕ.+-comm (snd x) (snd z)) ⟩
  (fst x +ℕ fst y) +ℕ (snd z +ℕ snd x) ≡⟨ ℕ.+-assoc (fst x +ℕ fst y) (snd z) (snd x) ⟩
  fst x +ℕ fst y +ℕ snd z +ℕ snd x     ≡⟨ cong (λ x' → x' +ℕ snd x) (sym (ℕ.+-assoc (fst x) (fst y) (snd z))) ⟩
  fst x +ℕ (fst y +ℕ snd z) +ℕ snd x   ≡⟨ cong (λ x' → fst x +ℕ x' +ℕ snd x) p ⟩
  fst x +ℕ (fst z +ℕ snd y) +ℕ snd x   ≡⟨ cong (λ x' → x' +ℕ snd x) (ℕ.+-assoc (fst x) (fst z) (snd y)) ⟩
  fst x +ℕ fst z +ℕ snd y +ℕ snd x     ≡⟨ sym (ℕ.+-assoc (fst x +ℕ fst z) (snd y) (snd x)) ⟩
  fst x +ℕ fst z +ℕ (snd y +ℕ snd x)   ≡⟨ cong (λ x' → fst x +ℕ fst z +ℕ x') (ℕ.+-comm (snd y) (snd x)) ⟩
  fst x +ℕ fst z +ℕ (snd x +ℕ snd y) ∎

+-assoc-3-2 : ∀ x y z → rel x y → rel (x +ℕ' z) (y +ℕ' z)
+-assoc-3-2 x y z p =
  (fst x +ℕ fst z) +ℕ (snd y +ℕ snd z) ≡⟨ cong (λ x' → x' +ℕ (snd y +ℕ snd z)) (ℕ.+-comm (fst x) (fst z)) ⟩
  (fst z +ℕ fst x) +ℕ (snd y +ℕ snd z) ≡⟨ ℕ.+-assoc (fst z +ℕ fst x) (snd y) (snd z) ⟩
  fst z +ℕ fst x +ℕ snd y +ℕ snd z     ≡⟨ cong (λ x' → x' +ℕ snd z) (sym (ℕ.+-assoc (fst z) (fst x) (snd y))) ⟩
  fst z +ℕ (fst x +ℕ snd y) +ℕ snd z   ≡⟨ cong (λ x' → fst z +ℕ x' +ℕ snd z) p ⟩
  fst z +ℕ (fst y +ℕ snd x) +ℕ snd z   ≡⟨ cong (λ x' → x' +ℕ snd z) (ℕ.+-assoc (fst z) (fst y) (snd x)) ⟩
  fst z +ℕ fst y +ℕ snd x +ℕ snd z     ≡⟨ sym (ℕ.+-assoc (fst z +ℕ fst y) (snd x) (snd z)) ⟩
  fst z +ℕ fst y +ℕ (snd x +ℕ snd z)   ≡⟨ cong (λ x' → x' +ℕ (snd x +ℕ snd z)) (ℕ.+-comm (fst z) (fst y)) ⟩
  fst y +ℕ fst z +ℕ (snd x +ℕ snd z) ∎

_+ℤ_ : ℤ → ℤ → ℤ
[ x ] +ℤ [ y ] = [ x +ℕ' y ]

[ x ] +ℤ eq/ y₁ y₂ r j = eq/ (x +ℕ' y₁) (x +ℕ' y₂) (+-assoc-3-1 x y₁ y₂ r) j

[ x ] +ℤ squash/ y₁ y₂ p q j j₁ = squash/ ([ x ] +ℤ y₁) ([ x ] +ℤ y₂) ((cong (λ y → [ x ] +ℤ y)) p) ((cong (λ y → [ x ] +ℤ y)) q) j j₁

eq/ x₁ x₂ r i +ℤ [ y ] = eq/ (x₁ +ℕ' y) (x₂ +ℕ' y) (+-assoc-3-2 x₁ x₂ y r) i

-- i = i0 ⊢ eq/ (x₁ +ℕ' y₁) (x₁ +ℕ' y₂) (+-assoc-3-1 x₁ y₁ y₂ r₁) j
-- i = i1 ⊢ eq/ (x₂ +ℕ' y₁) (x₂ +ℕ' y₂) (+-assoc-3-1 x₂ y₁ y₂ r₁) j
-- j = i0 ⊢ eq/ (x₁ +ℕ' y₁) (x₂ +ℕ' y₁) (+-assoc-3-2 x₁ x₂ y₁ r) i
-- j = i1 ⊢ eq/ (x₁ +ℕ' y₂) (x₂ +ℕ' y₂) (+-assoc-3-2 x₁ x₂ y₂ r) i

eq/ x₁ x₂ r i +ℤ eq/ y₁ y₂ r₁ j = isSet→isSet' ℤ-isSet
                                  (eq/ (x₁ +ℕ' y₁) (x₁ +ℕ' y₂) (+-assoc-3-1 x₁ y₁ y₂ r₁))
                                  (eq/ (x₂ +ℕ' y₁) (x₂ +ℕ' y₂) (+-assoc-3-1 x₂ y₁ y₂ r₁))
                                  (eq/ (x₁ +ℕ' y₁) (x₂ +ℕ' y₁) (+-assoc-3-2 x₁ x₂ y₁ r))
                                  (eq/ (x₁ +ℕ' y₂) (x₂ +ℕ' y₂) (+-assoc-3-2 x₁ x₂ y₂ r))
                                 i j

-- i = i0 ⊢ squash/ ([ x₁ ] +ℤ y₁) ([ x₁ ] +ℤ y₂)
--          (λ i₁ → [ x₁ ] +ℤ p i₁) (λ i₁ → [ x₁ ] +ℤ q i₁) j₁ j₂
-- i = i1 ⊢ squash/ ([ x₂ ] +ℤ y₁) ([ x₂ ] +ℤ y₂)
--          (λ i₁ → [ x₂ ] +ℤ p i₁) (λ i₁ → [ x₂ ] +ℤ q i₁) j₁ j₂
-- j₁ = i0 ⊢ eq/ x₁ x₂ r i +ℤ p j₂
-- j₁ = i1 ⊢ eq/ x₁ x₂ r i +ℤ q j₂
-- j₂ = i0 ⊢ eq/ x₁ x₂ r i +ℤ y₁
-- j₂ = i1 ⊢ eq/ x₁ x₂ r i +ℤ y₂

eq/ x₁ x₂ r i +ℤ squash/ y₁ y₂ p q j₁ j₂ = isGroupoid→isGroupoid' ℤ-isGroupoid
                                           (squash/ ([ x₁ ] +ℤ y₁) ([ x₁ ] +ℤ y₂) (λ i₁ → [ x₁ ] +ℤ p i₁) (λ i₁ → [ x₁ ] +ℤ q i₁))
                                           (squash/ ([ x₂ ] +ℤ y₁) ([ x₂ ] +ℤ y₂) (λ i₁ → [ x₂ ] +ℤ p i₁) (λ i₁ → [ x₂ ] +ℤ q i₁))
                                           (λ k₁ k₂ → (eq/ x₁ x₂ r k₁) +ℤ p k₂)
                                           (λ k₁ k₂ → eq/ x₁ x₂ r k₁ +ℤ q k₂)
                                           (λ k₁ k₂ → eq/ x₁ x₂ r k₁ +ℤ y₁)
                                           (λ k₁ k₂ → eq/ x₁ x₂ r k₁ +ℤ y₂)
                                         i j₁ j₂

squash/ x₁ x₂ p q i i₁ +ℤ [ y ] = squash/ (x₁ +ℤ [ y ]) (x₂ +ℤ [ y ]) ((cong (λ x → x +ℤ [ y ])) p) ((cong (λ x → x +ℤ [ y ])) q) i i₁

-- i = i0 ⊢ p i₁ +ℤ eq/ y₁ y₂ r j
-- i = i1 ⊢ q i₁ +ℤ eq/ y₁ y₂ r j
-- i₁ = i0 ⊢ x₁ +ℤ eq/ y₁ y₂ r j
-- i₁ = i1 ⊢ x₂ +ℤ eq/ y₁ y₂ r j
-- j = i0 ⊢ squash/ (x₁ +ℤ [ y₁ ]) (x₂ +ℤ [ y₁ ])
--          (λ i₂ → p i₂ +ℤ [ y₁ ]) (λ i₂ → q i₂ +ℤ [ y₁ ]) i i₁
-- j = i1 ⊢ squash/ (x₁ +ℤ [ y₂ ]) (x₂ +ℤ [ y₂ ])
--          (λ i₂ → p i₂ +ℤ [ y₂ ]) (λ i₂ → q i₂ +ℤ [ y₂ ]) i i₁

squash/ x₁ x₂ p q i i₁ +ℤ eq/ y₁ y₂ r j = isGroupoid→isGroupoid' ℤ-isGroupoid
                                          (λ k₁ k₂ → p k₁ +ℤ eq/ y₁ y₂ r k₂) (λ k₁ k₂ → {!q k₁ +ℤ eq/ y₁ y₂ r k₂!}) {!!} {!!} {!!} {!!} {!!} {!!} {!!}

squash/ x₁ x₂ p q i i₁ +ℤ squash/ y₁ y₂ p₁ q₁ j₁ j₂ = {!!}


-ℤ'_  : ℤ → ℤ
-ℤ' [ a ] = [ snd a , fst a ]
-ℤ' eq/ a b r i = eq/ (snd a , fst a) (snd b , fst b) (tmp a b r) i
                                                      where
                                                        tmp : ∀ a b → fst a +ℕ snd b ≡ fst b +ℕ snd a → snd a +ℕ fst b ≡ snd b +ℕ fst a
                                                        tmp a b r =
                                                          snd a +ℕ fst b ≡⟨ ℕ.+-comm (snd a) (fst b) ⟩
                                                          fst b +ℕ snd a ≡⟨ sym r ⟩
                                                          fst a +ℕ snd b ≡⟨ ℕ.+-comm (fst a) (snd b) ⟩
                                                          snd b +ℕ fst a ∎
-ℤ' squash/ a a₁ p q i i₁ = squash/ (-ℤ' a) (-ℤ' a₁) (cong (λ x → -ℤ' x) p) (cong (λ x → -ℤ' x) q) i i₁

_-ℤ_ : ℤ → ℤ → ℤ
a -ℤ b = a +ℤ (-ℤ' b)
