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
[ a ] +ℤ [ a₁ ] = [ a +ℕ' a₁ ]

[ a ] +ℤ eq/ a₁ b r i = eq/ (a +ℕ' a₁) (a +ℕ' b) (+-assoc-3-1 a a₁ b r) i
                            
[ a ] +ℤ squash/ c c₁ p q i i₁ = squash/ ( [ a ] +ℤ c) ([ a ] +ℤ c₁) (cong (λ x → [ a ] +ℤ x) (p)) (cong (λ x → [ a ] +ℤ x) (q)) i i₁

eq/ a b r i +ℤ [ a₁ ] = eq/ (a +ℕ' a₁) (b +ℕ' a₁)
                            (+-assoc-3-2 a b a₁ r) i

eq/ a b r i +ℤ eq/ a₁ b₁ r₁ i₁ = isSet→isSet' ℤ-isSet (eq/ (a +ℕ' a₁) (a +ℕ' b₁) (+-assoc-3-1 a a₁ b₁ r₁))
                                                     (eq/ (b +ℕ' a₁) (b +ℕ' b₁) (+-assoc-3-1 b a₁ b₁ r₁))
                                                     (eq/ (a +ℕ' a₁) (b +ℕ' a₁) (+-assoc-3-2 a b a₁ r))
                                                     (eq/ (a +ℕ' b₁) (b +ℕ' b₁) (+-assoc-3-2 a b b₁ r))
                                                     i i₁
-- i = i0 ⊢ squash/ ([ a ] +ℤ c) ([ a ] +ℤ c₁) (λ i₃ → [ a ] +ℤ p i₃)
--          (λ i₃ → [ a ] +ℤ q i₃) i₁ i₂
-- i = i1 ⊢ squash/ ([ b ] +ℤ c) ([ b ] +ℤ c₁) (λ i₃ → [ b ] +ℤ p i₃)
--          (λ i₃ → [ b ] +ℤ q i₃) i₁ i₂
-- i₁ = i0 ⊢ eq/ a b r i +ℤ p i₂
-- i₁ = i1 ⊢ eq/ a b r i +ℤ q i₂
-- i₂ = i0 ⊢ eq/ a b r i +ℤ c
-- i₂ = i1 ⊢ eq/ a b r i +ℤ c₁

-- ?0
--   : Square (λ i₃ → [ a ] +ℤ p i₃) (λ i₃ → [ b ] +ℤ p i₃) ([ a ] +ℤ c) ≡ ([ b ] +ℤ c)
--     ([ a ] +ℤ c₁) ≡ ([ b ] +ℤ c₁)
-- ?1
--   : Square (λ i₃ → [ a ] +ℤ q i₃) (λ i₃ → [ b ] +ℤ q i₃) ([ a ] +ℤ c) ≡ ([ b ] +ℤ c)
--    ([ a ] +ℤ c₁) ≡ ([ b ] +ℤ c₁)
-- ?2
--   : Square (λ i₃ → [ a ] +ℤ c) (λ i₃ → [ b ] +ℤ c) ([ a ] +ℤ c) ≡ ([ b ] +ℤ c)
--     ([ a ] +ℤ c) ≡ ([ b ] +ℤ c)
-- ?3
--   : Square (λ i₃ → [ a ] +ℤ c₁) (λ i₃ → [ b ] +ℤ c₁) ([ a ] +ℤ c₁) ≡ ([ b ] +ℤ c₁)
--    ([ a ] +ℤ c₁) ≡ ([ b ] +ℤ c₁)

eq/ a b r i +ℤ squash/ c c₁ p q i₁ i₂ = isGroupoid→isGroupoid' ℤ-isGroupoid (squash/ ([ a ] +ℤ c) ([ a ] +ℤ c₁) (λ i₃ → [ a ] +ℤ p i₃) (λ i₃ → [ a ] +ℤ q i₃))
                                                                           (squash/ ([ b ] +ℤ c) ([ b ] +ℤ c₁) (λ i₃ → [ b ] +ℤ p i₃) (λ i₃ → [ b ] +ℤ q i₃))
                                                                          -- (λ i₃ i₄ → eq/ a b r i₃ +ℤ p i₄) (λ i₃ i₄ → eq/ a b r i₃ +ℤ q i₄) (λ i₃ i₄ → eq/ a b r i₃ +ℤ c) (λ i₃ i₄ → eq/ a b r i₃ +ℤ c₁)
                                                                            (eq+eq-1 [ a ] [ b ] c c₁ (eq/ a b r) p) (eq+eq-1 [ a ] [ b ] c c₁ (eq/ a b r) q) (eq+eq-2 [ a ] [ b ] c (eq/ a b r)) (eq+eq-2 [ a ] [ b ] c₁ (eq/ a b r))
                                                                            i i₁ i₂
                                       where
                                         eq+eq-1 : ∀ ( x₁ x₂  y₁ y₂ : ℤ ) → ( p : x₁ ≡ x₂ ) → ( q : y₁ ≡ y₂ )
                                                 → Square {- (i = i0) -} (λ k → x₁ +ℤ q k)
                                                          {- (i = i1) -} (λ k → x₂ +ℤ q k)
                                                          {- (j = i0) -} (cong (λ x → x +ℤ y₁) p)
                                                          {- (j = i1) -} (cong (λ x → x +ℤ y₂) p)
                                         eq+eq-1 x₁ x₂ y₁ p q i j = {!p!}
                                         eq+eq-2 : ∀ ( x₁ x₂  y₁ : ℤ ) → ( p : x₁ ≡ x₂ )
                                                 → Square {- (i = i0) -} (λ k → x₁ +ℤ y₁)
                                                          {- (i = i1) -} (λ k → x₂ +ℤ y₁)
                                                          {- (j = i0) -} (cong (λ x → x +ℤ y₁) p)
                                                          {- (j = i1) -} (cong (λ x → x +ℤ y₁) p)
                                         eq+eq-2 x₁ x₂ y₁ p i j = {!!}

squash/ a a₁ p q i i₁ +ℤ [ a₂ ] = squash/ (a +ℤ [ a₂ ]) (a₁ +ℤ [ a₂ ]) (cong (λ x → x +ℤ [ a₂ ]) (p)) (cong (λ x → x +ℤ [ a₂ ]) (q)) i i₁

-- i = i0 ⊢ p i₁ +ℤ eq/ a₂ b r i₂
-- i = i1 ⊢ q i₁ +ℤ eq/ a₂ b r i₂
-- i₁ = i0 ⊢ a +ℤ eq/ a₂ b r i₂
-- i₁ = i1 ⊢ a₁ +ℤ eq/ a₂ b r i₂
-- i₂ = i0 ⊢ squash/ (a +ℤ [ a₂ ]) (a₁ +ℤ [ a₂ ])
--           (λ i₃ → p i₃ +ℤ [ a₂ ]) (λ i₃ → q i₃ +ℤ [ a₂ ]) i i₁
-- i₂ = i1 ⊢ squash/ (a +ℤ [ b ]) (a₁ +ℤ [ b ]) (λ i₃ → p i₃ +ℤ [ b ])
--          (λ i₃ → q i₃ +ℤ [ b ]) i i₁

-- ?4
--   : Square (a +ℤ [ a₂ ]) ≡ (a +ℤ [ b ]) (a₁ +ℤ [ a₂ ]) ≡ (a₁ +ℤ [ b ]) (λ i₃ → p i₃ +ℤ [ a₂ ])
--     (λ i₃ → p i₃ +ℤ [ b ])
-- ?5
--   : Square (a +ℤ [ a₂ ]) ≡ (a +ℤ [ b ]) (a₁ +ℤ [ a₂ ]) ≡ (a₁ +ℤ [ b ]) (λ i₃ → q i₃ +ℤ [ a₂ ])
--     (λ i₃ → q i₃ +ℤ [ b ])
-- ?6
--   : Square (a +ℤ [ a₂ ]) ≡ (a +ℤ [ b ]) (a +ℤ [ a₂ ]) ≡ (a +ℤ [ b ]) (λ i₃ → a +ℤ [ a₂ ])
--     (λ i₃ → a +ℤ [ b ])
-- ?7
--   : Square (a₁ +ℤ [ a₂ ]) ≡ (a₁ +ℤ [ b ]) (a₁ +ℤ [ a₂ ]) ≡ (a₁ +ℤ [ b ]) (λ i₃ → a₁ +ℤ [ a₂ ])
--     (λ i₃ → a₁ +ℤ [ b ])

squash/ a a₁ p q i i₁ +ℤ eq/ a₂ b r i₂ = isGroupoid→isGroupoid' ℤ-isGroupoid
                                                                            -- (λ i₃ i₄ → p i₃ +ℤ eq/ a₂ b r i₄) (λ i₃ i₄ → q i₃ +ℤ eq/ a₂ b r i₄) (λ i₃ i₄ → a +ℤ (eq/ a₂ b r i₄)) (λ i₃ i₄ → ?)
                                                                            {!eq+eq-1 a a₁ [ a₂ ] [ b ] p (eq/ a₂ b r)!} {!!} {!!} {!!}
                                                                            (squash/ (a +ℤ [ a₂ ]) (a₁ +ℤ [ a₂ ]) (λ i₃ → p i₃ +ℤ [ a₂ ]) (λ i₃ → q i₃ +ℤ [ a₂ ]))
                                                                            (squash/ (a +ℤ [ b ]) (a₁ +ℤ [ b ]) (λ i₃ → p i₃ +ℤ [ b ]) (λ i₃ → q i₃ +ℤ [ b ]))
                                                                            i i₁ i₂
                                       where
                                         eq+eq-1 : ∀ ( x₁ x₂  y₁ y₂ : ℤ ) → ( p : x₁ ≡ x₂ ) → ( q : y₁ ≡ y₂ )
                                                 → Square {- (i = i0) -} (cong (λ y → x₁ +ℤ y) q)
                                                          {- (i = i1) -} (cong (λ y → x₂ +ℤ y) q)
                                                          {- (j = i0) -} (λ k → p k +ℤ y₁)
                                                          {- (j = i1) -} (λ k → p k +ℤ y₂)
                                         eq+eq-1 x₁ x₂ y₁ p q i j = {!!}
                                         eq+eq-2 : ∀ ( x₁ x₂  y₁ : ℤ ) → ( p : x₁ ≡ x₂ )
                                                 → Square {- (i = i0) -} (λ k → x₁ +ℤ y₁)
                                                          {- (i = i1) -} (λ k → x₂ +ℤ y₁)
                                                          {- (j = i0) -} (cong (λ x → x +ℤ y₁) p)
                                                          {- (j = i1) -} (cong (λ x → x +ℤ y₁) p)
                                         eq+eq-2 x₁ x₂ y₁ p i j = {!!}

-- i = i0 ⊢ p i₁ +ℤ squash/ c c₁ p₁ q₁ i₂ i₃
-- i = i1 ⊢ q i₁ +ℤ squash/ c c₁ p₁ q₁ i₂ i₃
-- i₁ = i0 ⊢ a +ℤ squash/ c c₁ p₁ q₁ i₂ i₃
-- i₁ = i1 ⊢ a₁ +ℤ squash/ c c₁ p₁ q₁ i₂ i₃
-- i₂ = i0 ⊢ squash/ a a₁ p q i i₁ +ℤ p₁ i₃
-- i₂ = i1 ⊢ squash/ a a₁ p q i i₁ +ℤ q₁ i₃
-- i₃ = i0 ⊢ squash/ a a₁ p q i i₁ +ℤ c
-- i₃ = i1 ⊢ squash/ a a₁ p q i i₁ +ℤ c₁
squash/ a a₁ p q i i₁ +ℤ squash/ c c₁ p₁ q₁ i₂ i₃ = {!!}


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
