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

open import Cubical.HITs.SetQuotients as SetQuotient
open import Cubical.HITs.PropositionalTruncation as PropositionalTruncation
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.Data.Nat as ℕ renaming (_+_ to _+ℕ_ ; _·_ to _*ℕ_)


rel : (ℕ × ℕ) → (ℕ × ℕ) → Type₀
rel (a₀ , b₀) (a₁ , b₁) = x ≡ y
  where
    x = a₀ +ℕ b₁
    y = a₁ +ℕ b₀

ℤ = (ℕ × ℕ) / rel

ℤ-isSet : isSet ℤ
ℤ-isSet m n p q = squash/ m n p q

_+ℕ'_ : (ℕ × ℕ) → (ℕ × ℕ) → (ℕ × ℕ)
(n₁ , n₂) +ℕ' (m₁ , m₂) = (n₁ +ℕ m₁ , n₂ +ℕ m₂)

[_-ℕ'_] : ℕ → ℕ → ℤ
[ x -ℕ' y ] = [ x , y ]

ℤ-cancelˡ : ∀ {a b} (c : ℕ) → [ c +ℕ a -ℕ' c +ℕ b ] ≡ [ a -ℕ' b ]
ℤ-cancelˡ {a} {b} c = eq/ _ _ (tmp a b c)
  where tmp : ∀ a b c → rel (c +ℕ a , c +ℕ b) (a , b)
        tmp a b c =
          c +ℕ a +ℕ b
            ≡⟨ cong (λ x → x +ℕ b) (ℕ.+-comm c a) ⟩
          a +ℕ c +ℕ b
            ≡⟨ sym(ℕ.+-assoc a c b) ⟩
          a +ℕ (c +ℕ b) ∎

ℤ-cancelʳ : ∀ {a b} (c : ℕ) → [ a +ℕ c -ℕ' b +ℕ c ] ≡ [ a -ℕ' b ]
ℤ-cancelʳ {a} {b} c = eq/ _ _ (tmp a b c)
  where tmp : ∀ a b c → rel (a +ℕ c , b +ℕ c) (a , b)
        tmp a b c =
          a +ℕ c +ℕ b
            ≡⟨ sym(ℕ.+-assoc a c b) ⟩
          a +ℕ (c +ℕ b)
            ≡⟨ cong (λ x → a +ℕ x) (ℕ.+-comm c b) ⟩
          a +ℕ (b +ℕ c) ∎

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

_+_ : ℤ → ℤ → ℤ
_+_ = SetQuotient.rec2 ℤ-isSet (λ x y → [ x +ℕ' y ]) feql feqr
  where
    feql : (a b c : ℕ × ℕ) (r : rel a b) → [ a +ℕ' c ] ≡ [ b +ℕ' c ]
    feql a b c r = eq/ (a +ℕ' c) (b +ℕ' c) (+-assoc-3-2 a b c r)
    feqr : (a b c : ℕ × ℕ) (r : rel b c) → [ a +ℕ' b ] ≡ [ a +ℕ' c ]
    feqr a b c r = eq/ (a +ℕ' b) (a +ℕ' c) (+-assoc-3-1 a b c r)

test : [ 3 , 9 ] + [ 10 , 14 ] ≡ [ 0 , 10 ]
test = ℤ-cancelˡ 13

zero-[a,a]ˡ-lem : (a : ℕ)(b : ℤ) → (Σ (ℕ × ℕ) ( λ (c , d) → [ (c , d) ]  ≡ b )) → [ a , a ] + b ≡ b
zero-[a,a]ˡ-lem a b ( (c , d) , p ) = 
  [ a , a ] + b           ≡⟨ cong (λ x → [ a , a ] + x) (sym(p)) ⟩
  [ a , a ] + [ c , d ]   ≡⟨ ℤ-cancelˡ a ⟩
  [ c , d ]               ≡⟨ p ⟩
  b ∎

zero-[a,a]ˡ : (a : ℕ)(b : ℤ) → [ a , a ] + b ≡ b
zero-[a,a]ˡ a b = PropositionalTruncation.rec (lem2 a b) (zero-[a,a]ˡ-lem a b) (SetQuotient.[]surjective b)
                                               where
                                                 lem2 : (a : ℕ) (b : ℤ) → isProp ([ a , a ] + b ≡ b)
                                                 lem2 a b = λ x y i i₁ → squash/ ([ a , a ] + b) b x y i i₁

zero-[a,a]ʳ-lem : (a : ℕ)(b : ℤ) → (Σ (ℕ × ℕ) ( λ (c , d) → [ (c , d) ]  ≡ b )) → b + [ a , a ] ≡ b
zero-[a,a]ʳ-lem a b ( (c , d) , p ) = 
  b + [ a , a ]           ≡⟨ cong (λ x → x + [ a , a ]) (sym(p)) ⟩
  [ c , d ] + [ a , a ]   ≡⟨ ℤ-cancelʳ a ⟩
  [ c , d ]               ≡⟨ p ⟩
  b ∎

zero-[a,a]ʳ : (a : ℕ)(b : ℤ) → b + [ a , a ] ≡ b
zero-[a,a]ʳ a b = PropositionalTruncation.rec (lem2 a b) (zero-[a,a]ʳ-lem a b) (SetQuotient.[]surjective b)
                                               where
                                                 lem2 : (a : ℕ) (b : ℤ) → isProp (b + [ a , a ] ≡ b)
                                                 lem2 a b = λ x y i i₁ → squash/ (b + [ a , a ]) b x y i i₁


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

_-_ : ℤ → ℤ → ℤ
a - b = a + (-ℤ' b)
