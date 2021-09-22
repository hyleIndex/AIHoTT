{-# OPTIONS --cubical #-}
module DiffInt.Base where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
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

_+ℕ'_ : (ℕ × ℕ) → (ℕ × ℕ) → (ℕ × ℕ)
(n₁ , n₂) +ℕ' (m₁ , m₂) = (n₁ +ℕ m₁ , n₂ +ℕ m₂)

q-rec : ∀ {ℓ} {A : Type ℓ} {R : A → A → Type ℓ} {B : Type ℓ} →
        (Bset : isSet B) →
        (f : A → B) →
        (feq : {a b : A} (r : R a b) → f a ≡ f b) → (x : A / R) →
        B
q-rec Bset f feq [ a ] = f a
q-rec Bset f feq (eq/ a b r i) = feq r i
q-rec Bset f feq (squash/ x x₁ p q i i₁) = {!!}

_+ℤ_ : ℤ → ℤ → ℤ
[ a ] +ℤ [ a₁ ] = [ a +ℕ' a₁ ]
[ a ] +ℤ eq/ a₁ b r i = eq/ (a +ℕ' a₁) (a +ℕ' b)
                            (+-assoc-6-1 (fst a) (snd a) (fst a₁) (snd a₁) (fst b) (snd b) r) i
                            where
                              +-assoc-6-1 : ∀ a b c d e f → c +ℕ f ≡ e +ℕ d → (a +ℕ c) +ℕ (b +ℕ f) ≡ (a +ℕ e) +ℕ (b +ℕ d)
                              +-assoc-6-1 a b c d e f p =
                                (a +ℕ c) +ℕ (b +ℕ f) ≡⟨ cong (λ x → (a +ℕ c) +ℕ x) (ℕ.+-comm b f) ⟩
                                (a +ℕ c) +ℕ (f +ℕ b) ≡⟨ ℕ.+-assoc (a +ℕ c) f b ⟩
                                a +ℕ c +ℕ f +ℕ b     ≡⟨ cong (λ x → x +ℕ b) (sym (ℕ.+-assoc a c f)) ⟩
                                a +ℕ (c +ℕ f) +ℕ b   ≡⟨ cong (λ x → a +ℕ x +ℕ b) p ⟩
                                a +ℕ (e +ℕ d) +ℕ b   ≡⟨ cong (λ x → x +ℕ b) (ℕ.+-assoc a e d) ⟩
                                a +ℕ e +ℕ d +ℕ b     ≡⟨ sym (ℕ.+-assoc (a +ℕ e) d b) ⟩
                                a +ℕ e +ℕ (d +ℕ b)   ≡⟨ cong (λ x → a +ℕ e +ℕ x) (ℕ.+-comm d b) ⟩
                                a +ℕ e +ℕ (b +ℕ d) ∎
[ a ] +ℤ squash/ c c₁ p q i i₁ = squash/ ( [ a ] +ℤ c) ([ a ] +ℤ c₁) (cong (λ x → [ a ] +ℤ x) (p)) (cong (λ x → [ a ] +ℤ x) (q)) i i₁
eq/ a b r i +ℤ [ a₁ ] = eq/ (a +ℕ' a₁) (b +ℕ' a₁)
                            (+-assoc-6-2 (fst a) (snd a) (fst b) (snd b) (fst a₁) (snd a₁) r) i
                            where
                              +-assoc-6-2 : ∀ a b c d e f → a +ℕ d ≡ c +ℕ b → (a +ℕ e) +ℕ (d +ℕ f) ≡ (c +ℕ e) +ℕ (b +ℕ f)
                              +-assoc-6-2 a b c d e f p =
                                (a +ℕ e) +ℕ (d +ℕ f) ≡⟨ cong (λ x → x +ℕ (d +ℕ f)) (ℕ.+-comm a e) ⟩
                                (e +ℕ a) +ℕ (d +ℕ f) ≡⟨ ℕ.+-assoc (e +ℕ a) d f ⟩
                                e +ℕ a +ℕ d +ℕ f     ≡⟨ cong (λ x → x +ℕ f) (sym (ℕ.+-assoc e a d)) ⟩
                                e +ℕ (a +ℕ d) +ℕ f   ≡⟨ cong (λ x → e +ℕ x +ℕ f) p ⟩
                                e +ℕ (c +ℕ b) +ℕ f   ≡⟨ cong (λ x → x +ℕ f) (ℕ.+-assoc e c b) ⟩
                                e +ℕ c +ℕ b +ℕ f     ≡⟨ sym (ℕ.+-assoc (e +ℕ c) b f) ⟩
                                e +ℕ c +ℕ (b +ℕ f)   ≡⟨ cong (λ x → x +ℕ (b +ℕ f)) (ℕ.+-comm e c) ⟩
                                c +ℕ e +ℕ (b +ℕ f) ∎

-- i = i0 ⊢ eq/ (a +ℕ' a₁) (a +ℕ' b₁)
         -- (DiffInt.Base.+-assoc-6-1 a a₁ b₁ r₁ i₁ (fst a) (snd a) (fst a₁)
          -- (snd a₁) (fst b₁) (snd b₁) r₁)
         -- i₁
-- i = i1 ⊢ eq/ (b +ℕ' a₁) (b +ℕ' b₁)
         -- (DiffInt.Base.+-assoc-6-1 b a₁ b₁ r₁ i₁ (fst b) (snd b) (fst a₁)
          -- (snd a₁) (fst b₁) (snd b₁) r₁)
         -- i₁
-- i₁ = i0 ⊢ eq/ (a +ℕ' a₁) (b +ℕ' a₁)
          -- (DiffInt.Base.+-assoc-6-2 a b r i a₁ (fst a) (snd a) (fst b)
           -- (snd b) (fst a₁) (snd a₁) r)
          -- i
-- i₁ = i1 ⊢ eq/ (a +ℕ' b₁) (b +ℕ' b₁)
          -- (DiffInt.Base.+-assoc-6-2 a b r i b₁ (fst a) (snd a) (fst b)
           -- (snd b) (fst b₁) (snd b₁) r)
          -- i
eq/ a b r i +ℤ eq/ a₁ b₁ r₁ i₁ = isSet→isSet' ℤ-isSet {!+-assoc-6-1 a a₁ b₁ r₁ i₁ (fst a) (snd a) (fst a₁) (snd a₁) (fst b₁) (snd b₁) r₁!} {!!} {!!} {!!} i i₁
-- eq/ (a +ℕ' a₁) (b +ℕ' b₁) (+-assoc-8 a b a₁ b₁ r r₁) {!!}
                               where
                                 +-assoc-8 : ∀ a b a₁ b₁ → rel a b → rel a₁ b₁ → rel (a +ℕ' a₁) (b +ℕ' b₁)
                                 +-assoc-8 a b a₁ b₁ r r₁ =
                                   fst a +ℕ fst a₁ +ℕ (snd b +ℕ snd b₁) ≡⟨ ℕ.+-assoc (fst a +ℕ fst a₁) (snd b) (snd b₁) ⟩
                                   fst a +ℕ fst a₁ +ℕ snd b +ℕ snd b₁   ≡⟨ cong (λ x → x +ℕ snd b₁) (sym (ℕ.+-assoc (fst a) (fst a₁) (snd b))) ⟩
                                   fst a +ℕ (fst a₁ +ℕ snd b) +ℕ snd b₁ ≡⟨ cong (λ x → fst a +ℕ x +ℕ snd b₁) (ℕ.+-comm (fst a₁) (snd b)) ⟩
                                   fst a +ℕ (snd b +ℕ fst a₁) +ℕ snd b₁ ≡⟨ cong (λ x → x +ℕ snd b₁) (ℕ.+-assoc (fst a) (snd b) (fst a₁)) ⟩
                                   fst a +ℕ snd b +ℕ fst a₁ +ℕ snd b₁   ≡⟨ cong (λ x → x +ℕ fst a₁ +ℕ snd b₁) (r) ⟩
                                   fst b +ℕ snd a +ℕ fst a₁ +ℕ snd b₁   ≡⟨ sym (ℕ.+-assoc (fst b +ℕ snd a) (fst a₁) (snd b₁)) ⟩
                                   fst b +ℕ snd a +ℕ (fst a₁ +ℕ snd b₁) ≡⟨ cong (λ x →  fst b +ℕ snd a +ℕ x) (r₁) ⟩
                                   fst b +ℕ snd a +ℕ (fst b₁ +ℕ snd a₁) ≡⟨ ℕ.+-assoc (fst b +ℕ snd a) (fst b₁) (snd a₁) ⟩
                                   fst b +ℕ snd a +ℕ fst b₁ +ℕ snd a₁   ≡⟨ cong (λ x → x +ℕ snd a₁) (sym (ℕ.+-assoc (fst b) (snd a) (fst b₁))) ⟩
                                   fst b +ℕ (snd a +ℕ fst b₁) +ℕ snd a₁ ≡⟨ cong (λ x → fst b +ℕ x +ℕ snd a₁) (ℕ.+-comm (snd a) (fst b₁)) ⟩
                                   fst b +ℕ (fst b₁ +ℕ snd a) +ℕ snd a₁ ≡⟨ cong (λ x → x +ℕ snd a₁) (ℕ.+-assoc (fst b) (fst b₁) (snd a)) ⟩
                                   fst b +ℕ fst b₁ +ℕ snd a +ℕ snd a₁   ≡⟨ sym (ℕ.+-assoc (fst b +ℕ fst b₁) (snd a) (snd a₁)) ⟩
                                   fst b +ℕ fst b₁ +ℕ (snd a +ℕ snd a₁) ∎
eq/ a b r i +ℤ squash/ c c₁ p q i₁ i₂ = {!!} -- this is because ℤ is a set and therefore a groupoid!
-- squash/ ([ a ] +ℤ c) ([ b ] +ℤ c₁) (+-rewrite-4 [ a ] [ b ] c c₁ (eq/ a b r) p) (+-rewrite-4 [ a ] [ b ] c c₁ (eq/ a b r) q) (i ∧ i₁) {!!}
    where
      +-rewrite-4 : ∀ a b c d → a ≡ b → c ≡ d → a +ℤ c ≡ b +ℤ d
      +-rewrite-4 a b c d p q =
        a +ℤ c ≡⟨ cong (λ x → a +ℤ x) (q) ⟩
        a +ℤ d ≡⟨ cong (λ x → x +ℤ d) (p) ⟩
        b +ℤ d ∎
squash/ a a₁ p q i i₁ +ℤ [ a₂ ] = squash/ (a +ℤ [ a₂ ]) (a₁ +ℤ [ a₂ ]) (cong (λ x → x +ℤ [ a₂ ]) (p)) (cong (λ x → x +ℤ [ a₂ ]) (q)) i i₁
squash/ a a₁ p q i i₁ +ℤ eq/ a₂ b r i₂ = {!!} -- groupoid also here I guess...
-- squash/ (a +ℤ [ a₂ ]) (a₁ +ℤ [ b ]) (+-rewrite-4 a a₁ [ a₂ ] [ b ] p (eq/ a₂ b r)) (+-rewrite-4 a a₁ [ a₂ ] [ b ] q (eq/ a₂ b r)) (i ∧ i₂) {!!}
    where
      +-rewrite-4 : ∀ a b c d → a ≡ b → c ≡ d → a +ℤ c ≡ b +ℤ d
      +-rewrite-4 a b c d p q =
        a +ℤ c ≡⟨ cong (λ x → a +ℤ x) (q) ⟩
        a +ℤ d ≡⟨ cong (λ x → x +ℤ d) (p) ⟩
        b +ℤ d ∎
squash/ a a₁ p q i i₁ +ℤ squash/ c c₁ p₁ q₁ i₂ i₃ = squash/ (a +ℤ c) (a₁ +ℤ c₁) (+-rewrite-4 a a₁ c c₁ p p₁) (+-rewrite-4 a a₁ c c₁ q q₁) (i ∧ i₂) {!!}
    where
      +-rewrite-4 : ∀ a b c d → a ≡ b → c ≡ d → a +ℤ c ≡ b +ℤ d
      +-rewrite-4 a b c d p q =
        a +ℤ c ≡⟨ cong (λ x → a +ℤ x) (q) ⟩
        a +ℤ d ≡⟨ cong (λ x → x +ℤ d) (p) ⟩
        b +ℤ d ∎


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
