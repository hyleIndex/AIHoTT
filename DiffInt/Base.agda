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

lemma : (g : ℕ × ℕ → ℕ × ℕ → ℕ)
        (g-eql : ∀ ((x , x') (y , y') (z , z') : ℕ × ℕ) (p : x +ℕ y' ≡ y +ℕ x')
                 → y' +ℕ (g (x , x') (z , z')) ≡ x' +ℕ (g (y , y') (z , z')))
        (g-eqr : ∀ ((x , x') (y , y') (z , z') : ℕ × ℕ) (p : y +ℕ z' ≡ z +ℕ y')
                 → (g (x , x') (y , y')) +ℕ z' ≡ (g (x , x') (z , z')) +ℕ y')
        → ℤ → ℤ → ℤ
lemma g g-eql g-eqr = rec2 ℤ-isSet (λ (x , x') (y , y') → [ g (x , x') (y , y') -ℕ' (x' +ℕ y') ])
                                   (λ (x , x') (y , y') (z , z') r → eql (x , x') (y , y') (z , z') r)
                                   (λ (x , x') (y , y') (z , z') p → eqr (x , x') (y , y') (z , z') p )
                                   where
                                     eql : ∀ ((x , x') (y , y') (z , z') : ℕ × ℕ) (p : x +ℕ y' ≡ y +ℕ x')
                                           → [ g (x , x') (z , z') -ℕ' x' +ℕ z' ] ≡ [ g (y , y') (z , z') -ℕ' y' +ℕ z' ]
                                     eql (x , x') (y , y') (z , z') p =
                                       [ g (x , x') (z , z') -ℕ' x' +ℕ z' ]
                                         ≡⟨ sym (ℤ-cancelˡ y') ⟩
                                       [ y' +ℕ (g (x , x') (z , z')) -ℕ' y' +ℕ (x' +ℕ z') ]
                                         ≡[ i ]⟨ [ y' +ℕ (g (x , x') (z , z')) -ℕ' ℕ.+-assoc y' x' z' i ] ⟩
                                       [ y' +ℕ (g (x , x') (z , z')) -ℕ' (y' +ℕ x') +ℕ z' ]
                                         ≡[ i ]⟨ [ g-eql (x , x') (y , y') (z , z') p i -ℕ' ℕ.+-comm y' x' i +ℕ z' ] ⟩
                                       [ x' +ℕ (g (y , y') (z , z')) -ℕ' (x' +ℕ y') +ℕ z' ]
                                         ≡[ i ]⟨ [ x' +ℕ (g (y , y') (z , z')) -ℕ' ℕ.+-assoc x' y' z' (~ i) ] ⟩
                                       [ x' +ℕ (g (y , y') (z , z')) -ℕ' x' +ℕ (y' +ℕ z') ]
                                         ≡⟨ ℤ-cancelˡ x' ⟩
                                       [ g (y , y') (z , z') -ℕ' y' +ℕ z' ] ∎
                                     eqr : ∀ ((x , x') (y , y') (z , z') : ℕ × ℕ) (p : y +ℕ z' ≡ z +ℕ y')
                                           → [ g (x , x') (y , y') -ℕ' x' +ℕ y' ] ≡ [ g (x , x') (z , z') -ℕ' x' +ℕ z' ]
                                     eqr (x , x') (y , y') (z , z') p =
                                       [ g (x , x') (y , y') -ℕ' x' +ℕ y' ]
                                         ≡⟨ sym (ℤ-cancelʳ z') ⟩
                                       [ (g (x , x') (y , y')) +ℕ z' -ℕ' (x' +ℕ y') +ℕ z' ]
                                         ≡[ i ]⟨ [ (g (x , x') (y , y')) +ℕ z' -ℕ' ℕ.+-assoc x' y' z' (~ i) ] ⟩
                                       [ (g (x , x') (y , y')) +ℕ z' -ℕ' x' +ℕ (y' +ℕ z') ]
                                         ≡[ i ]⟨ [ g-eqr (x , x') (y , y') (z , z') p i -ℕ' x' +ℕ ℕ.+-comm y' z' i ] ⟩
                                       [ (g (x , x') (z , z')) +ℕ y' -ℕ' x' +ℕ (z' +ℕ y') ]
                                         ≡[ i ]⟨ [ (g (x , x') (z , z')) +ℕ y' -ℕ' ℕ.+-assoc x' z' y' i ] ⟩
                                       [ (g (x , x') (z , z')) +ℕ y' -ℕ' (x' +ℕ z') +ℕ y' ]
                                         ≡⟨ ℤ-cancelʳ y' ⟩
                                       [ g (x , x') (z , z') -ℕ' x' +ℕ z' ] ∎

sym→lemma : (g : ℕ × ℕ → ℕ × ℕ → ℕ)
            (g-sym : ∀ x y → g x y ≡ g y x)
            (g-eql : ∀ ((x , x') (y , y') (z , z') : ℕ × ℕ) (p : x +ℕ y' ≡ y +ℕ x')
                     → y' +ℕ (g (x , x') (z , z')) ≡ x' +ℕ (g (y , y') (z , z')))
            → ℤ → ℤ → ℤ
sym→lemma g g-sym g-eql = lemma g g-eql q-eqr
                            where
                              q-eqr : ∀ ((x , x') (y , y') (z , z') : ℕ × ℕ) (p : y +ℕ z' ≡ z +ℕ y')
                                      → (g (x , x') (y , y')) +ℕ z' ≡ (g (x , x') (z , z')) +ℕ y'
                              q-eqr (x , x') (y , y') (z , z') p =
                                (g (x , x') (y , y')) +ℕ z' ≡[ i ]⟨ ℕ.+-comm (g-sym (x , x') (y , y') i) (z') i ⟩
                                z' +ℕ (g (y , y') (x , x')) ≡⟨ g-eql (y , y') (z , z') (x , x') p ⟩
                                y' +ℕ (g (z , z') (x , x')) ≡[ i ]⟨ ℕ.+-comm (y') (g-sym (z , z') (x , x') i) i ⟩
                                (g (x , x') (z , z')) +ℕ y' ∎

_+_ : ℤ → ℤ → ℤ
_+_ = sym→lemma (λ { (x , x') (c , d) → x +ℕ c })
                (λ { (x , x') (c , d) → ℕ.+-comm x c })
                (λ { (x , x') (c , d) (e , f) p → tmp (x , x') (c , d) (e , f) p})
                where
                  tmp : ∀ ((x , x') (c , d) (e , f) : ℕ × ℕ) → x +ℕ d ≡ c +ℕ x' → d +ℕ (x +ℕ e) ≡ x' +ℕ (c +ℕ e)
                  tmp (x , x') (c , d) (e , f) p =
                    d +ℕ (x +ℕ e) ≡⟨ ℕ.+-assoc d x e ⟩
                    d +ℕ x +ℕ e   ≡⟨ cong (λ x → x +ℕ e) (ℕ.+-comm d x) ⟩
                    x +ℕ d +ℕ e   ≡⟨ cong (λ x → x +ℕ e) p ⟩
                    c +ℕ x' +ℕ e  ≡⟨ cong (λ x → x +ℕ e) (ℕ.+-comm c x') ⟩
                    x' +ℕ c +ℕ e  ≡⟨ sym(ℕ.+-assoc x' c e) ⟩
                    x' +ℕ (c +ℕ e) ∎

test : [ 3 , 9 ] + [ 10 , 14 ] ≡ [ 0 , 10 ]
test = ℤ-cancelˡ 13

zero-[a,a]ˡ-lem : (a : ℕ)(b : ℤ) → (∃[ (c , d) ∈ ℕ × ℕ ] [ (c , d) ] ≡ b)  → [ a , a ] + b ≡ b
zero-[a,a]ˡ-lem a b ((c , d) , p) =
  [ a , a ] + b           ≡⟨ cong (λ x → [ a , a ] + x) (sym(p)) ⟩
  [ a , a ] + [ c , d ]   ≡⟨ ℤ-cancelˡ a ⟩
  [ c , d ]               ≡⟨ p ⟩
  b ∎

zero-[a,a]ˡ : (a : ℕ)(b : ℤ) → [ a , a ] + b ≡ b
zero-[a,a]ˡ a b = zero-[a,a]ˡ-lem a b ([]surjective b)

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
