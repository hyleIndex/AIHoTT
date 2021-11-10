{-# OPTIONS --cubical #-}

open import Agda.Builtin.Cubical.Path
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

PathP→Path : {ℓ : Level} {A : Type ℓ} {x : A} {y : A} (p : PathP (λ _ → A) x y) → x ≡ y
PathP→Path p i = p i

pair≡ : {ℓ : Level} {A : Type ℓ} {B : A → Type ℓ} →
        ((x : A) → isProp (B x)) →
        (x y : Σ A B) →
        (fst x ≡ fst y) →
        x ≡ y
pair≡ {B = B} P (x , x') (y , y') f i = f i , p i
  where
  p : PathP (λ i → B (f i)) x' y'
  p = toPathP (P y _ y')

pair≡' : {ℓ : Level} {A : Type ℓ} {B : A → Type ℓ} →
        ((x : A) → isProp (B x)) →
        (x y : Σ A B) →
        (fst x ≡ fst y) →
        x ≡ y
pair≡' P x y f = ΣProp≡ P f
