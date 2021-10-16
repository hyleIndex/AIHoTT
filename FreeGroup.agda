{-# OPTIONS --cubical #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything hiding (Type; assoc; _∘_; ⟨_⟩)
open import Cubical.Data.List

variable
  ℓ ℓ′ : Level
  A B C T : Type₀

record Group A : Type₀ where
  field
    set : isSet A

    _∘_  : A → A → A
    -_   : A → A
    ε   : A

    unit-l : ∀ x     → ε ∘ x ≡ x
    unit-r : ∀ x     → x ∘ ε ≡ x
    inv-l  : ∀ x     → x ∘ (- x) ≡ ε
    inv-r  : ∀ x     → (- x) ∘ x ≡ ε
    assoc  : ∀ x y z → (x ∘ y) ∘ z ≡ x ∘ (y ∘ z)

open Group {{...}}

data HITGro A : Type₀ where
  ⟨_⟩   : A → HITGro A
  :ε:   : HITGro A
  _:∘:_  : HITGro A → HITGro A → HITGro A
  :-:_  : HITGro A → HITGro A

  :unit-l: : ∀ x      → :ε: :∘: x ≡ x
  :unit-r: : ∀ x      → x :∘: :ε: ≡ x
  :inv-l:  : ∀ x      → x :∘: (:-: x) ≡ :ε:
  :inv-r:  : ∀ x      → (:-: x) :∘: x ≡ :ε:
  :assoc:  : ∀ x y z  → (x :∘: y) :∘: z ≡ x :∘: (y :∘: z)

  trunc    : isSet (HITGro A)

freeGroup : ∀ A → Group (HITGro A)
freeGroup A = record
  { set = trunc
  ; _∘_ = _:∘:_
  ; -_ = :-:_
  ; ε = :ε:
  ; unit-l = :unit-l:
  ; unit-r = :unit-r:
  ; inv-l = :inv-l:
  ; inv-r = :inv-r:
  ; assoc = :assoc:
  }

elimProp : (P : HITGro A → Type) → (∀ x → isProp (P x))
             → (∀ x → P ⟨ x ⟩) → P :ε: → (∀ x y → P x → P y → P (x :∘: y)) → (∀ x → P x → P (:-: x)) → ∀ x → P x
elimProp P PIsProp P⟨_⟩ Pe P∘ Pinv = go
  where
    go : ∀ x → P x
    go ⟨ x ⟩ = P⟨_⟩ x
    go :ε: = Pe
    go (x :∘: y) = P∘ x y (go x) (go y)
    go (:-: x) = Pinv x (go x)
    go (:unit-l: x i) = isProp→PathP (λ j → PIsProp (:unit-l: x j)) (P∘ _ _ Pe (go x)) (go x) i
    go (:unit-r: x i) = isProp→PathP (λ j → PIsProp (:unit-r: x j)) (P∘ _ _ (go x) Pe) (go x) i
    go (:inv-l: x i) = isProp→PathP (λ j → PIsProp (:inv-l: x j)) (P∘ _ _ (go x) (Pinv _ (go x))) (Pe) i
    go (:inv-r: x i) = isProp→PathP (λ j → PIsProp (:inv-r: x j)) (P∘ _ _ (Pinv _ (go x)) (go x)) (Pe) i
    go (:assoc: x y z i) = isProp→PathP (λ j → PIsProp (:assoc: x y z j)) (P∘ _ _ (P∘ _ _ (go x) (go y)) (go z)) (P∘ _ _ (go x) (P∘ _ _ (go y) (go z))) i
    go (trunc x y p q i j) = isOfHLevel→isOfHLevelDep 2 (λ a → isProp→isSet (PIsProp a)) (go x) (go y) (cong go p) (cong go q) (trunc x y p q) i j

data FG A : Type where
  Pos : List A -> FG A
  Neg : List A -> FG A
  e : Pos [] ≡ Neg []

module FGVsHITGro {A : Type} (AIsSet : isSet A) where
  listIsSet : isSet (List A)
  listIsSet = isOfHLevelList 0 AIsSet

  fromFG : FG A → HITGro A
  fromFG (Pos x) = {!!}
  fromFG (Neg x) = {!!}
  fromFG (e i) = {!!}
