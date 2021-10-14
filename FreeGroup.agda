{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.List

record Group A : Type where
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

data HITGro A : Type where
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
