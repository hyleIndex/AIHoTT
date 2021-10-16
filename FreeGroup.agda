{-# OPTIONS --cubical #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything hiding (Type; assoc; _∘_; ⟨_⟩)
open import Cubical.Data.List
open import Cubical.Data.Bool
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients as SetQuotients renaming( [_] to ∥_∥ )


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

elimFGProp : {A : Type₀} → (P : HITGro A → Type) → (∀ x → isProp (P x))
             → (∀ x → P ⟨ x ⟩) → P :ε: → (∀ x y → P x → P y → P (x :∘: y)) → (∀ x → P x → P (:-: x)) → ∀ x → P x
elimFGProp P PIsProp P⟨_⟩ Pe P∘ Pinv = go
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

module FGByList {A : Type₀} (AIsSet : isSet A) where
  X : Type
  X = Bool × A

  FA : Type₀
  FA = List X

  inv : X → X
  inv (f , x) = (not f , x)

  finv : FA → FA
  finv [] = []
  finv (x ∷ xs) = finv xs ++ [ inv x ]

  rel : FA → FA → Type₀
  rel s t = Σ[ u ∈ FA ] (Σ[ v ∈ FA ] (Σ[ x ∈ X ] ((s ≡ (u ++ [ x ] ++ [ inv x ] ++ v)) × (t ≡ u ++ v))))

  FG : Type₀
  FG = FA / rel

  FG-isSet : isSet FG
  FG-isSet = λ _ _ _ _ → squash/ _ _ _ _

  _+_ : FG → FG → FG
  _+_ = rec2 FG-isSet (λ x y → ∥ x ++ y ∥) {!!} {!!}

  FG+-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
  FG+-assoc = SetQuotients.elimProp3 (λ _ _ _ → FG-isSet _ _)
              (λ { x y z i → ∥ ++-assoc x y z i  ∥ })

  -FG_ : FG → FG
  -FG ∥ a ∥ = {!!}
  -FG eq/ a b r i = {!!}
  -FG squash/ x x₁ p q i i₁ = {!!}

module FGVsHITGro {A : Type₀} (AIsSet : isSet A) where
  open FGByList {A = A} AIsSet

  toFG : HITGro A → FG
  toFG ⟨ x ⟩ = ∥ [ (true , x) ] ∥
  toFG :ε: = ∥ [] ∥
  toFG (x :∘: y) = (toFG x) + (toFG y)
  toFG (:-: x) = -FG (toFG x)
  toFG (:unit-l: x i) = {!!}
  toFG (:unit-r: x i) = {!!}
  toFG (:inv-l: x i) = {!!}
  toFG (:inv-r: x i) = {!!}
  toFG (:assoc: x y z i) = FG+-assoc (toFG x) (toFG y) (toFG z) i
  toFG (trunc x y p q i j) = FG-isSet (toFG x) (toFG y) (λ k → toFG (p k)) (λ k → toFG (q k)) i j

  private
    fromFA : FA → HITGro A
    fromFA [] = :ε:
    fromFA ((false , x) ∷ xs) = (:-: ⟨ x ⟩) :∘: (fromFA xs)
    fromFA ((true , x) ∷ xs) = ⟨ x ⟩ :∘: (fromFA xs)

    inv→inv : (x : X) → fromFA ([ x ] ++ [ inv x ]) ≡ :ε:
    inv→inv (true , x) = {!(⟨ x ⟩) :∘: ((:-: ⟨ x ⟩) :∘: :ε:) ≡⟨?⟩ ? ∎!}
    inv→inv (false , x) = {!!}

  fromFG : FG → HITGro A
  fromFG ∥ [] ∥ = :ε:
  fromFG ∥ x ∷ xs ∥ = (tmp x) :∘: (fromFG ∥ xs ∥)
    where
      tmp : X → HITGro A
      tmp (true , x) = ⟨ x ⟩
      tmp (false , x) = :-: ⟨ x ⟩
  fromFG (eq/ a b r i) = {!!}
  fromFG (squash/ x y p q i j) = trunc (fromFG x) (fromFG y) (λ k → fromFG (p k)) (λ k → fromFG (q k)) i j
