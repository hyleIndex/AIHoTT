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
    inv-r  : ∀ x     → x ∘ (- x) ≡ ε
    inv-l  : ∀ x     → (- x) ∘ x ≡ ε
    assoc  : ∀ x y z → (x ∘ y) ∘ z ≡ x ∘ (y ∘ z)

open Group {{...}}

data HITGro A : Type₀ where
  ⟨_⟩   : A → HITGro A
  :ε:   : HITGro A
  _:∘:_  : HITGro A → HITGro A → HITGro A
  :-:_  : HITGro A → HITGro A

  :unit-l: : ∀ x      → :ε: :∘: x ≡ x
  :unit-r: : ∀ x      → x :∘: :ε: ≡ x
  :inv-r:  : ∀ x      → x :∘: (:-: x) ≡ :ε:
  :inv-l:  : ∀ x      → (:-: x) :∘: x ≡ :ε:
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
    go (:inv-r: x i) = isProp→PathP (λ j → PIsProp (:inv-r: x j)) (P∘ _ _ (go x) (Pinv _ (go x))) (Pe) i
    go (:inv-l: x i) = isProp→PathP (λ j → PIsProp (:inv-l: x j)) (P∘ _ _ (Pinv _ (go x)) (go x)) (Pe) i
    go (:assoc: x y z i) = isProp→PathP (λ j → PIsProp (:assoc: x y z j)) (P∘ _ _ (P∘ _ _ (go x) (go y)) (go z)) (P∘ _ _ (go x) (P∘ _ _ (go y) (go z))) i
    go (trunc x y p q i j) = isOfHLevel→isOfHLevelDep 2 (λ a → isProp→isSet (PIsProp a)) (go x) (go y) (cong go p) (cong go q) (trunc x y p q) i j

module FGByList {A : Type₀} (AIsSet : isSet A) where
  X : Type
  X = Bool × A

  FA : Type₀
  FA = List X

  inv : X → X
  inv (f , x) = (not f , x)

  inv-invol : (x : X) → inv (inv x) ≡ x
  inv-invol (false , v) = refl
  inv-invol (true , v) = refl

  finv : FA → FA
  finv [] = []
  finv (x ∷ xs) = finv xs ++ [ inv x ]

  ++-finv-hom : (s t : FA) → finv (s ++ t) ≡ finv t ++ finv s
  ++-finv-hom [] t = sym (++-unit-r (finv t))
  ++-finv-hom (x ∷ xs) t = finv (xs ++ t) ++ [ inv x ] ≡⟨ cong (λ y → y ++ [ inv x ]) (++-finv-hom xs t) ⟩
                           (finv t ++ finv xs) ++ [ inv x ] ≡⟨ ++-assoc (finv t) (finv xs) [ inv x ] ⟩
                           finv t ++ finv xs ++ [ inv x ]  ∎

  finv-invol : (x : FA) → finv (finv x) ≡ x
  finv-invol [] = refl
  finv-invol (x ∷ xs) = ++-finv-hom (finv xs) [ inv x ] ∙ (cong (λ a →  a ∷ (finv (finv xs))) (inv-invol x)) ∙ cong (λ a → x ∷ a) (finv-invol xs)

  rel : FA → FA → Type₀
  rel s t = Σ[ u ∈ FA ] (Σ[ v ∈ FA ] (Σ[ x ∈ X ] ((s ≡ (u ++ [ x ] ++ [ inv x ] ++ v)) × (t ≡ u ++ v))))

  rel-ex : FA → FA → Type₀
  rel-ex s t = Σ[ u ∈ FA ] (Σ[ v ∈ FA ] (Σ[ x ∈ FA ] (((s ≡ (u ++ x ++ finv x ++ v)) × (t ≡ u ++ v)) ⊎ ((t ≡ (u ++ x ++ finv x ++ v)) × (s ≡ u ++ v)))))

  +-left-congruence-ex : ∀ x x' y → rel-ex x x' → rel-ex (x ++ y) (x' ++ y)
  +-left-congruence-ex x x' y (u , v , z , inl(p , q)) = u , v ++ y , z , inl(p' , q')
    where
      p' : x ++ y ≡ u ++ z ++ finv z ++ v ++ y
      p' = cong (λ a → a ++ y) p ∙ ++-assoc u (z ++ finv z ++ v) y ∙ cong (λ a → u ++ a) (++-assoc z (finv z ++ v) y) ∙ cong (λ a → u ++ z ++ a) (++-assoc (finv z) v y)
      q' : x' ++ y ≡ u ++ v ++ y
      q' = cong (λ a → a ++ y) q ∙ (++-assoc u v y)
  +-left-congruence-ex x x' y (u , v , z , inr(p , q)) = u , ((v ++ y) , (z , (inr (p' , q'))))
    where
      p' = cong (λ a → a ++ y) p ∙ ++-assoc u (z ++ finv z ++ v) y ∙ cong (λ a → u ++ a) (++-assoc z (finv z ++ v) y) ∙ cong (λ a → u ++ z ++ a) (++-assoc (finv z) v y)
      q' = cong (λ a → a ++ y) q ∙ (++-assoc u v y)

  +-right-congruence-ex : ∀ x y y' → rel-ex y y' → rel-ex (x ++ y) (x ++ y')
  +-right-congruence-ex x y y' (u , v , z , inl (p , q)) = x ++ u , v , z , inl(p' , q')
    where
      p' = cong (λ a → x ++ a) p ∙ (sym (++-assoc x u (z ++ finv z ++ v)))
      q' = cong (λ a → x ++ a) q ∙ (sym (++-assoc x u v))
  +-right-congruence-ex x y y' (u , v , z , inr (p , q)) = x ++ u , v , z , inr (p' , q')
    where
      p' = cong (λ a → x ++ a) p ∙ (sym (++-assoc x u (z ++ finv z ++ v)))
      q' = cong (λ a → x ++ a) q ∙ (sym (++-assoc x u v))

  FG : Type₀
  FG = FA / rel-ex

  FG-isSet : isSet FG
  FG-isSet = λ _ _ _ _ → squash/ _ _ _ _

  +-left-congruence : ∀ x x' y → rel x x' → rel (x ++ y) (x' ++ y)
  +-left-congruence x x' y (u , v , z , p , q) = u , (v ++ y) , z , p' , q'
    where
      p' = (cong (λ z → z ++ y) p) ∙ (++-assoc u ([ z ] ++ [ inv z ] ++ v) y)
      q' = (cong (λ z → z ++ y) q) ∙ (++-assoc u v y)

  +-right-congruence : ∀ x y y' → rel y y' → rel (x ++ y) (x ++ y')
  +-right-congruence x y y' (u , v , z , p , q) = (x ++ u) , v , z , p' , q'
    where
      p' = (cong (λ z → x ++ z) p) ∙ (sym (++-assoc x u ([ z ] ++ [ inv z ] ++ v)))
      q' = (cong (λ z → x ++ z) q) ∙ (sym (++-assoc x u v))

  _+_ : FG → FG → FG
  _+_ = rec2 FG-isSet (λ x y → ∥ x ++ y ∥) feql feqr
             where
               feql : (a b c : FA) (r : rel-ex a b) → ∥ a ++ c ∥ ≡ ∥ b ++ c ∥
               feql a b c r = eq/ (a ++ c) (b ++ c) (+-left-congruence-ex a b c r)
               feqr : (a b c : FA) (r : rel-ex b c) → ∥ a ++ b ∥ ≡ ∥ a ++ c ∥
               feqr a b c r = eq/ (a ++ b) (a ++ c) (+-right-congruence-ex a b c r)

  +-unit-r : ∀ x → x + ∥ [] ∥ ≡ x
  +-unit-r = SetQuotients.elimProp (λ x → FG-isSet (x + ∥ [] ∥) x)
              (λ { x i → ∥ ++-unit-r x i ∥ })

  +-unit-l : ∀ x → ∥ [] ∥ + x ≡ x
  +-unit-l = SetQuotients.elimProp (λ x → FG-isSet (∥ [] ∥ + x) x)
              (λ { x i → ∥ refl { x = x } i ∥ })

  FG+-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
  FG+-assoc = SetQuotients.elimProp3 (λ _ _ _ → FG-isSet _ _)
              (λ { x y z i → ∥ ++-assoc x y z i  ∥ })

--  lem : ∀ a b → rel a b → rel (finv a) (finv b)
--  lem a b (u , v , y , p , q) = (finv v , finv u , y , p' , q')
--        where
--          p' = finv a ≡⟨ cong (finv) p ⟩
--               finv (u ++ y ∷ inv y ∷ v) ≡⟨ ++-finv-hom u ([ y ] ++ [ inv y ] ++ v) ⟩
--               finv ([ y ] ++ [ inv y ] ++ v) ++ finv u ≡⟨ cong (λ z → ((finv z) ++ (finv u))) (sym (++-assoc [ y ] [ inv y ] v)) ⟩
--               finv (([ y ] ++ [ inv y ]) ++ v) ++ finv u ≡⟨ cong (λ z → z ++ finv u) (++-finv-hom ([ y ] ++ [ inv y ]) v) ⟩
--               (finv v ++ [ inv (inv y) ] ++ [ inv y ]) ++ finv u ≡⟨ cong (λ z → (finv v ++ [ z ] ++ [ inv y ]) ++ finv u) (inv-invol y) ⟩
--               (finv v ++ [ y ] ++ [ inv y ]) ++ finv u ≡⟨ ++-assoc (finv v) ([ y ] ++ [ inv y ]) (finv u) ⟩
--               finv v ++ [ y ] ++ [ inv y ] ++ finv u     ∎
--          q' = finv b ≡⟨ cong finv q ⟩
--               finv (u ++ v) ≡⟨ ++-finv-hom u v ⟩
--               finv v ++ finv u ∎

  rel-ex-inv : ∀ a b → rel-ex a b → rel-ex (finv a) (finv b)
  rel-ex-inv a b (u , v , x , inl(p , q)) = finv v , finv u , x , inl(p' , q')
    where
      p' = finv a ≡⟨ cong (finv) p ⟩
           finv (u ++ x ++ finv x ++ v) ≡⟨ ++-finv-hom u (x ++ finv x ++ v) ⟩
           finv (x ++ finv x ++ v) ++ finv u ≡⟨ cong (λ z → z ++ finv u) (++-finv-hom x (finv x ++ v))⟩
           (finv (finv x ++ v) ++ finv x) ++ finv u ≡⟨ ++-assoc (finv (finv x ++ v)) (finv x) (finv u) ⟩
           finv (finv x ++ v) ++ finv x ++ finv u ≡⟨ cong (λ a → a ++ (finv x) ++ (finv u)) (++-finv-hom (finv x) v) ⟩
           (finv v ++ finv (finv x)) ++ finv x ++ finv u ≡⟨ ++-assoc (finv v) (finv (finv x)) (finv x ++ finv u) ⟩
           finv v ++ finv (finv x) ++ finv x ++ finv u ≡⟨ cong (λ a → finv v ++ a ++ finv x ++ finv u) (finv-invol (x)) ⟩
           finv v ++ x ++ finv x ++ finv u ∎
      q' = finv b ≡⟨ cong (finv) q ⟩ finv (u ++ v) ≡⟨ ++-finv-hom u v ⟩ finv v ++ finv u ∎
  rel-ex-inv a b (u , v , x , inr(p , q)) = finv v , finv u , x , inr(p' , q')
    where
      p' = finv b ≡⟨ cong (finv) p ⟩
           finv (u ++ x ++ finv x ++ v) ≡⟨ ++-finv-hom u (x ++ finv x ++ v) ⟩
           finv (x ++ finv x ++ v) ++ finv u ≡⟨ cong (λ z → z ++ finv u) (++-finv-hom x (finv x ++ v))⟩
           (finv (finv x ++ v) ++ finv x) ++ finv u ≡⟨ ++-assoc (finv (finv x ++ v)) (finv x) (finv u) ⟩
           finv (finv x ++ v) ++ finv x ++ finv u ≡⟨ cong (λ a → a ++ (finv x) ++ (finv u)) (++-finv-hom (finv x) v) ⟩
           (finv v ++ finv (finv x)) ++ finv x ++ finv u ≡⟨ ++-assoc (finv v) (finv (finv x)) (finv x ++ finv u) ⟩
           finv v ++ finv (finv x) ++ finv x ++ finv u ≡⟨ cong (λ a → finv v ++ a ++ finv x ++ finv u) (finv-invol (x)) ⟩
           finv v ++ x ++ finv x ++ finv u ∎
      q' = finv a ≡⟨ cong (finv) q ⟩ finv (u ++ v) ≡⟨ ++-finv-hom u v ⟩ finv v ++ finv u ∎

  -FG_ : FG → FG
  -FG ∥ a ∥ = ∥ finv a ∥
  -FG eq/ a b r i = eq/ (finv a) (finv b) (rel-ex-inv a b r) i
  -FG squash/ x y p q i j = squash/ (-FG x) (-FG y) (cong (λ z → -FG z) p) (cong (λ z → -FG z) q) i j

  inv-invl-lem : ∀ x → rel ([ inv x ] ++  [ x ]) []
  inv-invl-lem x  = ([] , [] , inv x , p , refl)
    where
      p :  [ inv x ] ++ [ x ] ≡ [] ++ [ inv x ] ++ [ inv (inv x) ] ++ []
      p = [] ++ [ inv x ] ++ [ x ] ≡⟨ cong (λ z → [] ++ [ inv x ] ++ [ z ]) (sym (inv-invol x)) ⟩
          inv x ∷ [ inv (inv x) ] ≡⟨ sym (++-unit-r (inv x ∷ [ inv (inv x) ])) ⟩
          inv x ∷ inv (inv x) ∷ [] ∎

  inv-invr-lem : ∀ x → rel ([ x ] ++  [ inv x ]) []
  inv-invr-lem x  = ([] , [] , x , refl , refl)

  finv-invr : ∀ x → rel-ex (x ++ finv x) []
  finv-invr [] = [] , [] , [] , inl(refl , refl)
  finv-invr (x ∷ xs) = [] , [] , x ∷ xs , inl( p , refl )
    where
      p : x ∷ xs ++ finv xs ++ [ inv x ] ≡ x ∷ xs ++ (finv xs ++ [ inv x ]) ++ []
      p = x ∷ xs ++ finv xs ++ [ inv x ] ≡⟨ sym(++-unit-r (x ∷ xs ++ finv xs ++ [ inv x ])) ⟩
          (x ∷ xs ++ finv xs ++ [ inv x ]) ++ [] ≡⟨ ++-assoc (x ∷ xs ) (finv xs ++ [ inv x ]) [] ⟩
          (x ∷ xs) ++ (finv xs ++ [ inv x ]) ++ [] ∎

  finv-invl : ∀ x → rel-ex (finv x ++ x) []
  finv-invl [] = [] , [] , [] , inl(refl , refl)
  finv-invl (x ∷ xs) = [] , [] , finv (x ∷ xs) , inl( p , refl )
    where
      p : finv (x ∷ xs) ++ x ∷ xs ≡ finv (x ∷ xs) ++ finv (finv (x ∷ xs)) ++ []
      p = finv (x ∷ xs) ++ x ∷ xs ≡⟨ cong (λ a → finv (x ∷ xs) ++ a ) (sym (finv-invol (x ∷ xs))) ⟩
          finv (x ∷ xs) ++ finv (finv (x ∷ xs)) ≡⟨ sym(++-unit-r (finv (x ∷ xs) ++ finv (finv (x ∷ xs)))) ⟩
          (finv (x ∷ xs) ++ finv (finv (x ∷ xs))) ++ [] ≡⟨ ++-assoc (finv (x ∷ xs)) (finv (finv (x ∷ xs))) [] ⟩
          finv (x ∷ xs) ++ finv (finv (x ∷ xs)) ++ [] ∎

  -FG-inv-r : ∀ x → x + (-FG x) ≡ ∥ [] ∥
  -FG-inv-r = SetQuotients.elimProp (λ x → FG-isSet (x + (-FG x)) (∥ [] ∥))
              (λ x → eq/ (x ++ finv x) ([]) (finv-invr x))

  -FG-inv-l : ∀ x → (-FG x) + x ≡ ∥ [] ∥
  -FG-inv-l = SetQuotients.elimProp (λ x → FG-isSet ((-FG x) + x) (∥ [] ∥))
              (λ x → eq/ (finv x ++ x) ([]) (finv-invl x))

module FGVsHITGro {A : Type₀} (AIsSet : isSet A) where
  open FGByList {A = A} AIsSet

  toFG : HITGro A → FG
  toFG ⟨ x ⟩ = ∥ [ (true , x) ] ∥
  toFG :ε: = ∥ [] ∥
  toFG (x :∘: y) = (toFG x) + (toFG y)
  toFG (:-: x) = -FG (toFG x)
  toFG (:unit-l: x i) = +-unit-l (toFG x) i
  toFG (:unit-r: x i) = +-unit-r (toFG x) i
  toFG (:inv-l: x i) = -FG-inv-l (toFG x) i
  toFG (:inv-r: x i) = -FG-inv-r (toFG x) i
  toFG (:assoc: x y z i) = FG+-assoc (toFG x) (toFG y) (toFG z) i
  toFG (trunc x y p q i j) = FG-isSet (toFG x) (toFG y) (λ k → toFG (p k)) (λ k → toFG (q k)) i j

  private
    fromFA : FA → HITGro A
    fromFA [] = :ε:
    fromFA ((false , x) ∷ xs) = (:-: ⟨ x ⟩) :∘: (fromFA xs)
    fromFA ((true , x) ∷ xs) = ⟨ x ⟩ :∘: (fromFA xs)

    inv→inv : (x : X) → fromFA ([ x ] ++ [ inv x ]) ≡ :ε:
    inv→inv (true , x) = (⟨ x ⟩) :∘: ((:-: ⟨ x ⟩) :∘: :ε:) ≡⟨ sym(:assoc: ⟨ x ⟩ (:-: ⟨ x ⟩) :ε:)  ⟩
                         (⟨ x ⟩ :∘: (:-: ⟨ x ⟩)) :∘: :ε: ≡⟨ :unit-r: (⟨ x ⟩ :∘: (:-: ⟨ x ⟩)) ⟩
                         ⟨ x ⟩ :∘: (:-: ⟨ x ⟩) ≡⟨ :inv-r: ⟨ x ⟩ ⟩
                         :ε: ∎
    inv→inv (false , x) = {!!}

    finv-inv : (x : FA) → (fromFA x) :∘: (fromFA (finv x)) ≡ :ε:
    finv-inv [] = :unit-l: :ε:
    finv-inv ((true , x) ∷ xs) = :assoc: (⟨ x ⟩) (fromFA xs) (fromFA (finv ((true , x) ∷ xs))) ∙ {!!}
    finv-inv ((false , x) ∷ xs) = {!!}

  fromFG : FG → HITGro A
  fromFG ∥ [] ∥ = fromFA []
  fromFG ∥ x ∷ xs ∥ = fromFA (x ∷ xs)
  fromFG (eq/ a b r i) = {!!}
  fromFG (squash/ x y p q i j) = trunc (fromFG x) (fromFG y) (λ k → fromFG (p k)) (λ k → fromFG (q k)) i j
