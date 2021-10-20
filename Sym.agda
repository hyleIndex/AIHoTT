{-# OPTIONS --cubical #-}

module Sym where

open import Agda.Builtin.Cubical.Path
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels hiding (extend)
open import Cubical.Functions.Embedding
open import Cubical.HITs.SetTruncation
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order as Order
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

---
--- General lemmas
---

_≢_ : {ℓ : Level} {A : Type ℓ} → A → A → Type ℓ
x ≢ y = ¬ (x ≡ y)

id : {ℓ : Level} {A : Type ℓ} → A → A
id x = x

pair≡ : {ℓ : Level} {A B : Type ℓ} {a a' : A} {b b' : B} → a ≡ a' → b ≡ b' → (a , b) ≡ (a' , b')
pair≡ p q i = p i , q i

≤-dec : (m n : ℕ) → Dec (m ≤ n)
≤-dec zero n = yes (n , +-zero n)
≤-dec (suc m) zero = no ¬-<-zero
≤-dec (suc m) (suc n) with ≤-dec m n
... | yes p = yes (suc-≤-suc p)
... | no ¬p = no λ p → ¬p (pred-≤-pred p)

<-dec : (m n : ℕ) → Dec (m < n)
<-dec m n = ≤-dec (suc m) n

-- TODO: by trichotomy
¬<-≥ : {m n : ℕ} → ¬ (m < n) → n ≤ m
¬<-≥ {m = m} {n = n} p = {!!}

≤-≢-< : {m n : ℕ} → m ≤ n → m ≢ n → m < n
≤-≢-< {m = m} {n = n} (zero , p) q = ⊥.elim(q p)
≤-≢-< {m = m} {n = n} (suc x , p) q = x , +-suc x m ∙ p

<-≢ : {m n : ℕ} → m < n → m ≢ n
<-≢ {m = m} {n = n} p q = ¬m<m (subst (_< n) q p)

<-<-suc : {m n o : ℕ} → m < n → n < suc o → m < o
<-<-suc {m = m} {n = n} {o = o} (x , p) (y , q) = (x + y) , p'
  where
    p' = x + y + suc m ≡⟨ cong (λ a → a + suc m) (+-comm x y) ⟩
         y + x + suc m ≡⟨ sym(+-assoc y x (suc m)) ⟩
         y + (x + suc m) ≡⟨ cong (λ a → y + a) p ⟩
         y + n ≡⟨ injSuc ((sym (+-suc y n) ∙ q)) ⟩ o ∎

inspect : {ℓ : Level} {A : Type ℓ} (x : A) → singl x
inspect x = x , refl

Fin≡ : {k : ℕ} {m n : Fin k} → fst m ≡ fst n → m ≡ n
Fin≡ {k} {m} {n} p i = (p i) , q i
  where
  q : PathP (λ i → p i < k) (snd m) (snd n)
  q = toPathP (m≤n-isProp _ _)

Fin' : {n : ℕ} (i : Fin n) → Type₀
Fin' {n} i = Σ (Fin n) (λ j → j ≢ i)

toFin : {n : ℕ}{i : Fin n} → Fin' i → Fin n
toFin = fst

toFin-inj : {n : ℕ}{i : Fin n} → {j k : Fin' i} → toFin j ≡ toFin k → j ≡ k
toFin-inj = Σ≡Prop (λ _ → isPropΠ λ _ → ⊥.isProp⊥)

-- one inclusion of Fin into the next (the canonical one being fsuc)
fweak : {n : ℕ} (i : Fin n) → Fin (suc n)
fweak (zero , i<n) = zero , suc-≤-suc zero-≤
fweak (suc i , i<n) = suc i , suc-≤-suc (≤-trans (≤-suc ≤-refl) i<n)

---
--- Let's go
---

-- the symmetric group
S : (n : ℕ) → Type₀
S n = Fin n ≃ Fin n

-- normal form for symmetries
nf : ℕ → Type₀
nf zero    = Unit
nf (suc n) = Fin (suc n) × nf n

nf-isSet : {n : ℕ} → isSet (nf n)
nf-isSet {zero} = isProp→isSet isPropUnit
nf-isSet {suc n} = isSet× isSetFin nf-isSet

-- -- remove 0-th element
-- -- rm : {n : ℕ} → Fin (suc n) → Fin (suc n) → Fin n → Fin n
-- -- rm {n} f j' with f fzero | f (fsuc j')
-- -- rm {n} f j' | zero , i<sn | zero , j<sn = {!!}
-- -- rm {n} f j' | zero , i<sn | suc j , j<sn = {!!}
-- -- rm {n} f j' | suc i , i<sn | j , j<sn = {!!}

Fin-rm : {n : ℕ} (i : Fin (suc n)) → Σ (Fin (suc n)) (λ j → j ≢ i) ≃ Fin n
Fin-rm {n} (i , i<sn) = isoToEquiv (iso f g {!!} {!!})
  where
  f : Σ (Fin (suc n)) (λ j → j ≢ (i , i<sn)) → Fin n
  f ((j , j<sn) , j≢i) with <-dec i j
  f ((zero , j<sn) , j≢i) | yes i<j = ⊥.rec (¬-<-zero i<j)
  f ((suc j , j<sn) , j≢i) | yes i<j = j , pred-≤-pred j<sn
  f ((j , j<sn) , j≢i) | no ¬i<j = j , <-<-suc (≤-≢-< (¬<-≥ ¬i<j) (λ p → j≢i (Fin≡ p))) i<sn
  g : Fin n → Σ (Fin (suc n)) (λ j → j ≢ (i , i<sn))
  g (j , j<sn) with <-dec j i
  g (j , j<sn) | yes j<i = (j , ≤-trans j<sn (≤-suc ≤-refl)) , λ p → <-≢ j<i (cong fst p)
  g (j , j<sn) | no ¬j<i = (suc j , suc-≤-suc j<sn) , λ p → ¬j<i (0 , cong fst p)
  f-g : (j : Fin n) → f (g j) ≡ j
  f-g (j , j<n) with <-dec j i
  f-g (j , j<n) | yes p = {!!}
  f-g (j , j<n) | no ¬p = {!!}
  g-f : (x : Σ (Fin (suc n)) (λ j → j ≢ (i , i<sn))) → g (f x) ≡ x
  g-f (j , j≢i) = ΣPathP (g-f-fst (j , j≢i) , toPathP (funExt λ _ → isProp⊥ _ _))
    where
    g-f-fst : (j : Σ (Fin (suc n)) (λ j → j ≢ (i , i<sn))) → fst (g (f j)) ≡ fst j
    g-f-fst ((j , j<sn) , j≢i) with <-dec i j
    ... | yes p = {!!}
    ... | no ¬p = {!!}

-- the equivalence e without i in the input and e i in the output
restrict : {n : ℕ} (e : S (suc n)) (i : Fin (suc n)) → Fin' {suc n} i ≃ Fin' {suc n} (fst e i)
restrict {n} e i = isoToEquiv (iso f g {!!} {!!})
  where
  f : Fin' i → Fin' (fst e i)
  f (j , j<sn) = fst e j , λ p → j<sn ((sym (retEq e j)) ∙ (cong (invEq e) p) ∙ (retEq e i))
  g : Fin' (fst e i) → Fin' i
  g (j , j<sn) = invEq e j , λ p → j<sn ((sym (secEq e j)) ∙ cong (fst e) p)
  f-g : ∀ n → f (g n) ≡ n
  f-g (j , j<sn) = {!!}
  g-f : ∀ n → g (f n) ≡ n
  g-f (j , j<sn) = {!!}

rm≃ : {n : ℕ} (e : S (suc n)) → Fin n ≃ Fin n
rm≃ {n} e =
  Fin n ≃⟨ invEquiv (Fin-rm fzero) ⟩
  Σ (Fin (suc n)) (λ j → j ≢ fzero) ≃⟨ restrict e fzero ⟩
  Σ (Fin (suc n)) (λ j → j ≢ fst e fzero) ≃⟨ Fin-rm (fst e fzero) ⟩
  Fin n ■

-- like e but shifted by +1
shift≃ : {n : ℕ} → S n → S (suc n)
shift≃ {n} e = isoToEquiv (iso f g {!!} {!!})
  where
  f : Fin (suc n) → Fin (suc n)
  f (zero , i<sn) = zero , i<sn
  f (suc i , i<sn) = fsuc (fst e (i , (pred-≤-pred i<sn)))
  g : Fin (suc n) → Fin (suc n)
  g (zero , i<sn) = zero , i<sn
  g (suc i , i<sn) = fsuc (invEq e (i , (pred-≤-pred i<sn)))
  f-g : ∀ n → f (g n) ≡ n
  f-g (j , j<sn) = {!!}

-- -- TODO: "remove" (f 0)-th element
-- rm-≃ : {n : ℕ} → S (suc n) → S n
-- rm-≃ = {!!}

-- S→nf : {n : ℕ} → S n → nf n
-- S→nf {zero} f = tt
-- S→nf {suc n} f = fst f fzero , S→nf {n} (rm-≃ f)

-- send 0-th element to i and leave others untouched
-- SM : note, it might be easier to generalize to sending i to j, because the
-- inverse is also of this form
send : {n : ℕ} → Fin n → Fin n → Fin n
send {n} (zero , i<n) (j , j<n) = j , j<n
send {zero} (suc i , i<n) (j , j<n) = ⊥.rec (¬-<-zero j<n)
send {suc n} (suc i , i<n) (zero , j<n) = zero , j<n
send {suc n} (suc i , i<n) (suc j , j<n) = fsuc (send {n} (i , pred-≤-pred i<n) (j , (pred-≤-pred j<n)))

-- TODO: not easy, or we could define the inverse?
send² : {n : ℕ} (i j : Fin n) → send i (send i j) ≡ j
send² {n} (zero , i<n) (j , j<n) = refl
send² {zero} (suc i , i<n) (j , j<n) = ⊥.rec (¬-<-zero j<n)
send² {suc n} (suc i , i<n) (zero , j<n) = refl
send² {suc n} (suc i , i<n) (suc j , j<n) = {!cong fsuc ?!}

send≃ : {n : ℕ} → (i : Fin n) → S n
send≃ {n} i = isoToEquiv (iso (send i) (send i) (send² i) (send² i))

S0≃Unit : S 0 ≃ Unit
S0≃Unit = isoToEquiv (iso (λ _ → tt) (λ _ → idEquiv (Fin 0)) (λ { tt → refl }) (λ e → equivEq (funExt λ { (i , i<0) → ⊥.rec (¬-<-zero i<0) })))

Ss : (n : ℕ) → S (suc n) ≃ Fin (suc n) × S n
Ss n = isoToEquiv (iso f g {!!} {!!})
  where
  f : S (suc n) → Fin (suc n) × S n
  f e = (fst e fzero) , rm≃ e
  g : Fin (suc n) × S n → S (suc n)
  g (i , e) = compEquiv (shift≃ e) (send≃ i)

S≃nf : (n : ℕ) → S n ≃ nf n
S≃nf zero = S0≃Unit
S≃nf (suc n) =
  S (suc n) ≃⟨ Ss n ⟩
  Fin (suc n) × S n ≃⟨ cong≃ (λ A → Fin (suc n) × A) (S≃nf n) ⟩
  Fin (suc n) × nf n ■

---
--- Comparison with Bij
---

-- presentation of Bij n
data Sym : ℕ → Type₀ where
  nop : {n : ℕ} → Sym n
  -- exchange braids i and i+1
  swap : {n : ℕ} (i : Fin n) → Sym (2 + n) → Sym (2 + n)
  -- quotient
  inv  : {n : ℕ} (i : Fin n) (s : Sym (2 + n)) → swap i (swap i s) ≡ s
  xchg : {n : ℕ} (i j : Fin n) → 2 + fst i ≤ fst j → (s : Sym (2 + n)) → swap i (swap j s) ≡ swap j (swap i s)
  yb   : {n : ℕ} (i : Fin n) (s : Sym (3 + n)) → swap (fweak i) (swap (fsuc i) (swap (fweak i) s)) ≡ swap (fsuc i) (swap (fweak i) (swap (fsuc i) s))
  set  : {n : ℕ} → isSet (Sym n)

Sym→S : {n : ℕ} → Sym n → S n
Sym→S = {!!}

Sym→nf : {n : ℕ} → Sym n → nf n
Sym→nf {n} e = fst (S≃nf n) (Sym→S e)

nf→Sym : {n : ℕ} → nf n → Sym n
nf→Sym = {!!}

thm : {n : ℕ} → Sym n ≃ nf n
thm = {!!}
