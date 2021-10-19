{-# OPTIONS --cubical #-}

module Sym where

open import Agda.Builtin.Cubical.Path
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
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

rm : {n : ℕ} (f : Fin (suc n) → Fin (suc n)) → isEmbedding f → Fin n → Fin n
rm {n} f e j' with inspect (f fzero) | inspect (f (fsuc j'))
... | (zero , i<sn) , f0≡i | (zero , j<sn) , fsj'≡j = ⊥.rec (znots (cong fst (invEq (_ , e fzero (fsuc j')) (f0≡i ∙ sym (Fin≡ (cong fst fsj'≡j)))))) -- both zero and s j' are sent to 0: impossible because f is an embedding
... | (zero , i<sn) , f0≡i | (suc j , j<sn) , fsj'≡j = j , (fst j<sn , +-suc _ _ ∙ injSuc (cong suc (sym (+-suc _ _)) ∙ sym (+-suc _ _) ∙ snd j<sn))
... | (suc i , (k , p)) , f0≡i | (zero , j<sn) , fsj'≡j = zero , (k + i , ((sym (+-assoc k i 1)) ∙ (cong (λ a → k + a) (+-comm i 1))) ∙ injSuc(sym(+-suc k (suc i)) ∙ p))
... | (suc i , (k , p)) , f0≡i | (suc j , j<sn) , fsj'≡j = zero , (k + i , ((sym (+-assoc k i 1)) ∙ (cong (λ a → k + a) (+-comm i 1))) ∙ injSuc(sym(+-suc k (suc i)) ∙ p))

rm≃ : {n : ℕ} (e : S (suc n)) → Fin n ≃ Fin n
rm≃ e = {!!}

-- -- TODO: "remove" (f 0)-th element
-- rm-≃ : {n : ℕ} → S (suc n) → S n
-- rm-≃ = {!!}

-- S→nf : {n : ℕ} → S n → nf n
-- S→nf {zero} f = tt
-- S→nf {suc n} f = fst f fzero , S→nf {n} (rm-≃ f)

-- -- send 0-th element to i and leave others untouched
send : {n : ℕ} → Fin n → Fin n → Fin n
send {n} (zero , i<n) (j , j<n) = j , j<n
send {zero} (suc i , i<n) (j , j<n) = ⊥.rec (¬-<-zero j<n)
send {suc n} (suc i , i<n) (zero , j<n) = zero , j<n
send {suc n} (suc i , i<n) (suc j , j<n) = fsuc (send {n} (i , pred-≤-pred i<n) (j , (pred-≤-pred j<n)))

-- -- TODO: not easy, or we could define the inverse?
send² : {n : ℕ} (i j : Fin n) → send i (send i j) ≡ j
send² {n} (zero , i<n) (j , j<n) = refl
send² {zero} (suc i , i<n) (j , j<n) = ⊥.rec (¬-<-zero j<n)
send² {suc n} (suc i , i<n) (zero , j<n) = refl
send² {suc n} (suc i , i<n) (suc j , j<n) = {!cong fsuc ?!}

send≃ : {n : ℕ} → (i : Fin n) → S n
send≃ {n} i = isoToEquiv (iso (send i) (send i) (send² i) (send² i))

-- Fin-id : (n : ℕ) → Fin n ≃ Fin n
-- Fin-id n = isoToEquiv (iso f f (λ _ → refl) λ _ → refl)
  -- where
  -- f : Fin n → Fin n
  -- f x = x

-- Fin-lift-fun : {m n : ℕ} → (Fin m → Fin n) → Fin (suc m) → Fin (suc n)
-- Fin-lift-fun f (zero , i<m) = zero , suc-≤-suc zero-≤
-- Fin-lift-fun f (suc i , i<m) = fsuc (f (i , (pred-≤-pred i<m)))

-- -- equivalence sending 0 to 0 and behaving as e otherwise
-- cong-fsuc-≃ : {n : ℕ} → Fin n ≃ Fin n → Fin (suc n) ≃ Fin (suc n)
-- cong-fsuc-≃ {n} e = isoToEquiv (iso f g f-g g-f)
  -- where
  -- f : Fin (suc n) → Fin (suc n)
  -- f = Fin-lift-fun (fst e)
  -- g : Fin (suc n) → Fin (suc n)
  -- g = Fin-lift-fun (invEq e)
  -- g-f : (i : Fin (suc n)) → g (f i) ≡ i
  -- g-f (zero , i<sn) = ΣPathP (refl , m≤n-isProp _ _)
  -- g-f (suc i , i<sn) = ΣPathP ((cong suc {!!}) , m≤n-isProp _ _) -- should be easy by induction
  -- f-g : (i : Fin (suc n)) → f (g i) ≡ i
  -- f-g = {!!} -- similar as above

-- nf→S : {n : ℕ} → nf n → S n
-- nf→S {zero} tt = Fin-id 0
-- nf→S {suc n} (i , f) = compEquiv (send≃ i) (cong-fsuc-≃ (nf→S f))

-- S-nf-S : {n : ℕ} (f : S n) → nf→S (S→nf f) ≡ f
-- S-nf-S e@(f , _) = equivEq (nf→S (S→nf e)) e (funExt (λ j → {!!}))

-- nf-S-nf : {n : ℕ} (f : nf n) → S→nf (nf→S f) ≡ f
-- nf-S-nf {zero} tt = refl
-- nf-S-nf {suc n} (i , f) = {!!}

-- -- S≃nf : (n : ℕ) → S n ≃ nf n
-- -- S≃nf n = isoToEquiv (iso S→nf nf→S nf-S-nf S-nf-S)

S0≃Unit : S 0 ≃ Unit
S0≃Unit = isoToEquiv (iso (λ _ → tt) (λ _ → idEquiv (Fin 0)) (λ { tt → refl }) (λ e → equivEq (funExt λ { (i , i<0) → ⊥.rec (¬-<-zero i<0) })))

Ss : (n : ℕ) → S (suc n) ≃ Fin (suc n) × S n
Ss n = isoToEquiv (iso f g {!!} {!!})
  where
  f : S (suc n) → Fin (suc n) × S n
  f e = (fst e fzero) , rm≃ e
  g : Fin (suc n) × S n → S (suc n)
  g (i , e) = send≃ i

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
  inv  : {n : ℕ} (i : Fin n) (s : Sym (2 + n)) → swap i (swap i s) ≡ s
  xchg : {n : ℕ} (i j : Fin n) → 2 + fst i ≤ fst j → (s : Sym (2 + n)) → swap i (swap j s) ≡ swap j (swap i s)
  yb   : {n : ℕ} (i : Fin n) (s : Sym (3 + n)) → swap (fweak i) (swap (fsuc i) (swap (fweak i) s)) ≡ swap (fsuc i) (swap (fweak i) (swap (fsuc i) s))
  set  : {n : ℕ} → isSet (Sym n)

thm : {n : ℕ} → Sym n ≃ nf n
thm = {!!}
