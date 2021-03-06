{-# OPTIONS --cubical #-}

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
open import Cubical.Data.Fin hiding (_/_)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq
open import Cubical.Data.List
open import Cubical.Data.Fin.LehmerCode renaming (_∷_ to _::_)
open import Cubical.HITs.SetQuotients as SetQuotients renaming( [_] to ∥_∥ )

fweak : {n : ℕ} (i : Fin n) → Fin (suc n)
fweak (zero , i<n) = zero , suc-≤-suc zero-≤
fweak (suc i , i<n) = suc i , suc-≤-suc (≤-trans (≤-suc ≤-refl) i<n)

_↓_ : (n : ℕ) → (k : ℕ) → List ℕ
n ↓ zero = []
n ↓ suc k = (k + n) ∷ (n ↓ k)

data _∼'_ {m : ℕ} : List (Fin (suc m)) → List (Fin (suc m)) → Type₀ where
    swap : {n : Fin (suc m)} {k : Fin (suc m)} → (suc (k .fst) < (n .fst)) → (n ∷ k ∷ []) ∼' (k ∷ n ∷ [])
    braid : {n : Fin m} → (fsuc n ∷ fweak n ∷ fsuc n ∷ []) ∼' (fweak n ∷ fsuc n ∷ fweak n ∷ [])
    cancel : {n : Fin (suc m)} → (n ∷ n ∷ []) ∼' []

data _∼_ : {m : ℕ} → List (Fin m) → List (Fin m) → Type₀ where
    id : {m : ℕ} {l : List (Fin m)} → l ∼ l
    rel : {m : ℕ} {l1 l2 : List (Fin (suc m))} → l1 ∼' l2 →  l1 ∼ l2
    Symmetry : {m : ℕ} {l1 l2 : List (Fin m)} → (l1 ∼ l2) → l2 ∼ l1
    trans : {m : ℕ} {l1 l2 l3 : List (Fin m)} → (l1 ∼ l2) → (l2 ∼ l3) → l1 ∼ l3
    ++-hom : {m : ℕ} {l l' r r' : List (Fin m)} → (l ∼ l') → (r ∼ r') → (l ++ r) ∼ (l' ++ r')

data _~_ : List ℕ → List ℕ → Type₀ where
  cancel~ : {n : ℕ} → (l r m mf : List ℕ) → (defm : m ≡ l ++ n ∷ n ∷ r) → (defmf : mf ≡ l ++ r) → (m ~ mf)
  swap~ : {n : ℕ} → {k : ℕ} → (suc k < n) →  (l r m mf : List ℕ) → (defm : m ≡ l ++ n ∷ k ∷ r) → (defmf : mf ≡ l ++ k ∷ n ∷ r) → (m ~ mf)
  long~ : {n : ℕ} → (k : ℕ) → (l r m mf : List ℕ) → (defm : m ≡ l ++ (n ↓ (2 + k)) ++ (1 + k + n) ∷ r) → (defmf : mf ≡ l ++ (k + n) ∷ (n ↓ (2 + k)) ++ r) → (m ~ mf)

data _~*_ : List ℕ → List ℕ → Type₀ where
  id : {m : List ℕ} → m ~* m
  trans~ : {m1 m2 m3 : List ℕ} → (m1 ~ m2) → (m2 ~* m3) → m1 ~* m3

data _~+_ : List ℕ → List ℕ → Type₀ where
  trans~ : {m1 m2 m3 : List ℕ} → (m1 ~ m2) → (m2 ~* m3) → m1 ~+ m3

swap-~ : {n : ℕ} → {k : ℕ} → (pk : suc k < n) →  (l r : List ℕ) → (l ++ n ∷ k ∷ r) ~* (l ++ k ∷ n ∷ r)
swap-~ {k} {n} pk l r = trans~ (swap~ pk l r (l ++ k ∷ _ ∷ r) (l ++ _ ∷ k ∷ r) refl refl) id

long : {n : ℕ} → (k : ℕ) → (l r : List ℕ) → (l ++ (n ↓ (2 + k)) ++ (1 + k + n) ∷ r) ~* (l ++ (k + n) ∷ (n ↓ (2 + k)) ++ r)
long k l r = trans~ (long~ k l r _ _ refl refl) id

braid-~ : {n : ℕ} → (l r : List ℕ) → (l ++ (suc n) ∷ n ∷ (suc n) ∷ r) ~* (l ++ n ∷ suc n ∷ n ∷ r)
braid-~ {n} l r = long {n} 0 l r

trans-~ : {m1 m2 m3 : List ℕ} → (m1 ~* m2) → (m2 ~* m3) → m1 ~* m3
trans-~ id p  = p
trans-~ (trans~ x q) p = trans~ x (trans-~ q p)

add-l-lem : (m1 m2 l : List ℕ) → m1 ~ m2 → (l ++ m1) ~ (l ++ m2)
add-l-lem m1 m2 l (cancel~ l₁ r .m1 .m2 defm defmf) = cancel~ (l ++ l₁) r _ _ (cong (λ k → (l ++ k)) defm ∙ sym(++-assoc l l₁ _)) (cong (λ k → (l ++ k)) defmf ∙ sym(++-assoc l l₁ _))
add-l-lem m1 m2 l (swap~ x l₁ r .m1 .m2 defm defmf) = swap~ x (l ++ l₁) r _ _ (cong (λ k → (l ++ k)) defm ∙ sym(++-assoc l l₁ _)) (cong (λ k → (l ++ k)) defmf ∙ sym(++-assoc l l₁ _))
add-l-lem m1 m2 l (long~ k l₁ r .m1 .m2 defm defmf) = long~ k (l ++ l₁) r _ _ (cong (λ k → (l ++ k)) defm ∙ sym(++-assoc l l₁ _)) (cong (λ k → (l ++ k)) defmf ∙ sym(++-assoc l l₁ _))

add-l : (m1 m2 l : List ℕ) → m1 ~* m2 → (l ++ m1) ~* (l ++ m2)
add-l m1 .m1 l id = _~*_.id
add-l m1 m2 l (trans~ {m2 = m3} x p) = trans~ (add-l-lem m1 m3 l x) (add-l m3 m2 l p)

add-r-lem : (m1 m2 l : List ℕ) → m1 ~ m2 → (m1 ++ l) ~ (m2 ++ l)
add-r-lem m1 m2 r (cancel~ l r₁ .m1 .m2 defm defmf) = cancel~ l (r₁ ++ r) _ _ (cong (λ k → (k ++ r)) defm ∙ ++-assoc l _ r) (cong (λ k → (k ++ r)) defmf ∙ ++-assoc l _ r)
add-r-lem m1 m2 r (swap~ x l r₁ .m1 .m2 defm defmf) = swap~ x l (r₁ ++ r) _ _  (cong (λ k → (k ++ r)) defm ∙ ++-assoc l _ r) (cong (λ k → (k ++ r)) defmf ∙ ++-assoc l _ r)
add-r-lem m1 m2 r (long~ k l r₁ .m1 .m2 defm defmf) = long~ k l (r₁ ++ r) _ _  (cong (λ k → (k ++ r)) defm ∙ ++-assoc l _ r ∙ cong₂ _++_ (refl {x = l}) (cong₂ _∷_ refl (cong₂ _∷_ refl (++-assoc (_ ↓ k) _ r)))) 
                                                                                (cong (λ k → (k ++ r)) defmf ∙ ++-assoc l _ r ∙ cong₂ _++_ (refl {x = l}) (cong₂  _∷_ refl (cong₂ _∷_ refl (cong₂ _∷_  refl (++-assoc _ r₁ r)))))

add-r : (m1 m2 l : List ℕ) → m1 ~* m2 → (m1 ++ l) ~* (m2 ++ l)
add-r m1 .m1 r id = _~*_.id
add-r m1 m2 r (trans~ {m2 = m3} x p) = trans~ (add-r-lem m1 m3 r x) (add-r m3 m2 r p)

¬nil~cons : {x : ℕ} → ¬ ((x ∷ []) ~ [])
¬nil~cons (cancel~ [] r .(_ ∷ []) .[] defm defmf) = ¬nil≡cons (cons-inj₂ defm)
¬nil~cons (cancel~ (x ∷ l) r .(_ ∷ []) .[] defm defmf) = ¬nil≡cons defmf
¬nil~cons (swap~ x [] r .(_ ∷ []) .[] defm defmf) = ¬nil≡cons defmf
¬nil~cons (swap~ x (x₁ ∷ l) r .(_ ∷ []) .[] defm defmf) = ¬nil≡cons defmf
¬nil~cons (long~ k [] r .(_ ∷ []) .[] defm defmf) = ¬nil≡cons defmf
¬nil~cons (long~ k (x ∷ l) r .(_ ∷ []) .[] defm defmf) = ¬nil≡cons defmf

Sym : (n : ℕ) → Type₀
Sym n = (List (Fin n)) / (_∼_ {n})

_-ℕ_ : ℕ → ℕ → ℕ
m -ℕ 0 = m
0 -ℕ (suc n) = 0
(suc m) -ℕ (suc n) = m -ℕ n

-ℕ-cancelˡ : ∀ k m n → (k + m) -ℕ (k + n) ≡ m -ℕ n
-ℕ-cancelˡ zero    = λ _ _ → refl
-ℕ-cancelˡ (suc k) = -ℕ-cancelˡ k

-- decode LehmerCode to a series of transposition

LehmerCode→Trans : {n : ℕ} → (LehmerCode n) → List ℕ
LehmerCode→Trans {zero} x = []
LehmerCode→Trans {suc n} ((j , j<sn) :: xs) = LehmerCode→Trans xs ++ (((suc n) -ℕ j) ↓ j)

-- all the element in List l is smaller then n, using this definition we can get the inequality.

data _>L_ : ℕ → List ℕ → Type₀ where
  largerThenEmpty : {n : ℕ} → n >L []
  _:⟨_⟩:_ : {n : ℕ} → {l : List ℕ} → (k : ℕ) → (k < n) → n >L l → n >L (k ∷ l)

≤s : {i j : ℕ} → suc i ≤ j → i ≤ j
fst (≤s (k , p)) = suc k
snd (≤s {i} (k , p)) = (sym (+-suc k i)) ∙ p

getOrderFrom>L : {n : ℕ} {a : ℕ} {l l1 l2 : List ℕ} → (n >L l) → (l ≡ l1 ++ (a ∷ l2)) → (a < n)
getOrderFrom>L {n = n} {l = .[]} {l1 = []} {l2 = l2} largerThenEmpty p = ⊥.elim (¬cons≡nil (sym p))
getOrderFrom>L {n = n} {l = .(k ∷ _)} {l1 = []} {l2 = l2} (k :⟨ x ⟩: ln) p = transport (cong (λ k → (k < n)) (cons-inj₁ p)) x
getOrderFrom>L {n = n} {l = []} {l1 = x ∷ l1} {l2 = l2} ln p = ⊥.elim (¬cons≡nil (sym p))
getOrderFrom>L {n = n} {l = x₁ ∷ l} {l1 = x ∷ l1} {l2 = l2} (_ :⟨ _ ⟩: ln) p = getOrderFrom>L ln (cons-inj₂ p)

>L-↓ : (n k r : ℕ) → (r + k ≤ n) → (n >L (k ↓ r))
>L-↓ n k zero r+k≤n = largerThenEmpty
>L-↓ n k (suc r) r+k≤sn = (r + k) :⟨ r+k≤sn ⟩: (>L-↓ n k r (≤s r+k≤sn))

>L-++ : {n : ℕ} → {l1 l2 : List ℕ} → n >L l1 → n >L l2 → n >L (l1 ++ l2)
>L-++ {n} {[]} {l2} ll1 ll2 = ll2
>L-++ {n} {x ∷ l1} {l2} (.x :⟨ p ⟩: ll1) ll2 = x :⟨ p ⟩: (>L-++ ll1 ll2)

<-weak : {n k : ℕ} → (k < n) → (k < suc n)
<-weak {n} {k} (i , k<n) = suc i , cong suc k<n

>L-suc : {n : ℕ} → {l : List ℕ} → (n >L l) → ((suc n) >L l)
>L-suc largerThenEmpty = largerThenEmpty
>L-suc (k :⟨ p ⟩: l') = k :⟨ <-weak p ⟩: >L-suc l'

>L-Prop : {n : ℕ} → {l : List ℕ} → (l1 : n >L l) → (l2 : n >L l) → (l1 ≡ l2)
>L-Prop largerThenEmpty largerThenEmpty = refl
>L-Prop (k1 :⟨ p ⟩: l1) (k2 :⟨ q ⟩: l2) = cong (λ l → k1 :⟨ p ⟩: l) (>L-Prop l1 l2) ∙ cong (λ a → (k1 :⟨ a ⟩: l2)) (<-Prop p q)
  where
    <-Prop : {m n : ℕ} → (p : m < n) →  (q : m < n) → (p ≡ q)
    <-Prop {m} {n} (k , p) (l , q) = Σ≡Prop witness-prop lemma
      where
        witness-prop : {m n : ℕ} → ∀ j → isProp (j + m ≡ n)
        witness-prop {m} {n} j = isSetℕ (j + m) n
        lemma : k ≡ l
        lemma = inj-+m (p ∙ (sym q))

ListWithOrder : ℕ → Type₀
ListWithOrder n = Σ _ (λ l → n >L l)

data _≤′_ (m : ℕ) : ℕ → Set where
  ≤′-refl :                         m ≤′ m
  ≤′-step : ∀ {n} (m≤′n : m ≤′ n) → m ≤′ suc n

private
  ≤′→≤ : {n : ℕ} {m : ℕ} → (n ≤′ m) → (n ≤ m)
  ≤′→≤ {n = n} {m = .n} ≤′-refl = zero , refl
  ≤′→≤ {n = n} {m = .(suc n₁)} (≤′-step {n = n₁} p) = suc (fst f) , cong suc (snd f)
    where
      f = ≤′→≤ p

  ≤→≤′ : {n : ℕ} {m : ℕ} → (n ≤ m) → (n ≤′ m)
  ≤→≤′ {n = zero} {m = zero} (x , p) = ≤′-refl
  ≤→≤′ {n = suc n} {m = zero} f = ⊥.elim (¬-<-zero {m = n} (fst f , snd f))
  ≤→≤′ {n = n} {m = suc m} (zero , p) = transport (sym (cong (λ k → (k ≤′ (suc m))) p)) ≤′-refl
  ≤→≤′ {n = n} {m = suc m} (suc x , p) = ≤′-step (≤→≤′ (x , injSuc p))

PushIn->L : {n m : ℕ} → (n ≤′ m) → (x : LehmerCode n) → Σ (LehmerCode m) (λ y → LehmerCode→Trans y ≡ LehmerCode→Trans x)
PushIn->L {n} {.n} ≤′-refl x = x , refl
PushIn->L {n} {.(suc n₁)} (≤′-step {n = n₁} p) x = ((zero , n₁ , +-comm n₁ 1) :: (fst tmp)) , ++-unit-r (LehmerCode→Trans (fst tmp)) ∙ (snd tmp)
  where
    tmp = PushIn->L {n} {n₁} (p) x

PushOut->L : {n : ℕ} → (x : LehmerCode n) → (m : ℕ) → (m >L (LehmerCode→Trans x)) → Σ (LehmerCode m) (λ y → LehmerCode→Trans y ≡ LehmerCode→Trans x)
PushOut->L {zero} x m y = PushIn->L (≤→≤′ zero-≤) x
PushOut->L {suc n} ((zero , p) :: xs) m y = fst (PushOut->L {n} xs m (transport (cong (λ a → m >L a) (++-unit-r (LehmerCode→Trans xs))) y)) ,
                                            snd (PushOut->L {n} xs m (transport (cong (λ a → m >L a) (++-unit-r (LehmerCode→Trans xs))) y)) ∙ sym (++-unit-r (LehmerCode→Trans xs))
PushOut->L {suc n} ((suc x , p) :: xs) zero y = ⊥.elim (¬-<-zero  (getOrderFrom>L y refl))
PushOut->L {suc n} ((suc x , p) :: xs) (suc m) y = PushIn->L {m = suc m} (≤→≤′ (subst (λ k → k ≤ (suc m)) (cong suc tmp) (getOrderFrom>L y refl))) ((suc x , p) :: xs)
  where
    tmp = x + (n -ℕ x)
            ≡⟨ cong (λ k → x + k) (sym (cong (λ k → (k -ℕ x)) (snd f)) ∙ cong (λ k → (k -ℕ x)) (+-assoc (fst f) 1 x)
              ∙ cong (λ k → ((k + x) -ℕ x)) (+-comm (fst f) 1) ∙ cong (λ k → (k -ℕ x)) (+-comm (suc (fst f)) x)
              ∙ cong (λ k → ((x + suc (fst f)) -ℕ k)) (sym (+-zero x)) ∙ -ℕ-cancelˡ x (suc (fst f)) zero) ⟩
          x + (suc (fst f))
            ≡⟨ (+-comm x (suc (fst f)) ∙ (cong suc (+-comm (fst p) x)) ∙ sym (+-comm (fst f) (suc x))) ∙ snd f ⟩
          n ∎
      where
        f = <-k+-cancel {1} p

L-lem : {n : ℕ} → {l1 l2 : ListWithOrder n} → ((l1 .fst) ≡ (l2 .fst)) → (l1 ≡ l2)
L-lem {n} {(l1 , l1')} {(l2 , l2')} p i = p i , f i
  where
    f : PathP (λ i → n >L (p i)) l1' l2'
    f = toPathP (>L-Prop _ _)

≤--ℕ-+-cancel : {m n : ℕ} → m ≤ n → (n -ℕ m) + m ≡ n
≤--ℕ-+-cancel {zero} {n} _ = +-zero _
≤--ℕ-+-cancel {suc m} {zero} m≤n = ⊥.rec (¬-<-zero m≤n)
≤--ℕ-+-cancel {suc m} {suc n} m+1≤n+1 = +-suc _ _ ∙ cong suc (≤--ℕ-+-cancel (pred-≤-pred m+1≤n+1))

TransWithOrder : {n : ℕ} → (x : LehmerCode n) → (n >L (LehmerCode→Trans x))
TransWithOrder {zero} x = _>L_.largerThenEmpty
TransWithOrder {suc n} ((j , j<sn) :: xs) = >L-++ (>L-suc (TransWithOrder xs)) (>L-↓ (suc n) ((suc n) -ℕ j) j (zero , (+-comm j (suc n -ℕ j)) ∙ (≤--ℕ-+-cancel {j} {suc n} (<-weaken j<sn) )))

private
    f : {n : ℕ} → ListWithOrder n → List (Fin n)
    f {n} ([] , largerThenEmpty) = []
    f {n} (x ∷ xs , (.x :⟨ p ⟩: y)) = (x , p) ∷ f (xs , y)

    g : {n : ℕ} → List (Fin n) → ListWithOrder n
    g {n} [] = [] , largerThenEmpty
    g {n} (x ∷ xs) = ((x . fst) ∷ (g xs) . fst) , ((x .fst) :⟨ x .snd ⟩: (g xs) . snd)

    f-g : {n : ℕ} → (x : List (Fin n)) → f (g x) ≡ x
    f-g [] = refl
    f-g ((x , p) ∷ xs) = cong₂ (_∷_) refl (f-g xs)

    g-f : {n : ℕ} → (x : ListWithOrder n) → g (f x) ≡ x
    g-f ([] , largerThenEmpty) = refl
    g-f (x ∷ xs , (n :⟨ p ⟩: l)) = L-lem (cong₂ (_∷_) refl (cong fst (g-f (xs , l))))

lem : {n : ℕ} → (ListWithOrder n) ≃ (List (Fin n))
lem = isoToEquiv (iso f g f-g g-f)

Lehmer→Sym : {n : ℕ} → LehmerCode n → List (Fin n)
Lehmer→Sym {zero} x = []
Lehmer→Sym {suc n} x = fst lem ((LehmerCode→Trans x , TransWithOrder x))

Lehmer→Sym-injective : {n : ℕ} → (x1 x2 : LehmerCode (suc n)) → (Lehmer→Sym x1) ∼ (Lehmer→Sym x2) → (x1 ≡ x2)
Lehmer→Sym-injective x1 x2 p = {!!}

Sym→Lehmer-Helper : {n : ℕ} → (x : List (Fin (suc n))) → Σ (LehmerCode (suc n)) (λ y → x ∼ Lehmer→Sym y)
Sym→Lehmer-Helper {n} x = {!!}
  where
    tmp = g (rev x)
    mx = fst tmp
    ns = snd tmp
    LehmerTmp = List


Sym→Lehmer : {n : ℕ} →  List (Fin n) → LehmerCode n
Sym→Lehmer {zero} [] = []
Sym→Lehmer {zero} ((x , p) ∷ xs) = ⊥.rec (¬-<-zero p)
Sym→Lehmer {suc n} x = Sym→Lehmer-Helper x . fst

Sym→Sym : {n : ℕ} → (x : List (Fin n)) → Lehmer→Sym (Sym→Lehmer x) ∼ x
Sym→Sym {zero} [] = id
Sym→Sym {zero} ((x , p) ∷ xs) = ⊥.rec (¬-<-zero p)
Sym→Sym {suc n} x = Symmetry {suc n} (Sym→Lehmer-Helper x . snd)

Lehmer→Lehmer : {n : ℕ} → (x : LehmerCode n) → Sym→Lehmer (Lehmer→Sym x) ≡ x
Lehmer→Lehmer {zero} [] = refl
Lehmer→Lehmer {suc n} x = Lehmer→Sym-injective tmp x p
  where
    tmp = fst (Sym→Lehmer-Helper (fst lem ((LehmerCode→Trans x , TransWithOrder x))))
    p = Symmetry (snd (Sym→Lehmer-Helper (fst lem ((LehmerCode→Trans x , TransWithOrder x)))))
