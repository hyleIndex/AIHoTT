\begin{code}
{-# OPTIONS --cubical #-}
open import Cubical.HITs.SetQuotients as SetQuotient
open import Cubical.HITs.PropositionalTruncation as PropositionalTruncation

open import Cubical.Data.Sigma
open import Cubical.Data.Nat as ℕ renaming (_+_ to _+ℕ_ ; _·_ to _*ℕ_)

rel : (ℕ × ℕ) → (ℕ × ℕ) → Type₀
rel (a₀ , b₀) (a₁ , b₁) = x ≡ y
  where
    x = a₀ +ℕ b₁
    y = a₁ +ℕ b₀

\end{code}