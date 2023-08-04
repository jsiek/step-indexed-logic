{-# OPTIONS --without-K --prop #-}

open import Data.Nat using (ℕ; zero; suc)
open import PropLib

module StrongInduction where

strong-induction : ∀{P : ℕ → Prop} → (∀ (n : ℕ) → (∀ k → k < n → P k) → P n) → (∀ n → P n)
strong-induction {P} step n = aux step (suc n) n (≤-refl{n})
  where
  aux : ∀{P : ℕ → Prop} → (∀ (n : ℕ) → (∀ k → k < n → P k) → P n) → (∀ j k → k < j → P k)
  aux {P} step zero k ()
  aux {P} step (suc j) zero k<j = step 0 λ {k ()}
  aux {P} step (suc j) (suc k) k<j =
    step (suc k) (λ i i<sk → aux step j i (≤-trans{suc i}{suc k}{j} i<sk (≤-pred{suc k}{j} k<j)))
