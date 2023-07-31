{-# OPTIONS --without-K #-}

open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-pred)

module StrongInduction where

strong-induction : ∀{P : ℕ → Set} → (∀ (n : ℕ) → (∀ k → k < n → P k) → P n) → (∀ n → P n)
strong-induction {P} step n = aux step (suc n) n ≤-refl
  where
  aux : ∀{P : ℕ → Set} → (∀ (n : ℕ) → (∀ k → k < n → P k) → P n) → (∀ j k → k < j → P k)
  aux {P} step zero k ()
  aux {P} step (suc j) zero k<j = step 0 λ {k ()}
  aux {P} step (suc j) (suc k) k<j =
    step (suc k) (λ i i<sk → aux step j i (≤-trans i<sk (≤-pred k<j)))
