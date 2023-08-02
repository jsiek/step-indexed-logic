{-# OPTIONS --without-K #-}

open import Data.Nat using (ℕ; _<_)
open import Data.Nat.Properties using (≤-trans)
open import RawSetO
open import SetO
open import Variables

module Later where

  ▷ : ∀{Γ} → (RecEnv Γ → ℕ → Set) → (RecEnv Γ → ℕ → Set)
  ▷ ϕ δ k = ∀ j → j < k → ϕ δ j

  down-later : ∀{Γ}{Δ : Times Γ} (ϕ : Setᵒ Γ Δ)
    → ∀ δ → downClosedᵈ δ → downClosed (▷ (# ϕ) δ)
  down-later {Γ}{Δ} ϕ δ down-δ n ▷ϕn k k≤n j j<k = ▷ϕn j (≤-trans j<k k≤n)
