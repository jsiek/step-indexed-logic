{-# OPTIONS --without-K --prop #-}

open import Data.Nat using (ℕ; zero; suc)

open import PropLib
open import RawSetO
open import SetO
open import Variables

module Later where

  ▷ : ∀{Γ} → (RecEnv Γ → Setₒ) → (RecEnv Γ → Setₒ)
  ▷ ϕ δ k = ∀ j → j < k → ϕ δ j

  down-later : ∀{Γ}{Δ : Times Γ} (ϕ : Setᵒ Γ Δ)
    → ∀ δ → downClosedᵈ δ → downClosed (▷ (# ϕ) δ)
  down-later {Γ}{Δ} ϕ δ down-δ n ▷ϕn k k≤n j j<k = ▷ϕn j (≤-trans{suc j}{k}{n} j<k k≤n)
