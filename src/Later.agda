{-# OPTIONS --without-K --prop #-}

open import Data.Nat using (ℕ; zero; suc; _+_)

open import PropP
open import Variables
open import RawSetO
open import SetO
open import Approx
open import Env
open import EquivalenceRelationProp

module Later where

▷ : Setₒ → Setₒ
▷ ϕ k = ∀ j → j <ₚ k → ϕ j

down-later : ∀{Γ}{Δ : Times Γ} (ϕ : Setᵒ Γ Δ)
  → ∀ δ → downClosedᵈ δ → downClosed (▷ (# ϕ δ))
down-later {Γ}{Δ} ϕ δ down-δ n ▷ϕn k k≤n j j<k = ▷ϕn j (≤-transₚ{suc j}{k}{n} j<k k≤n)

cong-▷ : ∀{ϕ ψ : Setₒ} → ϕ ≡ₒ ψ → ▷ ϕ ≡ₒ ▷ ψ
cong-▷ {ϕ}{ψ} ϕ=ψ i = (λ ▷ϕi j j<i → let ψj = proj₁ₚ (ϕ=ψ j) (▷ϕi j j<i) in ψj)
        ,ₚ (λ ▷ψi j j<i → let ϕj = proj₂ₚ (ϕ=ψ j) (▷ψi j j<i) in ϕj)

contractive-▷ : ∀{k} (S : Setₒ) → ▷ S ≡ₒ[ suc k ] ▷ (↓ k S)
contractive-▷ {k} S zero = (λ _ → ttₚ ,ₚ (λ x ())) ,ₚ (λ _ → ttₚ ,ₚ (λ x ()))
contractive-▷ {k} S (suc i) = (λ { (x ,ₚ x₁) → x ,ₚ (λ j x₂ → ≤-transₚ{suc j}{suc i}{k} x₂ x ,ₚ (x₁ j x₂))})
     ,ₚ λ { (x ,ₚ ▷↓kSsi) → x ,ₚ (λ j x₂ → let xx = ▷↓kSsi j x₂ in proj₂ₚ xx)}

wellformed-▷ : ∀{Γ}{Δ : Times Γ}(S : Setᵒ Γ Δ) → wellformed-prop (laters Γ) (λ δ → ▷ (# S δ))
wellformed-▷ {Γ}{Δ} S x
    with wellformed S x
... | wellformedS
    with timeof x Δ
... | Now rewrite timeof-later{Γ} x = λ δ j k k≤j →
      ↓ (suc k) (▷ (# S δ))
    ⩦⟨ contractive-▷ (# S δ) ⟩
      ↓ (suc k) (▷ (↓ k (# S δ)))
    ⩦⟨ cong-approx (suc k) (cong-▷ (wellformedS δ j k k≤j)) ⟩
      ↓ (suc k) (▷ (↓ k (# S (↓ᵈ j x δ))))
    ⩦⟨ ≡ₒ-sym (contractive-▷ (# S (↓ᵈ j x δ))) ⟩
      ↓ (suc k) (▷ (# S (↓ᵈ j x δ)))
    ∎
... | Later rewrite timeof-later{Γ} x = λ δ j k k≤j →
      ↓ (suc k) (▷ (# S δ))
    ⩦⟨ ≡ₒ-sym (lemma17 (suc k)) ⟩
      ↓ (suc k) (↓ (2 + k) (▷ (# S δ)))
    ⩦⟨ cong-approx (suc k) (contractive-▷ (# S δ)) ⟩
      ↓ (suc k) (↓ (2 + k) (▷ (↓ (suc k) (# S δ))))
    ⩦⟨ cong-approx (suc k) (cong-approx (2 + k) (cong-▷ (wellformedS δ j k k≤j))) ⟩
      ↓ (suc k) (↓ (2 + k) (▷ (↓ (suc k) ((# S) (↓ᵈ j x δ)))))
    ⩦⟨ ≡ₒ-sym (cong-approx (suc k) (contractive-▷ (# S (↓ᵈ j x δ)))) ⟩
      ↓ (suc k) (↓ (2 + k) (▷ (# S (↓ᵈ j x δ))))
    ⩦⟨ lemma17 (suc k) ⟩
      ↓ (suc k) (▷ (# S (↓ᵈ j x δ)))
    ∎
      

