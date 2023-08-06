{-# OPTIONS --without-K --prop #-}

open import Data.Nat using (ℕ; zero; suc; _+_)

open import PropLib
open import Variables
open import RawSetO
open import SetO
open import Approx
open import Env
open import EquivalenceRelationProp

module Later where

▷ : ∀{Γ} → (RecEnv Γ → Setₒ) → (RecEnv Γ → Setₒ)
▷ ϕ δ k = ∀ j → j < k → ϕ δ j

down-later : ∀{Γ}{Δ : Times Γ} (ϕ : Setᵒ Γ Δ)
  → ∀ δ → downClosedᵈ δ → downClosed (▷ (# ϕ) δ)
down-later {Γ}{Δ} ϕ δ down-δ n ▷ϕn k k≤n j j<k = ▷ϕn j (≤-trans{suc j}{k}{n} j<k k≤n)

cong-▷ : ∀{Γ}{ϕ ψ : RecEnv Γ → Setₒ}{δ : RecEnv Γ} → ϕ δ ≡ₒ ψ δ → ▷ ϕ δ ≡ₒ ▷ ψ δ
cong-▷ {Γ}{ϕ}{ψ} ϕ=ψ i = (λ ▷ϕi j j<i → let ψj = proj₁ (ϕ=ψ j) (▷ϕi j j<i) in ψj)
        , (λ ▷ψi j j<i → let ϕj = proj₂ (ϕ=ψ j) (▷ψi j j<i) in ϕj)

contractive-▷ : ∀{Γ}{k}{δ : RecEnv Γ} (S : RecEnv Γ → Setₒ) → ▷ S δ ≡ₒ[ suc k ] ▷ (λ δ′ → ↓ k (S δ′)) δ
contractive-▷ {Γ} {k} {δ} S zero = (λ _ → tt , (λ x ())) , (λ _ → tt , (λ x ()))
contractive-▷ {Γ} {k} {δ} S (suc i) = (λ { (x , x₁) → x , (λ j x₂ → ≤-trans{suc j}{suc i}{k} x₂ x , (x₁ j x₂))})
     , λ { (x , ▷↓kSsi) → x , (λ j x₂ → let xx = ▷↓kSsi j x₂ in proj₂ xx)}

strong-▷ : ∀{Γ}{Δ : Times Γ}(S : Setᵒ Γ Δ) → strong-fun (laters Γ) (λ δ k → ▷ (# S) δ k)
strong-▷ {Γ}{Δ} S x
    with strong S x
... | strongS
    with timeof x Δ
... | Now rewrite timeof-later{Γ} x = λ δ j k k≤j →
      ↓ (suc k) (▷ (# S) δ)
    ⩦⟨ contractive-▷ (# S) ⟩
      ↓ (suc k) (▷ (λ δ′ → ↓ k ((# S) δ′)) δ)
    ⩦⟨ cong-approx (suc k) (cong-▷{Γ}{ϕ = (λ δ′ → ↓ k ((# S) δ′))}{ψ = (λ δ′ → ↓ k ((# S) (↓ᵈ j x δ′)))}
                (strongS δ j k k≤j)) ⟩
      ↓ (suc k) (▷ (λ δ′ → ↓ k ((# S) (↓ᵈ j x δ′))) δ)
    ⩦⟨ ≡ₒ-sym (contractive-▷ (# S)) ⟩
      ↓ (suc k) (▷ (# S) (↓ᵈ j x δ))
    ∎
... | Later rewrite timeof-later{Γ} x = λ δ j k k≤j →
      ↓ (suc k) (▷ (# S) δ)
    ⩦⟨ ≡ₒ-sym (lemma17 (suc k)) ⟩
      ↓ (suc k) (↓ (2 + k) (▷ (# S) δ))
    ⩦⟨ cong-approx (suc k) (contractive-▷ (# S)) ⟩
      ↓ (suc k) (↓ (2 + k) (▷ (λ δ′ → ↓ (suc k) ((# S) δ′)) δ))
    ⩦⟨ cong-approx (suc k) (cong-approx (2 + k) (cong-▷{Γ}{ϕ = (λ δ′ → ↓ (suc k) ((# S) δ′))}
             {ψ = (λ δ′ → ↓ (suc k) ((# S) (↓ᵈ j x δ′)))} (strongS δ j k k≤j))) ⟩
      ↓ (suc k) (↓ (2 + k) (▷ (λ δ′ → ↓ (suc k) ((# S) (↓ᵈ j x δ′))) δ))
    ⩦⟨ ≡ₒ-sym (cong-approx (suc k) (contractive-▷ (# S))) ⟩
      ↓ (suc k) (↓ (2 + k) (▷ (λ δ′ → (# S) (↓ᵈ j x δ′)) δ))
    ⩦⟨ lemma17 (suc k) ⟩
      ↓ (suc k) (▷ (# S) (↓ᵈ j x δ))
    ∎
      

