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

▷ : Setₒ → Setₒ
▷ ϕ k = ∀ j → j < k → ϕ j

down-later : ∀{Γ}{Δ : Times Γ} (ϕ : Setᵒ Γ Δ)
  → ∀ δ → downClosedᵈ δ → downClosed (▷ (# ϕ δ))
down-later {Γ}{Δ} ϕ δ down-δ n ▷ϕn k k≤n j j<k = ▷ϕn j (≤-trans{suc j}{k}{n} j<k k≤n)

cong-▷ : ∀{ϕ ψ : Setₒ} → ϕ ≡ₒ ψ → ▷ ϕ ≡ₒ ▷ ψ
cong-▷ {ϕ}{ψ} ϕ=ψ i = (λ ▷ϕi j j<i → let ψj = proj₁ (ϕ=ψ j) (▷ϕi j j<i) in ψj)
        , (λ ▷ψi j j<i → let ϕj = proj₂ (ϕ=ψ j) (▷ψi j j<i) in ϕj)

contractive-▷ : ∀{k} (S : Setₒ) → ▷ S ≡ₒ[ suc k ] ▷ (↓ k S)
contractive-▷ {k} S zero = (λ _ → tt , (λ x ())) , (λ _ → tt , (λ x ()))
contractive-▷ {k} S (suc i) = (λ { (x , x₁) → x , (λ j x₂ → ≤-trans{suc j}{suc i}{k} x₂ x , (x₁ j x₂))})
     , λ { (x , ▷↓kSsi) → x , (λ j x₂ → let xx = ▷↓kSsi j x₂ in proj₂ xx)}

strong-▷ : ∀{Γ}{Δ : Times Γ}(S : Setᵒ Γ Δ) → strong-fun (laters Γ) (λ δ → ▷ (# S δ))
strong-▷ {Γ}{Δ} S x
    with strong S x
... | strongS
    with timeof x Δ
... | Now rewrite timeof-later{Γ} x = λ δ j k k≤j →
      ↓ (suc k) (▷ (# S δ))
    ⩦⟨ contractive-▷ (# S δ) ⟩
      ↓ (suc k) (▷ (↓ k (# S δ)))
    ⩦⟨ cong-approx (suc k) (cong-▷ (strongS δ j k k≤j)) ⟩
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
    ⩦⟨ cong-approx (suc k) (cong-approx (2 + k) (cong-▷ (strongS δ j k k≤j))) ⟩
      ↓ (suc k) (↓ (2 + k) (▷ (↓ (suc k) ((# S) (↓ᵈ j x δ)))))
    ⩦⟨ ≡ₒ-sym (cong-approx (suc k) (contractive-▷ (# S (↓ᵈ j x δ)))) ⟩
      ↓ (suc k) (↓ (2 + k) (▷ (# S (↓ᵈ j x δ))))
    ⩦⟨ lemma17 (suc k) ⟩
      ↓ (suc k) (▷ (# S (↓ᵈ j x δ)))
    ∎
      

