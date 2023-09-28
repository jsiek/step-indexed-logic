{-# OPTIONS --without-K --prop #-}
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_,_;_×_) -- ; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Nat using (ℕ; zero; suc; _+_)
--open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_; _∸_; z≤n; s≤s; _≤′_; ≤′-step)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans)

open import PropLib renaming (_×_ to _×ₚ_; _,_ to _,ₚ_)
open import RawSetO
open import SetO
open import Variables
open import Env
open import Approx
open import EquivalenceRelationProp

module BinaryConnective
  (_⊕_ : ∀(P Q : Setₒ) → Setₒ)
  (cong-⊕ : ∀{ϕ ϕ′ ψ ψ′ : Setₒ} → ϕ ≡ₒ ϕ′ → ψ ≡ₒ ψ′ → ϕ ⊕ ψ ≡ₒ ϕ′ ⊕ ψ′)
  (nonexpansive-⊕ : ∀ k {ϕ ψ : Setₒ} → ϕ ⊕ ψ ≡ₒ[ k ] (↓ k ϕ) ⊕ (↓ k ψ))
  where

wellformed-connective : ∀{Γ}{Δ₁ Δ₂ : Times Γ} → (S : Setᵒ Γ Δ₁) (T : Setᵒ Γ Δ₂)
  → wellformed-prop (combine Δ₁ Δ₂) (λ δ → # S δ ⊕ # T δ)
wellformed-connective {Γ}{Δ₁}{Δ₂} S T {A} x
    rewrite timeof-combine {Γ}{Δ₁}{Δ₂}{A}{x}
    with timeof x Δ₁ in time-x1 | timeof x Δ₂ in time-x2
... | Now | Now = λ δ j k k≤j →
    let wellformedS = wellformed-now⇒nonexpansive (wellformed S x) time-x1 δ j k k≤j in
    let wellformedT = wellformed-now⇒nonexpansive (wellformed T x) time-x2 δ j k k≤j in
      ↓ k (# S δ ⊕ # T δ)
    ⩦⟨ nonexpansive-⊕ k ⟩ 
      ↓ k (↓ k (# S δ) ⊕ ↓ k (# T δ))
    ⩦⟨ cong-approx k (cong-⊕ wellformedS (≡ₒ-refl refl)) ⟩ 
      ↓ k (↓ k (# S (↓ᵈ j x δ)) ⊕ ↓ k (# T δ))
    ⩦⟨ cong-approx k (cong-⊕ (≡ₒ-refl refl) wellformedT) ⟩ 
      ↓ k (↓ k (# S (↓ᵈ j x δ)) ⊕ ↓ k (# T (↓ᵈ j x δ)))
    ⩦⟨ ≡ₒ-sym (nonexpansive-⊕ k) ⟩
      ↓ k (# S (↓ᵈ j x δ) ⊕ # T (↓ᵈ j x δ))
    ∎
... | Now | Later = λ δ j k k≤j →
    let wellformedS = wellformed-now⇒nonexpansive (wellformed S x) time-x1 δ j k k≤j in
    let wellformedT = wellformed-later⇒contractive (wellformed T x) time-x2 δ j k k≤j in
      ↓ k (# S δ ⊕ # T δ)
    ⩦⟨ ≡ₒ-sym (lemma17 k) ⟩ 
      ↓ k (↓ (1 + k) (# S δ ⊕ # T δ))
    ⩦⟨ cong-approx k (nonexpansive-⊕ (1 + k)) ⟩ 
      ↓ k (↓ (1 + k) (↓ (1 + k) (# S δ) ⊕ ↓ (1 + k) (# T δ)))
    ⩦⟨ cong-approx k (cong-approx (1 + k) (cong-⊕ (≡ₒ-refl refl) wellformedT)) ⟩ 
      ↓ k (↓ (1 + k) (↓ (1 + k) (# S δ) ⊕ ↓ (1 + k) (# T (↓ᵈ j x δ))))
    ⩦⟨ ≡ₒ-sym (cong-approx k (nonexpansive-⊕ (1 + k))) ⟩ 
      ↓ k (↓ (1 + k) (# S δ ⊕ # T (↓ᵈ j x δ)))
    ⩦⟨ lemma17 k ⟩ 
      ↓ k (# S δ ⊕ # T (↓ᵈ j x δ))
    ⩦⟨ nonexpansive-⊕ k ⟩ 
      ↓ k (↓ k (# S δ) ⊕ ↓ k (# T (↓ᵈ j x δ)))
    ⩦⟨ cong-approx k (cong-⊕ wellformedS (≡ₒ-refl refl)) ⟩ 
      ↓ k (↓ k (# S (↓ᵈ j x δ)) ⊕ ↓ k (# T (↓ᵈ j x δ)))
    ⩦⟨ ≡ₒ-sym (nonexpansive-⊕ k) ⟩ 
      ↓ k (# S (↓ᵈ j x δ) ⊕ # T (↓ᵈ j x δ))
    ∎
... | Later | Now = λ δ j k k≤j →
    let wellformedS = wellformed-later⇒contractive (wellformed S x) time-x1 δ j k k≤j in
    let wellformedT = wellformed-now⇒nonexpansive (wellformed T x) time-x2 δ j k k≤j in
      ↓ k (# S δ ⊕ # T δ)
    ⩦⟨ ≡ₒ-sym (lemma17 k) ⟩ 
      ↓ k (↓ (1 + k) (# S δ ⊕ # T δ))
    ⩦⟨ cong-approx k (nonexpansive-⊕ (1 + k)) ⟩ 
      ↓ k (↓ (1 + k) (↓ (1 + k) (# S δ) ⊕ ↓ (1 + k) (# T δ)))
    ⩦⟨ cong-approx k (cong-approx (1 + k) (cong-⊕ wellformedS (≡ₒ-refl refl))) ⟩ 
      ↓ k (↓ (1 + k) (↓ (1 + k) (# S (↓ᵈ j x δ)) ⊕ ↓ (1 + k) (# T δ)))
    ⩦⟨ ≡ₒ-sym (cong-approx k (nonexpansive-⊕ (1 + k))) ⟩ 
      ↓ k (↓ (1 + k) (# S (↓ᵈ j x δ) ⊕ # T δ))
    ⩦⟨ lemma17 k ⟩ 
      ↓ k (# S (↓ᵈ j x δ) ⊕ # T δ)
    ⩦⟨ nonexpansive-⊕ k ⟩ 
      ↓ k (↓ k (# S (↓ᵈ j x δ)) ⊕ ↓ k (# T δ))
    ⩦⟨ cong-approx k (cong-⊕ (≡ₒ-refl refl) wellformedT) ⟩ 
      ↓ k (↓ k (# S (↓ᵈ j x δ)) ⊕ ↓ k (# T (↓ᵈ j x δ)))
    ⩦⟨ ≡ₒ-sym (nonexpansive-⊕ k) ⟩ 
      ↓ k (# S (↓ᵈ j x δ) ⊕ # T (↓ᵈ j x δ))
    ∎
... | Later | Later = λ δ j k k≤j →
    let wellformedS = wellformed-later⇒contractive (wellformed S x) time-x1 δ j k k≤j in
    let wellformedT = wellformed-later⇒contractive (wellformed T x) time-x2 δ j k k≤j in
      ↓ (1 + k) (# S δ ⊕ # T δ)
    ⩦⟨ nonexpansive-⊕ (1 + k) ⟩ 
      ↓ (1 + k) (↓ (1 + k) (# S δ) ⊕ ↓ (1 + k) (# T δ))
    ⩦⟨ cong-approx (1 + k) (cong-⊕ wellformedS wellformedT) ⟩ 
      ↓ (1 + k) (↓ (1 + k) (# S (↓ᵈ j x δ)) ⊕ ↓ (1 + k) (# T (↓ᵈ j x δ)))
    ⩦⟨ ≡ₒ-sym (nonexpansive-⊕ (1 + k)) ⟩ 
      ↓ (1 + k) (# S (↓ᵈ j x δ) ⊕ # T (↓ᵈ j x δ))
    ∎
