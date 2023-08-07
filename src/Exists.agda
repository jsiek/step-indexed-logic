{-# OPTIONS --without-K --prop --allow-unsolved-metas #-}
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

module Exists where

∃ₒ : ∀(A : Set) → (P : A → Setₒ) → Setₒ
∃ₒ A P = λ k → Σ[ a ∈ A ] P a k

∃ₒ-syntax : ∀ (A : Set) → (A → Setₒ) → Setₒ
∃ₒ-syntax A = ∃ₒ A
infix 2 ∃ₒ-syntax
syntax ∃ₒ-syntax A (λ x → P) = ∃ₒ[ x ⦂ A ] P

cong-∃ : ∀{A : Set}{P Q : Predₒ A} → (∀ a → P a ≡ₒ Q a) → (∃ₒ[ a ⦂ A ] P a) ≡ₒ (∃ₒ[ a ⦂ A ] Q a)
cong-∃ {A} {P} {Q} P=Q i = (λ {(a ,ₚ b) → a ,ₚ proj₁ (P=Q a i) b}) ,ₚ λ {(a ,ₚ b) → a ,ₚ (proj₂ (P=Q a i) b)}

nonexpansive-∃ : ∀ k → ∀{A : Set} → (P : Predₒ A) → (∃ₒ[ a ⦂ A ] P a) ≡ₒ[ k ] (∃ₒ[ a ⦂ A ] ↓ k (P a))
nonexpansive-∃ k {A} P i = (λ {(a ,ₚ (b ,ₚ c)) → a ,ₚ (b ,ₚ (a ,ₚ c))}) ,ₚ λ { (a ,ₚ b ,ₚ c) → a ,ₚ b ,ₚ proj₂ c}

strong-exists : ∀{A : Set}{Γ}{Δ : Times Γ} → (P : A → Setᵒ Γ Δ)
  → strong-fun Δ (λ δ → ∃ₒ[ a ⦂ A ] # (P a) δ)
strong-exists {A}{Γ}{Δ} P x
    with timeof x Δ in time-x
... | Now = λ δ j k k≤j →
        ↓ k (∃ₒ[ a ⦂ A ] # (P a) δ)
      ⩦⟨ nonexpansive-∃ k (λ a → # (P a) δ)⟩
        ↓ k (∃ₒ[ a ⦂ A ] ↓ k (# (P a) δ))
      ⩦⟨ cong-approx k (cong-∃ λ a → strong-now⇒nonexpansive (strong (P a) x) time-x δ j k k≤j) ⟩
        ↓ k (∃ₒ[ a ⦂ A ] ↓ k (# (P a) (↓ᵈ j x δ)))
      ⩦⟨ ≡ₒ-sym (nonexpansive-∃ k (λ a → # (P a) (↓ᵈ j x δ)))⟩
        ↓ k (∃ₒ[ a ⦂ A ] # (P a) (↓ᵈ j x δ))
      ∎
... | Later = λ δ j k k≤j →
        ↓ (suc k) (∃ₒ[ a ⦂ A ] # (P a) δ)
      ⩦⟨ nonexpansive-∃ (suc k) (λ a → # (P a) δ) ⟩
        ↓ (suc k) (∃ₒ[ a ⦂ A ] ↓ (suc k) (# (P a) δ))
      ⩦⟨ cong-approx (suc k) (cong-∃ (λ a → strong-later⇒contractive (strong (P a) x) time-x δ j k k≤j)) ⟩
        ↓ (suc k) (∃ₒ[ a ⦂ A ] ↓ (suc k) (# (P a) (↓ᵈ j x δ)))
      ⩦⟨ ≡ₒ-sym (nonexpansive-∃ (suc k) (λ a → # (P a) (↓ᵈ j x δ))) ⟩
        ↓ (suc k) (∃ₒ[ a ⦂ A ] # (P a) (↓ᵈ j x δ))
      ∎
