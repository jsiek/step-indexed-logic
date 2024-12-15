{-# OPTIONS --without-K --prop #-}
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_,_;_×_) -- ; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Nat using (ℕ; zero; suc; _+_)
--open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_; _∸_; z≤n; s≤s; _≤′_; ≤′-step)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans)

open import PropP
open import RawSetO
open import SetO
open import SILVariables
open import Env
open import Approx
open import EquivalenceRelationProp

module Forall where

∀ₒ : ∀(A : Set) → (P : A → Setₒ) → Setₒ
∀ₒ A P = λ k → ∀ (a : A) → P a k

∀ₒ-syntax : ∀ (A : Set) → (A → Setₒ) → Setₒ
∀ₒ-syntax A = ∀ₒ A
infix 2 ∀ₒ-syntax
syntax ∀ₒ-syntax A (λ x → P) = ∀ₒ[ x ⦂ A ] P

cong-∀ : ∀{A : Set}{P Q : A → Setₒ} → (∀ a → P a ≡ₒ Q a) → (∀ₒ[ a ⦂ A ] P a) ≡ₒ (∀ₒ[ a ⦂ A ] Q a)
cong-∀ {A}{P}{Q} P=Q i = (λ ∀Pi a → proj₁ₚ (P=Q a i) (∀Pi a)) ,ₚ (λ ∀Qi a → proj₂ₚ (P=Q a i) (∀Qi a))

nonexpansive-∀ : ∀ k → ∀{A} (P : A → Setₒ) → (∀ₒ[ a ⦂ A ] P a)  ≡ₒ[ k ]  (∀ₒ[ a ⦂ A ] ↓ k (P a))
nonexpansive-∀ k P i = (λ {(i<k ,ₚ ∀Pi) → i<k ,ₚ λ a → i<k ,ₚ ∀Pi a})
                       ,ₚ (λ {(i<k ,ₚ ↓k∀Pi) → i<k ,ₚ λ a → proj₂ₚ (↓k∀Pi a)})

wellformed-all : ∀{A : Set}{Γ}{Δ : Times Γ} → (P : A → Setᵒ Γ Δ) → wellformed-prop Δ (λ δ → ∀ₒ[ a ⦂ A ] # (P a) δ)
wellformed-all {A}{Γ}{Δ} P x
    with timeof x Δ in time-x
... | Now = λ δ j k k≤j →
      ↓ k (∀ₒ[ a ⦂ A ] # (P a) δ)
    ⩦⟨ nonexpansive-∀ k (λ a → # (P a) δ) ⟩
      ↓ k (∀ₒ[ a ⦂ A ] ↓ k (# (P a) δ))
    ⩦⟨ cong-approx k (cong-∀ λ a → wellformed-now⇒nonexpansive (wellformed (P a) x) time-x δ j k k≤j) ⟩
      ↓ k (∀ₒ[ a ⦂ A ] ↓ k (# (P a) (↓ᵈ j x δ)))
    ⩦⟨ ≡ₒ-sym (nonexpansive-∀ k (λ a → # (P a) (↓ᵈ j x δ))) ⟩
      ↓ k (∀ₒ[ a ⦂ A ] # (P a) (↓ᵈ j x δ))
    ∎
... | Later = λ δ j k k≤j →
      ↓ (suc k) (∀ₒ[ a ⦂ A ] # (P a) δ)
    ⩦⟨ nonexpansive-∀ (suc k) (λ a → # (P a) δ) ⟩
      ↓ (suc k) (∀ₒ[ a ⦂ A ] ↓ (suc k) (# (P a) δ))
    ⩦⟨ cong-approx (suc k) (cong-∀ (λ a → wellformed-later⇒contractive (wellformed (P a) x) time-x δ j k k≤j)) ⟩
      ↓ (suc k) (∀ₒ[ a ⦂ A ] ↓ (suc k) (# (P a) (↓ᵈ j x δ)))
    ⩦⟨ ≡ₒ-sym (nonexpansive-∀ (suc k) (λ a → # (P a) (↓ᵈ j x δ))) ⟩
      ↓ (suc k) (∀ₒ[ a ⦂ A ] # (P a) (↓ᵈ j x δ))
    ∎

