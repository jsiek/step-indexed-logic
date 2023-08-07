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

module Conjunction where

_×ₒ_ : ∀(P Q : Setₒ) → Setₒ
P ×ₒ Q = λ k → P k ×ₚ Q k

cong-×ₒ : ∀{ϕ ϕ′ ψ ψ′ : Setₒ} → ϕ ≡ₒ ϕ′ → ψ ≡ₒ ψ′ → ϕ ×ₒ ψ ≡ₒ ϕ′ ×ₒ ψ′
cong-×ₒ {ϕ}{ϕ′}{ψ}{ψ′} ϕ=ϕ′ ψ=ψ′ k = to ,ₚ fro
  where
  to : (ϕ ×ₒ ψ) k → (ϕ′ ×ₒ ψ′) k
  to (ϕk ,ₚ ψk) = (⇔-to (ϕ=ϕ′ k) ϕk) ,ₚ (⇔-to (ψ=ψ′ k) ψk)
  fro : (ϕ′ ×ₒ ψ′) k → (ϕ ×ₒ ψ) k
  fro (ϕ′k ,ₚ ψ′k) = (⇔-fro (ϕ=ϕ′ k) ϕ′k) ,ₚ (⇔-fro (ψ=ψ′ k) ψ′k)

nonexpansive-× : ∀ k {ϕ ψ : Setₒ} → ϕ ×ₒ ψ ≡ₒ[ k ] (↓ k ϕ) ×ₒ (↓ k ψ)
nonexpansive-× k {ϕ}{ψ} i = (λ {(i<k ,ₚ (ϕi ,ₚ ψi)) → i<k ,ₚ (i<k ,ₚ ϕi) ,ₚ i<k ,ₚ ψi})
                             ,ₚ λ { (i<k ,ₚ (_ ,ₚ ϕi) ,ₚ (_ ,ₚ ψi)) → i<k ,ₚ ϕi ,ₚ ψi}

strong-conjunction : ∀{Γ}{Δ₁ Δ₂ : Times Γ} → (S : Setᵒ Γ Δ₁) (T : Setᵒ Γ Δ₂)
  → strong-fun (combine Δ₁ Δ₂) (λ δ → # S δ ×ₒ # T δ)
strong-conjunction {Γ}{Δ₁}{Δ₂} S T {A} x
    rewrite timeof-combine {Γ}{Δ₁}{Δ₂}{A}{x}
    with timeof x Δ₁ in time-x1 | timeof x Δ₂ in time-x2
... | Now | Now = λ δ j k k≤j →
    let strongS = strong-now⇒nonexpansive (strong S x) time-x1 δ j k k≤j in
    let strongT = strong-now⇒nonexpansive (strong T x) time-x2 δ j k k≤j in
      ↓ k (# S δ ×ₒ # T δ)
    ⩦⟨ nonexpansive-× k ⟩ 
      ↓ k (↓ k (# S δ) ×ₒ ↓ k (# T δ))
    ⩦⟨ cong-approx k (cong-×ₒ strongS (≡ₒ-refl refl)) ⟩ 
      ↓ k (↓ k (# S (↓ᵈ j x δ)) ×ₒ ↓ k (# T δ))
    ⩦⟨ cong-approx k (cong-×ₒ (≡ₒ-refl refl) strongT) ⟩ 
      ↓ k (↓ k (# S (↓ᵈ j x δ)) ×ₒ ↓ k (# T (↓ᵈ j x δ)))
    ⩦⟨ ≡ₒ-sym (nonexpansive-× k) ⟩
      ↓ k (# S (↓ᵈ j x δ) ×ₒ # T (↓ᵈ j x δ))
    ∎
... | Now | Later = λ δ j k k≤j →
    let strongS = strong-now⇒nonexpansive (strong S x) time-x1 δ j k k≤j in
    let strongT = strong-later⇒contractive (strong T x) time-x2 δ j k k≤j in
      ↓ k (# S δ ×ₒ # T δ)
    ⩦⟨ ≡ₒ-sym (lemma17 k) ⟩ 
      ↓ k (↓ (1 + k) (# S δ ×ₒ # T δ))
    ⩦⟨ cong-approx k (nonexpansive-× (1 + k)) ⟩ 
      ↓ k (↓ (1 + k) (↓ (1 + k) (# S δ) ×ₒ ↓ (1 + k) (# T δ)))
    ⩦⟨ cong-approx k (cong-approx (1 + k) (cong-×ₒ (≡ₒ-refl refl) strongT)) ⟩ 
      ↓ k (↓ (1 + k) (↓ (1 + k) (# S δ) ×ₒ ↓ (1 + k) (# T (↓ᵈ j x δ))))
    ⩦⟨ ≡ₒ-sym (cong-approx k (nonexpansive-× (1 + k))) ⟩ 
      ↓ k (↓ (1 + k) (# S δ ×ₒ # T (↓ᵈ j x δ)))
    ⩦⟨ lemma17 k ⟩ 
      ↓ k (# S δ ×ₒ # T (↓ᵈ j x δ))
    ⩦⟨ nonexpansive-× k ⟩ 
      ↓ k (↓ k (# S δ) ×ₒ ↓ k (# T (↓ᵈ j x δ)))
    ⩦⟨ cong-approx k (cong-×ₒ strongS (≡ₒ-refl refl)) ⟩ 
      ↓ k (↓ k (# S (↓ᵈ j x δ)) ×ₒ ↓ k (# T (↓ᵈ j x δ)))
    ⩦⟨ ≡ₒ-sym (nonexpansive-× k) ⟩ 
      ↓ k (# S (↓ᵈ j x δ) ×ₒ # T (↓ᵈ j x δ))
    ∎
... | Later | Now = λ δ j k k≤j →
    let strongS = strong-later⇒contractive (strong S x) time-x1 δ j k k≤j in
    let strongT = strong-now⇒nonexpansive (strong T x) time-x2 δ j k k≤j in
      ↓ k (# S δ ×ₒ # T δ)
    ⩦⟨ ≡ₒ-sym (lemma17 k) ⟩ 
      ↓ k (↓ (1 + k) (# S δ ×ₒ # T δ))
    ⩦⟨ cong-approx k (nonexpansive-× (1 + k)) ⟩ 
      ↓ k (↓ (1 + k) (↓ (1 + k) (# S δ) ×ₒ ↓ (1 + k) (# T δ)))
    ⩦⟨ cong-approx k (cong-approx (1 + k) (cong-×ₒ strongS (≡ₒ-refl refl))) ⟩ 
      ↓ k (↓ (1 + k) (↓ (1 + k) (# S (↓ᵈ j x δ)) ×ₒ ↓ (1 + k) (# T δ)))
    ⩦⟨ ≡ₒ-sym (cong-approx k (nonexpansive-× (1 + k))) ⟩ 
      ↓ k (↓ (1 + k) (# S (↓ᵈ j x δ) ×ₒ # T δ))
    ⩦⟨ lemma17 k ⟩ 
      ↓ k (# S (↓ᵈ j x δ) ×ₒ # T δ)
    ⩦⟨ nonexpansive-× k ⟩ 
      ↓ k (↓ k (# S (↓ᵈ j x δ)) ×ₒ ↓ k (# T δ))
    ⩦⟨ cong-approx k (cong-×ₒ (≡ₒ-refl refl) strongT) ⟩ 
      ↓ k (↓ k (# S (↓ᵈ j x δ)) ×ₒ ↓ k (# T (↓ᵈ j x δ)))
    ⩦⟨ ≡ₒ-sym (nonexpansive-× k) ⟩ 
      ↓ k (# S (↓ᵈ j x δ) ×ₒ # T (↓ᵈ j x δ))
    ∎
... | Later | Later = λ δ j k k≤j →
    let strongS = strong-later⇒contractive (strong S x) time-x1 δ j k k≤j in
    let strongT = strong-later⇒contractive (strong T x) time-x2 δ j k k≤j in
      ↓ (1 + k) (# S δ ×ₒ # T δ)
    ⩦⟨ nonexpansive-× (1 + k) ⟩ 
      ↓ (1 + k) (↓ (1 + k) (# S δ) ×ₒ ↓ (1 + k) (# T δ))
    ⩦⟨ cong-approx (1 + k) (cong-×ₒ strongS strongT) ⟩ 
      ↓ (1 + k) (↓ (1 + k) (# S (↓ᵈ j x δ)) ×ₒ ↓ (1 + k) (# T (↓ᵈ j x δ)))
    ⩦⟨ ≡ₒ-sym (nonexpansive-× (1 + k)) ⟩ 
      ↓ (1 + k) (# S (↓ᵈ j x δ) ×ₒ # T (↓ᵈ j x δ))
    ∎
