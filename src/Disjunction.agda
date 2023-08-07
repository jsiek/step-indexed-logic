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

module Disjunction where

_⊎ₒ_ : ∀(P Q : Setₒ) → Setₒ
P ⊎ₒ Q = λ k → P k ⊎ Q k

cong-⊎ₒ : ∀{ϕ ϕ′ ψ ψ′ : Setₒ} → ϕ ≡ₒ ϕ′ → ψ ≡ₒ ψ′ → ϕ ⊎ₒ ψ ≡ₒ ϕ′ ⊎ₒ ψ′
cong-⊎ₒ {ϕ}{ϕ′}{ψ}{ψ′} ϕ=ϕ′ ψ=ψ′ k = to ,ₚ fro
  where
  to : (ϕ ⊎ₒ ψ) k → (ϕ′ ⊎ₒ ψ′) k
  to (inj₁ ϕk) = inj₁ (⇔-to (ϕ=ϕ′ k) ϕk)
  to (inj₂ ψk) = inj₂ (⇔-to (ψ=ψ′ k) ψk)
  fro : (ϕ′ ⊎ₒ ψ′) k → (ϕ ⊎ₒ ψ) k
  fro (inj₁ ϕ′k) = inj₁ (⇔-fro (ϕ=ϕ′ k) ϕ′k)
  fro (inj₂ ψ′k) = inj₂ (⇔-fro (ψ=ψ′ k) ψ′k)

nonexpansive-⊎ : ∀ k {ϕ ψ : Setₒ} → ϕ ⊎ₒ ψ ≡ₒ[ k ] (↓ k ϕ) ⊎ₒ (↓ k ψ)
nonexpansive-⊎ k {ϕ}{ψ} i = (λ { (i<k ,ₚ inj₁ ϕi) → i<k ,ₚ (inj₁ (i<k ,ₚ ϕi))
                               ; (i<k ,ₚ inj₂ ψi) → i<k ,ₚ inj₂ (i<k ,ₚ ψi)})
                             ,ₚ (λ { (i<k ,ₚ inj₁ (_ ,ₚ ϕi)) → i<k ,ₚ inj₁ ϕi
                                   ; (i<k ,ₚ inj₂ (_ ,ₚ ψi)) → i<k ,ₚ inj₂ ψi})

open import BinaryConnective _⊎ₒ_ cong-⊎ₒ nonexpansive-⊎
  using () renaming (strong-connective to strong-disjunction) public

