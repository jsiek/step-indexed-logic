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
open import Variables
open import Env
open import Approx
open import EquivalenceRelationProp

module Disjunction where

_⊎ₒ_ : ∀(P Q : Setₒ) → Setₒ
P ⊎ₒ Q = λ k → P k ⊎ₚ Q k

cong-⊎ₒ : ∀{ϕ ϕ′ ψ ψ′ : Setₒ} → ϕ ≡ₒ ϕ′ → ψ ≡ₒ ψ′ → ϕ ⊎ₒ ψ ≡ₒ ϕ′ ⊎ₒ ψ′
cong-⊎ₒ {ϕ}{ϕ′}{ψ}{ψ′} ϕ=ϕ′ ψ=ψ′ k = to ,ₚ fro
  where
  to : (ϕ ⊎ₒ ψ) k → (ϕ′ ⊎ₒ ψ′) k
  to (inj₁ₚ ϕk) = inj₁ₚ (⇔-to (ϕ=ϕ′ k) ϕk)
  to (inj₂ₚ ψk) = inj₂ₚ (⇔-to (ψ=ψ′ k) ψk)
  fro : (ϕ′ ⊎ₒ ψ′) k → (ϕ ⊎ₒ ψ) k
  fro (inj₁ₚ ϕ′k) = inj₁ₚ (⇔-fro (ϕ=ϕ′ k) ϕ′k)
  fro (inj₂ₚ ψ′k) = inj₂ₚ (⇔-fro (ψ=ψ′ k) ψ′k)

nonexpansive-⊎ : ∀ k {ϕ ψ : Setₒ} → ϕ ⊎ₒ ψ ≡ₒ[ k ] (↓ k ϕ) ⊎ₒ (↓ k ψ)
nonexpansive-⊎ k {ϕ}{ψ} i = (λ { (i<k ,ₚ inj₁ₚ ϕi) → i<k ,ₚ (inj₁ₚ (i<k ,ₚ ϕi))
                               ; (i<k ,ₚ inj₂ₚ ψi) → i<k ,ₚ inj₂ₚ (i<k ,ₚ ψi)})
                             ,ₚ (λ { (i<k ,ₚ inj₁ₚ (_ ,ₚ ϕi)) → i<k ,ₚ inj₁ₚ ϕi
                                   ; (i<k ,ₚ inj₂ₚ (_ ,ₚ ψi)) → i<k ,ₚ inj₂ₚ ψi})

open import BinaryConnective _⊎ₒ_ cong-⊎ₒ nonexpansive-⊎
  using () renaming (wellformed-connective to wellformed-disjunction) public

