{-# OPTIONS --without-K --prop #-}
open import Data.Product using (_,_;_×_) -- ; proj₁; proj₂; Σ-syntax; ∃-syntax)

open import PropP
open import RawSetO
open import Approx
open import EquivalenceRelationProp
open import BinaryConnective

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

open import BinaryConnective _×ₒ_ cong-×ₒ nonexpansive-×
  using () renaming (wellformed-connective to wellformed-conjunction) public
