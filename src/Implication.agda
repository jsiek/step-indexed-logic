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

module Implication where

_→ₒ_ : ∀(P Q : Setₒ) → Setₒ
P →ₒ Q = λ k → ∀ j → j ≤ₚ k → P j → Q j

cong-→ₒ : ∀{ϕ ϕ′ ψ ψ′ : Setₒ} → ϕ ≡ₒ ϕ′ → ψ ≡ₒ ψ′ → ϕ →ₒ ψ ≡ₒ ϕ′ →ₒ ψ′
cong-→ₒ {ϕ}{ϕ′}{ψ}{ψ′} ϕ=ϕ′ ψ=ψ′ k = to ,ₚ fro
  where
  to : (ϕ →ₒ ψ) k → (ϕ′ →ₒ ψ′) k
  to ϕk→ψk j j≤k ϕ′j = let ϕj = proj₂ₚ (ϕ=ϕ′ j) ϕ′j in
                       let ψj = ϕk→ψk j j≤k ϕj in
                        let ψ′j = proj₁ₚ (ψ=ψ′ j) ψj in ψ′j
  fro : (ϕ′ →ₒ ψ′) k → (ϕ →ₒ ψ) k
  fro ϕ′k→ψ′k j j≤k ϕj = let ϕ′j = proj₁ₚ (ϕ=ϕ′ j) ϕj in
                         let ψ′j = ϕ′k→ψ′k j j≤k ϕ′j in
                         let ψj = proj₂ₚ (ψ=ψ′ j) ψ′j in ψj

nonexpansive-→ : ∀ k {ϕ ψ : Setₒ} → ϕ →ₒ ψ ≡ₒ[ k ] (↓ k ϕ) →ₒ (↓ k ψ)
nonexpansive-→ k {ϕ}{ψ} i =
  (λ {(i<k ,ₚ ϕi→ψi) → i<k ,ₚ λ { j j≤i (j<k ,ₚ ϕj) → j<k ,ₚ (ϕi→ψi j j≤i ϕj)}})
  ,ₚ (λ { (i<k ,ₚ ϕi→ψi) → i<k ,ₚ λ {j j≤i ϕj →
     let ↓ϕj = ϕi→ψi j j≤i ((≤-transₚ{suc j}{suc i}{k} (s≤sₚ{j}{i} j≤i) i<k) ,ₚ ϕj) in
     proj₂ₚ ↓ϕj}})

open import BinaryConnective _→ₒ_ cong-→ₒ nonexpansive-→
  using () renaming (wellformed-connective to wellformed-implication) public

