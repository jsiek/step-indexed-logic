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

module Pure where

_ₒ : Set → Setₒ
p ₒ = λ k → Squash p

strong-pure : ∀{Γ}{A}{Δ : Times Γ} (p : Set) (x : Γ ∋ A) → strong-var x (timeof x Δ) (λ δ → p ₒ)
strong-pure {Γ}{A}{Δ} p x
    with timeof x Δ
... | Now = λ δ j k k≤j → ≡ₒ-refl refl
... | Later = λ δ j k k≤j → ≡ₒ-refl refl
