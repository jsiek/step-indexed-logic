{-# OPTIONS --without-K --prop #-}

open import Relation.Binary.PropositionalEquality using (refl)

open import PropLib
open import RawSetO
open import Variables
open import Env

module Pure where

_ₒ : Set → Setₒ
p ₒ = λ k → Squash p

strong-pure : ∀{Γ}{A}{Δ : Times Γ} (p : Set) (x : Γ ∋ A) → strong-var x (timeof x Δ) (λ δ → p ₒ)
strong-pure {Γ}{A}{Δ} p x
    with timeof x Δ
... | Now = λ δ j k k≤j → ≡ₒ-refl refl
... | Later = λ δ j k k≤j → ≡ₒ-refl refl
