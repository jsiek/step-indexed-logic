{-# OPTIONS --without-K --prop #-}

open import Relation.Binary.PropositionalEquality using (refl)

open import PropP
open import RawSetO
open import Variables
open import Env

module Pure where

_ₒ : Set → Setₒ
p ₒ = λ k → ⌊ p ⌋

strong-pure : ∀{Γ}{A}{Δ : Times Γ} (p : Set) (x : Γ ∋ A) → strong-var x (timeof x Δ) (λ δ → p ₒ)
strong-pure {Γ}{A}{Δ} p x
    with timeof x Δ
... | Now = λ δ j k k≤j → ≡ₒ-refl refl
... | Later = λ δ j k k≤j → ≡ₒ-refl refl

_ₚ : Prop → Setₒ
p ₚ = λ k → p

strong-pure-prop : ∀{Γ}{A}{Δ : Times Γ} (p : Prop) (x : Γ ∋ A) → strong-var x (timeof x Δ) (λ δ → p ₚ)
strong-pure-prop {Γ}{A}{Δ} p x
    with timeof x Δ
... | Now = λ δ j k k≤j → ≡ₒ-refl refl
... | Later = λ δ j k k≤j → ≡ₒ-refl refl
