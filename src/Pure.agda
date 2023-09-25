{-# OPTIONS --without-K --prop #-}

open import Relation.Binary.PropositionalEquality using (refl)

open import PropP
open import RawSetO
open import Variables
open import Env

module Pure where

_ₒ : Set → Setₒ
p ₒ = λ k → ⌊ p ⌋

wellformed-pure : ∀{Γ}{A}{Δ : Times Γ} (p : Set) (x : Γ ∋ A) → wellformed-var x (timeof x Δ) (λ δ → p ₒ)
wellformed-pure {Γ}{A}{Δ} p x
    with timeof x Δ
... | Now = λ δ j k k≤j → ≡ₒ-refl refl
... | Later = λ δ j k k≤j → ≡ₒ-refl refl

_ₚ : Prop → Setₒ
p ₚ = λ k → p

wellformed-pure-prop : ∀{Γ}{A}{Δ : Times Γ} (p : Prop) (x : Γ ∋ A) → wellformed-var x (timeof x Δ) (λ δ → p ₚ)
wellformed-pure-prop {Γ}{A}{Δ} p x
    with timeof x Δ
... | Now = λ δ j k k≤j → ≡ₒ-refl refl
... | Later = λ δ j k k≤j → ≡ₒ-refl refl
