{-# OPTIONS --without-K #-}

open import Data.Nat using (ℕ; zero; suc; _≤_; _∸_; z≤n; s≤s)
open import Function using (id; _∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; cong-app; subst)

module Iteration where

infixr 8 _^_
_^_ : ∀ {ℓ} {A : Set ℓ} → (A → A) → ℕ → (A → A)
f ^ zero     =  id
f ^ (suc n)  =  f ∘ (f ^ n)

iter-subtract : ∀{ℓ}{A : Set ℓ}{a : A} (F : A → A) (j k : ℕ) → j ≤ k
  → (F ^ j) ((F ^ (k ∸ j)) a) ≡ (F ^ k) a
iter-subtract {A = A} {a} F .zero k z≤n = refl
iter-subtract {A = A} {a} F (suc j) (suc k) (s≤s j≤k)
  rewrite iter-subtract{A = A}{a} F j k j≤k = refl
