
EXPERIMENTAL

\begin{code}
{-# OPTIONS --without-K --rewriting --prop #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; cong-app; subst)

open import StepIndexedLogic2

module LaterRewrites where

private variable ϕ ϕ′ ψ ψ′ þ : Setᵏ

postulate ▷→-≡ : (▷ᵒ (ϕ →ᵒ ψ))  ≡  (▷ᵒ ϕ) →ᵒ (▷ᵒ ψ)
{-# REWRITE ▷→-≡ #-}

postulate ▷×-≡ : ▷ᵒ (ϕ ×ᵒ ψ) ≡ (▷ᵒ ϕ) ×ᵒ (▷ᵒ ψ)
{-# REWRITE ▷×-≡ #-}

\end{code}
