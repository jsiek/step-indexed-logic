{-# OPTIONS --without-K #-}

open import Data.Nat using (ℕ)
open import EquivalenceRelation using (EquivalenceRelation; _⇔_; ⩦-refl; ⩦-sym; ⩦-trans)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

module RawSetO where

Setₒ : Set₁
Setₒ = ℕ → Set

Predₒ : Set → Set₁
Predₒ A = A → Setₒ

infix 2 _≡ₒ_
_≡ₒ_ : Setₒ → Setₒ → Set
S ≡ₒ T = ∀ k → S k ⇔ T k

≡ₒ-refl : ∀{S T : Setₒ}
  → S ≡ T
  → S ≡ₒ T
≡ₒ-refl refl i = ⩦-refl refl

≡ₒ-sym : ∀{S T : Setₒ}
  → S ≡ₒ T
  → T ≡ₒ S
≡ₒ-sym ST i = ⩦-sym (ST i)

≡ₒ-trans : ∀{S T R : Setₒ}
  → S ≡ₒ T
  → T ≡ₒ R
  → S ≡ₒ R
≡ₒ-trans ST TR i = ⩦-trans (ST i) (TR i)

instance
  SIL-Eqₒ : EquivalenceRelation Setₒ
  SIL-Eqₒ = record { _⩦_ = _≡ₒ_ ; ⩦-refl = ≡ₒ-refl
                   ; ⩦-sym = ≡ₒ-sym ; ⩦-trans = ≡ₒ-trans }

≡ᵖ-refl : ∀{A}{P Q : Predₒ A} → P ≡ Q → ∀ {a} → P a ≡ₒ Q a
≡ᵖ-refl refl {a} = ≡ₒ-refl refl

congruentᵖ : ∀{A}{B} (F : Predₒ A → Predₒ B) → Set₁
congruentᵖ F = ∀ {P Q} → (∀ a → P a ≡ₒ Q a) → ∀ b → (F P b) ≡ₒ (F Q b)
