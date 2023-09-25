{-# OPTIONS --without-K --prop #-}

open import Data.Nat using (ℕ)
open import EquivalenceRelationProp using (EquivalenceRelation; _⇔_; ⩦-refl; ⩦-sym; ⩦-trans)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import PropP

module RawSetO where

Setₒ : Set₁
Setₒ = ℕ → Prop

Predₒ : Set → Set₁
Predₒ A = A → Setₒ

⊤ᵖ : ∀{A} → Predₒ A
⊤ᵖ = λ _ _ → ⊤ₚ

infix 2 _≡ₒ_
_≡ₒ_ : Setₒ → Setₒ → Prop
S ≡ₒ T = ∀ k → S k ⇔ T k

≡ₒ-refl : ∀{S T : Setₒ} → S ≡ T → S ≡ₒ T
≡ₒ-refl refl i = ⩦-refl refl

≡ₒ-sym : ∀{S T : Setₒ} → S ≡ₒ T → T ≡ₒ S
≡ₒ-sym ST i = ⩦-sym (ST i)

≡ₒ-trans : ∀{S T R : Setₒ} → S ≡ₒ T → T ≡ₒ R → S ≡ₒ R
≡ₒ-trans ST TR i = ⩦-trans (ST i) (TR i)

instance
  SIL-Eqₒ : EquivalenceRelation Setₒ
  SIL-Eqₒ = record { _⩦_ = _≡ₒ_ ; ⩦-refl = ≡ₒ-refl
                   ; ⩦-sym = ≡ₒ-sym ; ⩦-trans = ≡ₒ-trans }

≡ᵖ-refl : ∀{A}{P Q : Predₒ A} → P ≡ Q → ∀ {a} → P a ≡ₒ Q a
≡ᵖ-refl refl {a} = ≡ₒ-refl refl

congruentᵖ : ∀{A}{B} (F : Predₒ A → Predₒ B) → Prop₁
congruentᵖ F = ∀ {P Q} → (∀ a → P a ≡ₒ Q a) → ∀ b → (F P b) ≡ₒ (F Q b)

downClosed : Setₒ → Prop
downClosed S = ∀ n → S n → ∀ k → k ≤ₚ n → S k

downClosedᵖ : ∀{A} (P : Predₒ A) → Prop
downClosedᵖ {A} P = ∀ (a : A) → downClosed (P a)

downClosed-fun : ∀{A}{B} (F : Predₒ A → Predₒ B) → Prop₁
downClosed-fun {A}{B} F = ∀ (P : Predₒ A) (b : B) → downClosedᵖ P → downClosed (F P b)
