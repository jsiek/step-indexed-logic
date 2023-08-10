{-# OPTIONS --without-K --prop #-}

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product
   using (_×_; _,_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import PropP
open import EquivalenceRelationProp using (EquivalenceRelation; _⇔_; ⩦-refl; ⩦-sym; ⩦-trans)
open import RawSetO
open import Approx
open import Iteration
open import Variables
open import Env

module SetO where

record Setᵒ (Γ : Context) (Δ : Times Γ) : Set₁ where
  field
    # : RecEnv Γ → Setₒ
    down : ∀ δ → downClosedᵈ δ → downClosed (# δ)
    strong : strong-fun Δ #
    congr : congruent #

open Setᵒ public

make-Setᵒ : ∀{Γ}{Δ} → (sem : RecEnv Γ → Setₒ)
  → (∀ (δ : RecEnv Γ) → downClosedᵈ δ → downClosed (sem δ))
  → (strong-fun Δ sem)
  → (congruent sem)
  → Setᵒ Γ Δ
make-Setᵒ sem dc s c = record { # = sem ; down = dc ; strong = s ; congr = c}

private variable Γ : Context
private variable Δ : Times Γ
private variable ϕ ψ þ : Setᵒ Γ Δ

abstract
  infix 2 _≡ᵒ_
  _≡ᵒ_ : Setᵒ Γ Δ → Setᵒ Γ Δ → Prop₁
  ϕ ≡ᵒ ψ = ∀ δ → # ϕ δ ≡ₒ # ψ δ

  ≡ₒ⇒≡ᵒ : (∀ δ → # ϕ δ ≡ₒ # ψ δ) → ϕ ≡ᵒ ψ
  ≡ₒ⇒≡ᵒ P≡ₒQ = P≡ₒQ

  ≡ᵒ⇒≡ₒ : ∀{δ} → ϕ ≡ᵒ ψ → # ϕ δ ≡ₒ # ψ δ
  ≡ᵒ⇒≡ₒ {ϕ}{ψ}{δ}{k} {δ′} eq = eq δ′

  ≡ᵒ-intro : ∀{ϕ ψ : Setᵒ Γ Δ} → (∀ δ k → # ϕ δ k ⇔ # ψ δ k) → ϕ ≡ᵒ ψ
  ≡ᵒ-intro P⇔Q k = P⇔Q k

  ≡ᵒ-elim : ∀{δ}{k} → ϕ ≡ᵒ ψ → # ϕ δ k ⇔ # ψ δ k
  ≡ᵒ-elim {ϕ}{ψ}{δ}{k} {δ′}{k′} eq = eq δ′ k′

  ≡ᵒ-refl : ϕ ≡ ψ → ϕ ≡ᵒ ψ
  ≡ᵒ-refl {ϕ} refl ttᵖ k = (λ z → z) ,ₚ (λ z → z)

  ≡ᵒ-sym : ϕ ≡ᵒ ψ → ψ ≡ᵒ ϕ
  ≡ᵒ-sym {ϕ}{ψ} PQ ttᵖ k
      with PQ ttᵖ k
  ... | (ϕ⇒ψ ,ₚ ψ⇒ϕ) = ψ⇒ϕ ,ₚ ϕ⇒ψ

  ≡ᵒ-trans : ϕ ≡ᵒ ψ → ψ ≡ᵒ þ → ϕ ≡ᵒ þ
  ≡ᵒ-trans PQ QR ttᵖ k
      with PQ ttᵖ k | QR ttᵖ k
  ... | (ϕ⇒ψ ,ₚ ψ⇒ϕ) | (ψ⇒þ ,ₚ þ⇒ψ) = (λ z → ψ⇒þ (ϕ⇒ψ z)) ,ₚ (λ z → ψ⇒ϕ (þ⇒ψ z))

instance
  SIL-Eqᵒ : ∀{Γ}{Δ} → EquivalenceRelation (Setᵒ Γ Δ)
  SIL-Eqᵒ = record { _⩦_ = _≡ᵒ_ ; ⩦-refl = ≡ᵒ-refl
                   ; ⩦-sym = ≡ᵒ-sym ; ⩦-trans = ≡ᵒ-trans }
