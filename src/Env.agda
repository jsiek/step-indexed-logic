{-# OPTIONS --without-K --prop #-}

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product
   using (_×_; _,_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import PropLib renaming (_×_ to _×ₚ_; _,_ to _,ₚ_)
open import EquivalenceRelation using (EquivalenceRelation; _⇔_; ⩦-refl; ⩦-sym; ⩦-trans)
open import RawSetO
open import Approx
open import Iteration
open import Variables

module Env where

RecEnv : Context → Set₁
RecEnv [] = topᵖ 
RecEnv (A ∷ Γ) = (Predₒ A) × RecEnv Γ

downClosedᵈ : ∀{Γ} → RecEnv Γ → Prop
downClosedᵈ {[]} δ = ⊤
downClosedᵈ {A ∷ Γ} (P , δ) = (∀ a → downClosed (P a)) ×ₚ downClosedᵈ δ

upClosedᵈ : ∀{Γ} → RecEnv Γ → Prop
upClosedᵈ {[]} δ = ⊤
upClosedᵈ {A ∷ Γ} (P , δ) = (∀ a → upClosed (P a)) ×ₚ upClosedᵈ δ

tzᵈ : ∀{Γ} → RecEnv Γ → Prop
tzᵈ {[]} δ = ⊤
tzᵈ {A ∷ Γ} (P , δ) = (∀ a → (P a) 0) ×ₚ tzᵈ δ

↓ᵈ : ℕ → ∀{Γ}{A} → Γ ∋ A → RecEnv Γ → RecEnv Γ
↓ᵈ k {A ∷ Γ} {.A} zeroᵒ (P , δ) = ↓ᵖ k P , δ
↓ᵈ k {A ∷ Γ} {B} (sucᵒ x) (P , δ) = P , ↓ᵈ k x δ

_≡ᵈ_ : ∀{Γ} → RecEnv Γ → RecEnv Γ → Prop
_≡ᵈ_ {[]} δ δ′ = ⊤
_≡ᵈ_ {A ∷ Γ} (P , δ) (Q , δ′) = (∀ a → P a ≡ₒ Q a) ×ₚ δ ≡ᵈ δ′

≡ᵈ-refl : ∀{Γ}{δ : RecEnv Γ} → δ ≡ᵈ δ
≡ᵈ-refl {[]} {δ} = tt
≡ᵈ-refl {A ∷ Γ} {(P , δ)} = (λ a → ≡ₒ-refl refl) ,ₚ ≡ᵈ-refl

congruent : ∀{Γ : Context} → (RecEnv Γ → Setₒ) → Prop₁
congruent S = ∀{δ δ′} → δ ≡ᵈ δ′ → (S δ) ≡ₒ (S δ′)

strongly-nonexpansive : ∀{Γ}{A} → (x : Γ ∋ A) → (RecEnv Γ → Setₒ) → Prop₁
strongly-nonexpansive x F = ∀ δ j k → k ≤ j → F δ ≡ₒ[ k ] F (↓ᵈ j x δ)

strongly-contractive : ∀{Γ}{A} → (x : Γ ∋ A) → (RecEnv Γ → Setₒ) → Prop₁
strongly-contractive x F = ∀ δ j k → k ≤ j → F δ ≡ₒ[ suc k ] F (↓ᵈ j x δ)

strong-var : ∀{Γ}{A} → (x : Γ ∋ A) → Time → (RecEnv Γ → Setₒ) → Prop₁
strong-var x Now F = strongly-nonexpansive x F
strong-var x Later F = strongly-contractive x F

strong-now⇒nonexpansive : ∀{Γ}{A}{x : Γ ∋ A}{Δ : Times Γ}{F : RecEnv Γ → Setₒ}
   → strong-var x (timeof x Δ) F → timeof x Δ ≡ Now → strongly-nonexpansive x F
strong-now⇒nonexpansive gF eq rewrite eq = gF

strong-later⇒contractive : ∀{Γ}{A}{x : Γ ∋ A}{Δ : Times Γ}{F : RecEnv Γ → Setₒ}
   → strong-var x (timeof x Δ) F → timeof x Δ ≡ Later → strongly-contractive x F
strong-later⇒contractive gF eq rewrite eq = gF

strong-fun : ∀{Γ} → Times Γ → (RecEnv Γ → Setₒ) → Prop₁
strong-fun {Γ} Δ F = ∀{A} (x : Γ ∋ A) → strong-var x (timeof x Δ) F

