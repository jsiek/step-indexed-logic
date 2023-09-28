\begin{comment}
\begin{code}
{-# OPTIONS --without-K --prop #-}

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import PropP
open import EquivalenceRelation using (EquivalenceRelation; _⇔_; ⩦-refl; ⩦-sym; ⩦-trans)
open import RawSetO
open import Approx
open import Iteration
open import Variables

module Env where
\end{code}
\end{comment}

\begin{code}
RecEnv : Context → Set₁
RecEnv [] = topᵖ 
RecEnv (A ∷ Γ) = (Predₒ A) × RecEnv Γ

downClosedᵈ : ∀{Γ} → RecEnv Γ → Prop
downClosedᵈ {[]} δ = ⊤ₚ
downClosedᵈ {A ∷ Γ} (P , δ) = (∀ a → downClosed (P a)) ×ₚ downClosedᵈ δ

↓ᵈ : ℕ → ∀{Γ}{A} → Γ ∋ A → RecEnv Γ → RecEnv Γ
↓ᵈ k {A ∷ Γ} {.A} zeroᵒ (P , δ) = ↓ᵖ k P , δ
↓ᵈ k {A ∷ Γ} {B} (sucᵒ x) (P , δ) = P , ↓ᵈ k x δ

_≡ᵈ_ : ∀{Γ} → RecEnv Γ → RecEnv Γ → Prop
_≡ᵈ_ {[]} δ δ′ = ⊤ₚ
_≡ᵈ_ {A ∷ Γ} (P , δ) (Q , δ′) = (∀ a → P a ≡ₒ Q a) ×ₚ δ ≡ᵈ δ′

≡ᵈ-refl : ∀{Γ}{δ : RecEnv Γ} → δ ≡ᵈ δ
≡ᵈ-refl {[]} {δ} = ttₚ
≡ᵈ-refl {A ∷ Γ} {(P , δ)} = (λ a → ≡ₒ-refl refl) ,ₚ ≡ᵈ-refl

congruent : ∀{Γ : Context} → (RecEnv Γ → Setₒ) → Prop₁
congruent S = ∀{δ δ′} → δ ≡ᵈ δ′ → (S δ) ≡ₒ (S δ′)

nonexpansive : ∀{Γ}{A} → (x : Γ ∋ A) → (RecEnv Γ → Setₒ) → Prop₁
nonexpansive x F = ∀ δ j k → k ≤ₚ j → F δ ≡ₒ[ k ] F (↓ᵈ j x δ)

contractive : ∀{Γ}{A} → (x : Γ ∋ A) → (RecEnv Γ → Setₒ) → Prop₁
contractive x F = ∀ δ j k → k ≤ₚ j → F δ ≡ₒ[ suc k ] F (↓ᵈ j x δ)

wellformed-var : ∀{Γ}{A} → (x : Γ ∋ A) → Time → (RecEnv Γ → Setₒ) → Prop₁
wellformed-var x Now F = nonexpansive x F
wellformed-var x Later F = contractive x F

wellformed-now⇒nonexpansive : ∀{Γ}{A}{x : Γ ∋ A}{Δ : Times Γ}{F : RecEnv Γ → Setₒ}
   → wellformed-var x (timeof x Δ) F → timeof x Δ ≡ Now → nonexpansive x F
wellformed-now⇒nonexpansive gF eq rewrite eq = gF

wellformed-later⇒contractive : ∀{Γ}{A}{x : Γ ∋ A}{Δ : Times Γ}{F : RecEnv Γ → Setₒ}
   → wellformed-var x (timeof x Δ) F → timeof x Δ ≡ Later → contractive x F
wellformed-later⇒contractive gF eq rewrite eq = gF

wellformed-fun : ∀{Γ} → Times Γ → (RecEnv Γ → Setₒ) → Prop₁
wellformed-fun {Γ} Δ F = ∀{A} (x : Γ ∋ A) → wellformed-var x (timeof x Δ) F
\end{code}

