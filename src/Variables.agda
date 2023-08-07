{-# OPTIONS --without-K #-}
open import Data.List using (List; []; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

module Variables where

Context : Set₁
Context = List Set

data _∋_ : Context → Set → Set₁ where
  zeroᵒ : ∀{Γ}{A} → (A ∷ Γ) ∋ A
  sucᵒ : ∀{Γ}{A}{B} → Γ ∋ B → (A ∷ Γ) ∋ B

data Time : Set where
  Now : Time
  Later : Time

-- Phil: would prefer if this were a list
data Times : Context → Set₁ where
  [] : Times []
  _∷_ : ∀{Γ}{A} → Time → Times Γ → Times (A ∷ Γ)

laters : ∀ (Γ : Context) → Times Γ
laters [] = []
laters (A ∷ Γ) = Later ∷ (laters Γ)

var-now : ∀ (Γ : Context) → ∀{A} → (x : Γ ∋ A) → Times Γ
var-now (B ∷ Γ) zeroᵒ = Now ∷ (laters Γ)
var-now (B ∷ Γ) (sucᵒ x) = Later ∷ (var-now Γ x)

choose : Time → Time → Time
choose Now Now = Now
choose Now Later = Now
choose Later Now = Now
choose Later Later = Later

combine : ∀{Γ} (Δ₁ Δ₂ : Times Γ) → Times Γ
combine {[]} Δ₁ Δ₂ = []
combine {A ∷ Γ} (x ∷ Δ₁) (y ∷ Δ₂) = (choose x y) ∷ (combine Δ₁ Δ₂)

timeof : ∀{Γ}{A} → (x : Γ ∋ A) → Times Γ → Time
timeof {B ∷ Γ} zeroᵒ (t ∷ Δ) = t
timeof {B ∷ Γ} (sucᵒ x) (t ∷ Δ) = timeof x Δ

timeof-later : ∀{Γ}{A} → (x : Γ ∋ A) → (timeof x (laters Γ)) ≡ Later
timeof-later {B ∷ Γ} zeroᵒ = refl
timeof-later {B ∷ Γ} (sucᵒ x) = timeof-later x

timeof-combine : ∀{Γ}{Δ₁ Δ₂ : Times Γ}{A}{x : Γ ∋ A}
   → timeof x (combine Δ₁ Δ₂) ≡ choose (timeof x Δ₁) (timeof x Δ₂)
timeof-combine {B ∷ Γ} {s ∷ Δ₁} {t ∷ Δ₂} {.B} {zeroᵒ} = refl
timeof-combine {B ∷ Γ} {s ∷ Δ₁} {t ∷ Δ₂} {A} {sucᵒ x} =
  timeof-combine {Γ} {Δ₁} {Δ₂} {A} {x}
