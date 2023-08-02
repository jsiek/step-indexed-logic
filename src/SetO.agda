{-# OPTIONS --without-K --prop #-}

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _≤_)
{-
open import Data.Product
   using (_×_; _,_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Unit using (tt; ⊤)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
-}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import EquivalenceRelation using (EquivalenceRelation; _⇔_; ⩦-refl; ⩦-sym; ⩦-trans)
open import RawSetO
open import Approx
open import Iteration
open import Variables

module SetO where

RecEnv : Context → Set₁
RecEnv [] = topᵖ 
RecEnv (A ∷ Γ) = (Predₒ A) × RecEnv Γ

downClosedᵈ : ∀{Γ} → RecEnv Γ → Prop₁
downClosedᵈ {[]} δ = ⊤
downClosedᵈ {A ∷ Γ} (P , δ) = (∀ a → downClosed (P a)) × downClosedᵈ δ

tzᵈ : ∀{Γ} → RecEnv Γ → Set
tzᵈ {[]} δ = ⊤
tzᵈ {A ∷ Γ} (P , δ) = (∀ a → (P a) 0) × tzᵈ δ

↓ᵈ : ℕ → ∀{Γ}{A} → Γ ∋ A → RecEnv Γ → RecEnv Γ
↓ᵈ k {A ∷ Γ} {.A} zeroᵒ (P , δ) = ↓ᵖ k P , δ
↓ᵈ k {A ∷ Γ} {B} (sucᵒ x) (P , δ) = P , ↓ᵈ k x δ

timeof : ∀{Γ}{A} → (x : Γ ∋ A) → Times Γ → Time
timeof {B ∷ Γ} zeroᵒ (t ∷ Δ) = t
timeof {B ∷ Γ} (sucᵒ x) (t ∷ Δ) = timeof x Δ

_≡ᵈ_ : ∀{Γ} → RecEnv Γ → RecEnv Γ → Set
_≡ᵈ_ {[]} δ δ′ = ⊤
_≡ᵈ_ {A ∷ Γ} (P , δ) (Q , δ′) = (∀ a → P a ≡ₒ Q a) × δ ≡ᵈ δ′

≡ᵈ-refl : ∀{Γ}{δ : RecEnv Γ} → δ ≡ᵈ δ
≡ᵈ-refl {[]} {δ} = tt
≡ᵈ-refl {A ∷ Γ} {(P , δ)} = (λ a → ≡ₒ-refl refl) , ≡ᵈ-refl

congruent : ∀{Γ : Context} → (RecEnv Γ → Setₒ) → Set₁
congruent S = ∀{δ δ′} → δ ≡ᵈ δ′ → (S δ) ≡ₒ (S δ′)

strongly-nonexpansive : ∀{Γ}{A} → (x : Γ ∋ A) → (RecEnv Γ → Setₒ) → Set₁
strongly-nonexpansive x F = ∀ δ j k → k ≤ j → F δ ≡ₒ[ k ] F (↓ᵈ j x δ)

strongly-contractive : ∀{Γ}{A} → (x : Γ ∋ A) → (RecEnv Γ → Setₒ) → Set₁
strongly-contractive x F = ∀ δ j k → k ≤ j → F δ ≡ₒ[ suc k ] F (↓ᵈ j x δ)

strong-var : ∀{Γ}{A} → (x : Γ ∋ A) → Time → (RecEnv Γ → Setₒ) → Set₁
strong-var x Now F = strongly-nonexpansive x F
strong-var x Later F = strongly-contractive x F

strong-fun : ∀{Γ} → Times Γ → (RecEnv Γ → Setₒ) → Set₁
strong-fun {Γ} Δ F = ∀{A} (x : Γ ∋ A) → strong-var x (timeof x Δ) F

{-
data Setᵒ (Γ : Context) (Δ : Times Γ) : Set₁ where
  make-Setᵒ : (sem : RecEnv Γ → Setₒ) → .(∀ (δ : RecEnv Γ) → downClosedᵈ δ → downClosed (sem δ)) → Setᵒ Γ Δ

# : ∀{Γ}{Δ} → Setᵒ Γ Δ → (RecEnv Γ → Setₒ)
# (make-Setᵒ sem dc) = sem

.down : ∀{Γ}{Δ} → (S : Setᵒ Γ Δ) → (∀ (δ : RecEnv Γ) → downClosedᵈ δ → downClosed (# S δ))
down (make-Setᵒ sem dc) = dc -- not allowed
-}

record Setᵒ (Γ : Context) (Δ : Times Γ) : Set₁ where
  field
    # : RecEnv Γ → Setₒ
    .down : ∀ δ → downClosedᵈ δ → downClosed (# δ)
    .strong : strong-fun Δ #
{-    
    congr : congruent #
-}    
open Setᵒ public

make-Setᵒ : ∀{Γ}{Δ} → (sem : RecEnv Γ → Setₒ)
  → .(∀ (δ : RecEnv Γ) → downClosedᵈ δ → downClosed (sem δ))
  → .(strong-fun Δ sem)
  → Setᵒ Γ Δ
make-Setᵒ sem dc s = record { # = sem ; down = dc ; strong = s}

--postulate down : ∀{Γ}{Δ} (ϕ : Setᵒ Γ Δ) → ∀ δ → downClosedᵈ δ → downClosed (# ϕ δ)
--postulate strong : ∀{Γ}{Δ} (ϕ : Setᵒ Γ Δ) → strong-fun Δ (# ϕ)
postulate congr : ∀{Γ}{Δ} (ϕ : Setᵒ Γ Δ) → congruent (# ϕ)

private variable Γ : Context
private variable Δ : Times Γ
private variable ϕ ψ þ : Setᵒ Γ Δ

abstract
  infix 2 _≡ᵒ_
  _≡ᵒ_ : ∀{Γ}{Δ : Times Γ} → Setᵒ Γ Δ → Setᵒ Γ Δ → Set₁
  S ≡ᵒ T = ∀ δ → # S δ ≡ₒ # T δ

  ≡ₒ⇒≡ᵒ : ∀{ϕ ψ : Setᵒ Γ Δ} → (∀ δ → # ϕ δ ≡ₒ # ψ δ) → ϕ ≡ᵒ ψ
  ≡ₒ⇒≡ᵒ P≡ₒQ = P≡ₒQ

  ≡ᵒ⇒≡ₒ : ∀{S T : Setᵒ Γ Δ}{δ} → S ≡ᵒ T → # S δ ≡ₒ # T δ
  ≡ᵒ⇒≡ₒ {S}{T}{δ}{k} {δ′} eq = eq δ′

  ≡ᵒ-intro : ∀{ϕ ψ : Setᵒ Γ Δ} → (∀ δ k → # ϕ δ k ⇔ # ψ δ k) → ϕ ≡ᵒ ψ
  ≡ᵒ-intro P⇔Q k = P⇔Q k

  ≡ᵒ-elim : ∀{S T : Setᵒ Γ Δ}{δ}{k} → S ≡ᵒ T → # S δ k ⇔ # T δ k
  ≡ᵒ-elim {S}{T}{δ}{k} {δ′}{k′} eq = eq δ′ k′

  ≡ᵒ-refl : ϕ ≡ ψ → ϕ ≡ᵒ ψ
  ≡ᵒ-refl {ϕ} refl ttᵖ k = (λ z → z) , (λ z → z)

  ≡ᵒ-sym : ϕ ≡ᵒ ψ → ψ ≡ᵒ ϕ
  ≡ᵒ-sym {ϕ}{ψ} PQ ttᵖ k
      with PQ ttᵖ k
  ... | (ϕ⇒ψ , ψ⇒ϕ) = ψ⇒ϕ , ϕ⇒ψ

  ≡ᵒ-trans : ϕ ≡ᵒ ψ → ψ ≡ᵒ þ → ϕ ≡ᵒ þ
  ≡ᵒ-trans PQ QR ttᵖ k
      with PQ ttᵖ k | QR ttᵖ k
  ... | (ϕ⇒ψ , ψ⇒ϕ) | (ψ⇒þ , þ⇒ψ) = (λ z → ψ⇒þ (ϕ⇒ψ z)) , (λ z → ψ⇒ϕ (þ⇒ψ z))

instance
  SIL-Eqᵒ : ∀{Γ}{Δ} → EquivalenceRelation (Setᵒ Γ Δ)
  SIL-Eqᵒ = record { _⩦_ = _≡ᵒ_ ; ⩦-refl = ≡ᵒ-refl
                   ; ⩦-sym = ≡ᵒ-sym ; ⩦-trans = ≡ᵒ-trans }
