{-# OPTIONS --without-K --prop #-}

{-

 Logic with Gas
 It's upward closed instead of downward closed.

-}

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
--open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import PropLib renaming (_×_ to _×ₚ_; _,_ to _,ₚ_; ⊥ to ⊥ₚ)
--using (_<_; z≤s; Σ; Σ-syntaxₚ)
open import EquivalenceRelation using (EquivalenceRelation; _⇔_; ⩦-refl; ⩦-sym; ⩦-trans)
open import RawSetO
open import Approx
open import Iteration
open import Variables
open import Env
open import StrongInduction

module SetG where
abstract

  record Setᵍ (Γ : Context) (Δ : Times Γ) : Set₁ where
    field
      # : RecEnv Γ → Setₒ
      up : ∀ δ → upClosedᵈ δ → upClosed (# δ)
      
open Setᵍ public

abstract

  ▷ᵍ : ∀{Γ}{Δ : Times Γ}
     → Setᵍ Γ Δ
       -----------------
     → Setᵍ Γ (laters Γ)
  ▷ᵍ {Γ}{Δ} S = record { # = λ δ k → Σ[ j ∈ ℕ ] j < k ×ₚ (# S) δ j
                       ; up = {!!}}

  _ᵍ : ∀{Γ} → Set → Setᵍ Γ (laters Γ)
  p ᵍ = record { # = (λ δ k → Squash p) ; up = λ δ _ n z k _ → z }

  ⊥ᵍ : ∀{Γ} → Setᵍ Γ (laters Γ)
  ⊥ᵍ = ⊥ ᵍ

  ⊤ᵍ : ∀{Γ} → Setᵍ Γ (laters Γ)
  ⊤ᵍ = record { # = (λ δ k → ⊤) ; up = λ δ _ n _ k _ → tt }

  infixr 7 _×ᵍ_
  _×ᵍ_ : ∀{Γ}{Δ₁ Δ₂ : Times Γ}
     → Setᵍ Γ Δ₁
     → Setᵍ Γ Δ₂
       ------------------------
     → Setᵍ Γ (combine Δ₁ Δ₂)
  S ×ᵍ T = record { # = (λ δ k → # S δ k ×ₚ # T δ k) ; up = {!!} }

private variable ϕ ϕ′ ψ ψ′ þ : Setᵍ [] []
private variable 𝒫 : List (Setᵍ [] [])

abstract
  Πᵍ : List (Setᵍ [] []) → Setᵍ [] []
  Πᵍ [] = ⊤ᵍ
  Πᵍ (P ∷ 𝒫) = P ×ᵍ Πᵍ 𝒫 

  upClosed-Πᵍ : (𝒫 : List (Setᵍ [] [])) → upClosed (# (Πᵍ 𝒫) ttᵖ)
  upClosed-Πᵍ [] = λ n _ k _ → tt
  upClosed-Πᵍ (ϕ ∷ 𝒫) n (ϕn ,ₚ ⊨𝒫n) k k≤n =
    up ϕ ttᵖ tt n ϕn k k≤n ,ₚ (upClosed-Πᵍ 𝒫 n ⊨𝒫n k k≤n) -- 

  infix 1 _⊢ᵍ_
  _⊢ᵍ_ : List (Setᵍ [] []) → Setᵍ [] [] → Prop
  𝒫 ⊢ᵍ P = ∀ n → # (Πᵍ 𝒫) ttᵖ n → (Σ[ k ∈ ℕ ] (# P ttᵖ k))

  ▷E : ∀{𝒫}{ϕ} → 𝒫 ⊢ᵍ ▷ᵍ ϕ → 𝒫 ⊢ᵍ ϕ
  ▷E ▷ϕ k 𝒫k =
     match (▷ϕ k 𝒫k) λ i ϕsi → (suc i) ,ₚ {!!}

  monoᵍ : ∀{𝒫}{ϕ} → 𝒫 ⊢ᵍ ϕ  →  𝒫 ⊢ᵍ  ▷ᵍ ϕ
  monoᵍ {𝒫}{ϕ} ⊢ϕ k 𝒫k =
      match (⊢ϕ k 𝒫k) λ j ϕj →
      j ,ₚ {!!}

  lobᵍ : (▷ᵍ ϕ) ∷ 𝒫 ⊢ᵍ ϕ  →  𝒫 ⊢ᵍ ϕ
  lobᵍ {ϕ}{𝒫} ▷ϕ⊢ϕ k 𝒫k = {!!}
    where
    aux : ∀ (k : ℕ) → # (Πᵍ 𝒫) ttᵖ k → (▷ᵍ ϕ ∷ 𝒫 ⊢ᵍ ϕ) → Σ[ j ∈ ℕ ] (# ϕ ttᵖ j)
    aux = strong-induction si
      where
      si : (n : ℕ) → ((i : ℕ) → i < n → # (Πᵍ 𝒫) ttᵖ i → ▷ᵍ ϕ ∷ 𝒫 ⊢ᵍ ϕ → Σ-syntaxₚ ℕ (# ϕ ttᵖ))
          → # (Πᵍ 𝒫) ttᵖ n
          → ▷ᵍ ϕ ∷ 𝒫 ⊢ᵍ ϕ → Σ[ j ∈ ℕ ] (# ϕ ttᵖ j)
      si n IH 𝒫n ▷ϕ⊢ϕ =
        match (IH {!!} {!!} {!!} ▷ϕ⊢ϕ) λ i ϕi → 
        {!!}


{-      
      let xx = step (k ,ₚ (({!!} ,ₚ ({!!} ,ₚ {!!})) ,ₚ 𝒫k)) in
      xx
-}
