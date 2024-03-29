\begin{comment}
\begin{code}
{-# OPTIONS --without-K #-}
module July2024.SILInterface where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat
   using (ℕ; zero; suc; _≤_; _<_; _+_; _∸_; z≤n; s≤s; _≤′_; ≤′-step)
open import Data.Nat.Properties
   using (≤-refl; ≤-antisym; ≤-trans; ≤-step; ≤⇒≤′; ≤′⇒≤; n≤1+n; <⇒≤; s≤′s)
open import Data.Product
   using (_×_; _,_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt; ⊤)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; cong-app; subst)
open import Relation.Nullary using (¬_)
open import Function using (id; _∘_)
open import Level using (Lift)
open import EquivalenceRelation public
open import July2024.Prelude

\end{code}
\end{comment}

\begin{code}
record SIL : Set₂ where
  infix 1 _⊢ᵒ_
  infix 2 _≡ˢ_

  field
    {- Open Step-Indexed Propositions -}
    Setˢ : (Γ : Context) → Times Γ → Set₁
    ♯ : ∀{Γ Δ} → Setˢ Γ Δ → RecEnv Γ → Setᵒ

  field
    {- Formulas -}
    ⊤ᵒ : Setᵒ
    ⊥ᵒ : Setᵒ
    ▷ᵒ_ : Setᵒ → Setᵒ
    _×ᵒ_ : Setᵒ → Setᵒ → Setᵒ
    _⊎ᵒ_ : Setᵒ → Setᵒ → Setᵒ
    _→ᵒ_ : Setᵒ → Setᵒ → Setᵒ
    ∀ᵒ : (A → Setᵒ) → Setᵒ
    ∃ᵒ : (A → Setᵒ) → Setᵒ
    ↓ᵒ : ℕ → Setᵒ → Setᵒ
    _ᵒ : Set → Setᵒ
    μᵒ : (A → Setˢ (A ∷ []) (cons Later ∅)) → (A → Setᵒ)

    {- Proof Theory -}
    _⊢ᵒ_ : List Setᵒ → Setᵒ → Set
    monoᵒ : ∀{𝒫 ϕ} → 𝒫 ⊢ᵒ ϕ  →  𝒫 ⊢ᵒ (▷ᵒ ϕ)
    lobᵒ : ∀{𝒫 ϕ} → (▷ᵒ ϕ) ∷ 𝒫 ⊢ᵒ ϕ  →  𝒫 ⊢ᵒ ϕ
    ▷× : ∀{𝒫 ϕ ψ} → 𝒫 ⊢ᵒ (▷ᵒ (ϕ ×ᵒ ψ))  →  𝒫 ⊢ᵒ (▷ᵒ ϕ) ×ᵒ (▷ᵒ ψ)
    ▷⊎ : ∀{𝒫 ϕ ψ} → 𝒫 ⊢ᵒ (▷ᵒ (ϕ ⊎ᵒ ψ))  →  𝒫 ⊢ᵒ (▷ᵒ ϕ) ⊎ᵒ (▷ᵒ ψ)
    ▷→ : ∀{𝒫 ϕ ψ} → 𝒫 ⊢ᵒ (▷ᵒ (ϕ →ᵒ ψ))  →  𝒫 ⊢ᵒ (▷ᵒ ϕ) →ᵒ (▷ᵒ ψ)
    ▷∀ : ∀{𝒫}{ϕᵃ : A → Setᵒ} → 𝒫 ⊢ᵒ ▷ᵒ (∀ᵒ ϕᵃ)  →  𝒫 ⊢ᵒ (∀ᵒ (λ a → ▷ᵒ (ϕᵃ a)))
    substᵒ : ∀{𝒫 ϕ ψ} → ϕ ≡ᵒ ψ  →  𝒫 ⊢ᵒ ϕ  →  𝒫 ⊢ᵒ ψ
    ttᵒ : ∀{𝒫} → 𝒫 ⊢ᵒ ⊤ᵒ
    ⊥-elimᵒ : ∀{𝒫} → 𝒫 ⊢ᵒ ⊥ᵒ → (ϕ : Setᵒ) → 𝒫 ⊢ᵒ ϕ
    _,ᵒ_ : ∀{𝒫 ϕ ψ} → 𝒫 ⊢ᵒ ϕ  →  𝒫 ⊢ᵒ ψ  →  𝒫 ⊢ᵒ ϕ ×ᵒ ψ
    proj₁ᵒ : ∀{𝒫 ϕ ψ} → 𝒫 ⊢ᵒ ϕ ×ᵒ ψ  →  𝒫 ⊢ᵒ ϕ
    proj₂ᵒ : ∀{𝒫 ϕ ψ} → 𝒫 ⊢ᵒ ϕ ×ᵒ ψ  →  𝒫 ⊢ᵒ ψ
    inj₁ᵒ : ∀{𝒫 ϕ ψ} → 𝒫 ⊢ᵒ ϕ → 𝒫 ⊢ᵒ ϕ ⊎ᵒ ψ
    inj₂ᵒ : ∀{𝒫 ϕ ψ} → 𝒫 ⊢ᵒ ψ → 𝒫 ⊢ᵒ ϕ ⊎ᵒ ψ
    caseᵒ : ∀{𝒫 ϕ ψ þ} → 𝒫 ⊢ᵒ ϕ ⊎ᵒ ψ  →  ϕ ∷ 𝒫 ⊢ᵒ þ  →  ψ ∷ 𝒫 ⊢ᵒ þ  →  𝒫 ⊢ᵒ þ
    →ᵒI : ∀{𝒫 ϕ ψ} → ϕ ∷ 𝒫 ⊢ᵒ ψ  →  𝒫 ⊢ᵒ ϕ →ᵒ ψ
    appᵒ : ∀{𝒫 ϕ ψ} → 𝒫 ⊢ᵒ ϕ →ᵒ ψ  →  𝒫 ⊢ᵒ ϕ  →  𝒫 ⊢ᵒ ψ
    ⊢ᵒ-∀-intro : ∀{𝒫}{ϕᵃ : A → Setᵒ} → (∀ a → 𝒫 ⊢ᵒ ϕᵃ a)  →  𝒫 ⊢ᵒ ∀ᵒ ϕᵃ
    instᵒ : ∀{𝒫}{ϕᵃ : A → Setᵒ} → 𝒫 ⊢ᵒ ∀ᵒ ϕᵃ  →  (a : A)  →  𝒫 ⊢ᵒ ϕᵃ a
    ⊢ᵒ-∃-intro : ∀{𝒫}{ϕᵃ : A → Setᵒ}{{_ : Inhabited A}} → (a : A)  →  𝒫 ⊢ᵒ ϕᵃ a  →  𝒫 ⊢ᵒ ∃ᵒ ϕᵃ
    ⊢ᵒ-∃-elim : ∀{𝒫}{ϕᵃ : A → Setᵒ}{þ : Setᵒ}{{_ : Inhabited A}}
       → 𝒫 ⊢ᵒ ∃ᵒ ϕᵃ  →  (∀ a → ϕᵃ a ∷ 𝒫 ⊢ᵒ þ)  →  𝒫 ⊢ᵒ þ
    constᵒI : ∀{𝒫}{p : Set} → p → 𝒫 ⊢ᵒ p ᵒ
    constᵒE : ∀{𝒫 þ}{p : Set} → 𝒫 ⊢ᵒ p ᵒ  →  (p → 𝒫 ⊢ᵒ þ)  →  𝒫 ⊢ᵒ þ
    Zᵒ : ∀{𝒫 ϕ} → ϕ ∷ 𝒫 ⊢ᵒ ϕ
    Sᵒ : ∀{𝒫 ϕ ψ} → 𝒫 ⊢ᵒ ψ  →  ϕ ∷ 𝒫 ⊢ᵒ ψ
    ⊢ᵒ-sucP : ∀{𝒫 ϕ ψ} → 𝒫 ⊢ᵒ ϕ  →  (∀{n} → # ϕ (suc n) → 𝒫 ⊢ᵒ ψ)  →  𝒫 ⊢ᵒ ψ
    fixpointᵒ : ∀{A} (P : A → Setˢ (A ∷ []) (cons Later ∅)) (a : A) → μᵒ P a ≡ᵒ ♯ (P a) (μᵒ P , ttᵖ)

    {- Open Formulas -}
    ⊤ˢ : Setˢ Γ (laters Γ)
    ⊥ˢ : Setˢ Γ (laters Γ)
    _∈_ : A → (x : Γ ∋ A) → Setˢ Γ (var-now Γ x)
    ▷ˢ : Setˢ Γ Δ → Setˢ Γ (laters Γ)
    ↓ˢ : ℕ → Setˢ Γ Δ → Setˢ Γ Δ
    letˢ : (A → Setˢ Γ Δ) → Setˢ (A ∷ Γ) (cons Later Δ) → Setˢ Γ Δ   
    μˢ : (A → Setˢ (A ∷ Γ) (cons Later Δ)) → (A → Setˢ Γ Δ)
    _→ˢ_ : Setˢ Γ Δ₁ → Setˢ Γ Δ₂ → Setˢ Γ (Δ₁ ∪ Δ₂)
    _×ˢ_ : Setˢ Γ Δ₁ → Setˢ Γ Δ₂ → Setˢ Γ (Δ₁ ∪ Δ₂)
    _⊎ˢ_ : Setˢ Γ Δ₁ → Setˢ Γ Δ₂ → Setˢ Γ (Δ₁ ∪ Δ₂)
    ∀ˢ : (A → Setˢ Γ Δ) → Setˢ Γ Δ
    ∃ˢ : {{_ : Inhabited A}} → (A → Setˢ Γ Δ) → Setˢ Γ Δ
    _ˢ : Set → Setˢ Γ (laters Γ)

    {- Equations for Open Formulas -}
    ♯⊤ˢ : ∀ {Γ} (δ : RecEnv Γ) → ♯ ⊤ˢ δ ≡ ⊤ᵒ

    _≡ˢ_ : Setˢ Γ Δ → Setˢ Γ Δ → Set₁
    fixpointˢ : ∀ (F : A → Setˢ (A ∷ Γ) (cons Later Δ)) (a : A) → μˢ F a ≡ˢ letˢ (μˢ F) (F a)
\end{code}
