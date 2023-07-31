{-# OPTIONS --without-K #-}

open import Data.Unit using (tt; ⊤)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; s≤s; _≤′_; ≤′-step)
open import Data.Nat.Properties using (<⇒≤; ≤⇒≤′; ≤′⇒≤; ≤-trans)
open import Data.Product
   using (_×_; _,_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
open import SetO
open import EquivalenceRelation

module Approx where

↓ : ℕ → Setₒ → Setₒ
↓ k S zero = ⊤
↓ k S (suc j) = suc j < k × (S (suc j))

infix 2 _≡ₒ[_]_
_≡ₒ[_]_ : Setₒ → ℕ → Setₒ → Set
ϕ ≡ₒ[ k ] ψ =  ↓ k ϕ  ≡ₒ  ↓ k ψ

↓ᵖ : ℕ → ∀{A} → Predₒ A → Predₒ A
↓ᵖ j P a = ↓ j (P a)

cong-↓ : ∀{A}{k : ℕ} → congᵖ{A}{A} (↓ᵖ k)
cong-↓ {A} {k} {P} {Q} eq a zero = (λ _ → tt) , λ _ → tt
cong-↓ {A} {k} {P} {Q} eq a (suc i) =
   (λ {(si≤k , Pasi) → si≤k , (proj₁ (eq a (suc i)) Pasi)})
   ,
   λ {(si≤k , Qasi) → si≤k , (proj₂ (eq a (suc i)) Qasi)}

j≤k⇒↓kϕ≡[j]ϕ : ∀{j k} (ϕ : Setₒ) → j ≤ k → ↓ k ϕ ≡ₒ[ j ] ϕ
j≤k⇒↓kϕ≡[j]ϕ {j} {k} ϕ j≤k zero = (λ _ → tt) , (λ _ → tt)
j≤k⇒↓kϕ≡[j]ϕ {j} {k} ϕ j≤k (suc i) = (λ {(a , b , c) → a , c}) , λ {(a , b) → a , ≤-trans a j≤k , b}

