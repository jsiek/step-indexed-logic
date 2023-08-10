{-# OPTIONS --without-K --prop #-}

open import Data.Nat using (ℕ; zero; suc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import EquivalenceRelationProp
open import RawSetO
open import PropP

module Approx where

↓ : ℕ → Setₒ → Setₒ
↓ k S j = j <ₚ k ×ₚ (S j)

↑ : ℕ → Setₒ → Setₒ
↑ k S j = k <ₚ j ×ₚ (S j)

infix 2 _≡ₒ[_]_
_≡ₒ[_]_ : Setₒ → ℕ → Setₒ → Prop
ϕ ≡ₒ[ k ] ψ =  ↓ k ϕ  ≡ₒ  ↓ k ψ

abstract
  ≡ₒ[]-refl : ∀ {ϕ}{ψ}{k} → ϕ ≡ ψ → ϕ ≡ₒ[ k ] ψ
  ≡ₒ[]-refl {ϕ}{ψ}{k} refl = ≡ₒ-refl{S = ↓ k ϕ} refl

  ≡ₒ[]-sym : ∀ {ϕ}{ψ}{k} → ϕ ≡ₒ[ k ] ψ → ψ ≡ₒ[ k ] ϕ
  ≡ₒ[]-sym {ϕ}{ψ}{k} ϕ=ψ = ≡ₒ-sym{S = ↓ k ϕ}{↓ k ψ} ϕ=ψ

  ≡ₒ[]-trans : ∀ {ϕ}{ψ}{þ}{k} → ϕ ≡ₒ[ k ] ψ → ψ ≡ₒ[ k ] þ → ϕ ≡ₒ[ k ] þ
  ≡ₒ[]-trans {ϕ}{ψ}{þ}{k} ϕ=ψ ψ=þ = ≡ₒ-trans{S = ↓ k ϕ}{↓ k ψ}{↓ k þ} ϕ=ψ ψ=þ
{- This isn't working, see Iteration.agda -}
instance
  SIL-Eq[] : ∀{k} → EquivalenceRelation Setₒ
  SIL-Eq[] {k} = record { _⩦_ = λ ϕ ψ → ϕ ≡ₒ[ k ] ψ ; ⩦-refl = ≡ₒ[]-refl{k = k} ; ⩦-sym = ≡ₒ[]-sym{k = k} ; ⩦-trans = ≡ₒ[]-trans{k = k} }

≡ₒ[0] : ∀{ϕ ψ : Setₒ} → ϕ ≡ₒ[ 0 ] ψ
≡ₒ[0] k = (λ ↓0ϕ → ⊥-elimₚ (n≮0ₚ{k} (proj₁ₚ ↓0ϕ))) ,ₚ λ ↓0ψ → ⊥-elimₚ (n≮0ₚ{k} (proj₁ₚ ↓0ψ))

cong-approx : ∀ {ϕ ψ : Setₒ} k → ϕ ≡ₒ ψ → ϕ ≡ₒ[ k ] ψ
cong-approx {ϕ} {ψ} k ϕ=ψ i = (λ {(i<k ,ₚ ϕi) → i<k ,ₚ (proj₁ₚ (ϕ=ψ i)) ϕi })
                             ,ₚ (λ {(i<k ,ₚ ψi) → i<k ,ₚ (proj₂ₚ (ϕ=ψ i)) ψi })

↓ᵖ : ℕ → ∀{A} → Predₒ A → Predₒ A
↓ᵖ j P a = ↓ j (P a)

↑ᵖ : ℕ → ∀{A} → Predₒ A → Predₒ A
↑ᵖ j P a = ↑ j (P a)

cong-approxᵖ : ∀{A}{k : ℕ} → congruentᵖ{A}{A} (↓ᵖ k)
cong-approxᵖ {A} {k} {P} {Q} eq a i =
  (λ {(i<k ,ₚ Pa) → i<k ,ₚ proj₁ₚ (eq a i) Pa}) ,ₚ λ {(i<k ,ₚ Qa) → i<k ,ₚ proj₂ₚ (eq a i) Qa}

j≤k⇒↓kϕ≡[j]ϕ : ∀{j k} (ϕ : Setₒ) → j ≤ₚ k → ↓ k ϕ ≡ₒ[ j ] ϕ
j≤k⇒↓kϕ≡[j]ϕ {j} {k} ϕ j≤k i =
  (λ {(i<j ,ₚ (i<k ,ₚ ϕi)) → i<j ,ₚ ϕi}) ,ₚ (λ {(i<j ,ₚ ϕi) → i<j ,ₚ (≤-transₚ{suc i}{j}{k} i<j j≤k ,ₚ ϕi)})

lemma17 : ∀ {ϕ} k → ↓ (suc k) ϕ ≡ₒ[ k ] ϕ
lemma17 {ϕ} k = j≤k⇒↓kϕ≡[j]ϕ {k}{suc k} ϕ (n≤1+nₚ k)

equiv-approx : ∀{ϕ ψ : Setₒ} → (∀ k → ϕ ≡ₒ[ k ] ψ) → ϕ ≡ₒ ψ
equiv-approx ∀k,ϕ=[k]ψ i =
  let ↓ϕ⇔↓ψ = ∀k,ϕ=[k]ψ (suc i) i in
  (λ ϕi → let ↓siψi = proj₁ₚ ↓ϕ⇔↓ψ ((s≤sₚ{i}{i} (≤-reflₚ{i})) ,ₚ ϕi) in proj₂ₚ ↓siψi)
  ,ₚ (λ ψi → let ↓siϕi = proj₂ₚ ↓ϕ⇔↓ψ ((s≤sₚ{i}{i} (≤-reflₚ{i})) ,ₚ ψi) in proj₂ₚ ↓siϕi)

