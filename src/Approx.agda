{-# OPTIONS --without-K --prop #-}

open import Data.Unit using (tt; ⊤)
open import Data.Nat using (ℕ; zero; suc) --; _≤_; _<_; s≤s; _≤′_; ≤′-step)
open import RawSetO
open import EquivalenceRelationProp
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans)
open import PropLib

module Approx where

↓ : ℕ → Setₒ → Setₒ
↓ k S j = j < k × (S j)

↑ : ℕ → Setₒ → Setₒ
↑ k S j = k < j × (S j)

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
≡ₒ[0] k = (λ ↓0ϕ → ⊥-elim (n≮0{k} (proj₁ ↓0ϕ))) , λ ↓0ψ → ⊥-elim (n≮0{k} (proj₁ ↓0ψ))

cong-approx : ∀ {ϕ ψ : Setₒ} k → ϕ ≡ₒ ψ → ϕ ≡ₒ[ k ] ψ
cong-approx {ϕ} {ψ} k ϕ=ψ i = (λ {(i<k , ϕi) → i<k , (proj₁ (ϕ=ψ i)) ϕi })
                             , (λ {(i<k , ψi) → i<k , (proj₂ (ϕ=ψ i)) ψi })

↓ᵖ : ℕ → ∀{A} → Predₒ A → Predₒ A
↓ᵖ j P a = ↓ j (P a)

↑ᵖ : ℕ → ∀{A} → Predₒ A → Predₒ A
↑ᵖ j P a = ↑ j (P a)

cong-approxᵖ : ∀{A}{k : ℕ} → congruentᵖ{A}{A} (↓ᵖ k)
cong-approxᵖ {A} {k} {P} {Q} eq a i =
  (λ {(i<k , Pa) → i<k , proj₁ (eq a i) Pa}) , λ {(i<k , Qa) → i<k , proj₂ (eq a i) Qa}

j≤k⇒↓kϕ≡[j]ϕ : ∀{j k} (ϕ : Setₒ) → j ≤ k → ↓ k ϕ ≡ₒ[ j ] ϕ
j≤k⇒↓kϕ≡[j]ϕ {j} {k} ϕ j≤k i =
  (λ {(i<j , (i<k , ϕi)) → i<j , ϕi}) , (λ {(i<j , ϕi) → i<j , (≤-trans{suc i}{j}{k} i<j j≤k , ϕi)})

lemma17 : ∀ {ϕ} k → ↓ (suc k) ϕ ≡ₒ[ k ] ϕ
lemma17 {ϕ} k = j≤k⇒↓kϕ≡[j]ϕ {k}{suc k} ϕ (n≤1+n k)

equiv-approx : ∀{ϕ ψ : Setₒ} → (∀ k → ϕ ≡ₒ[ k ] ψ) → ϕ ≡ₒ ψ
equiv-approx ∀k,ϕ=[k]ψ i =
  let ↓ϕ⇔↓ψ = ∀k,ϕ=[k]ψ (suc i) i in
  (λ ϕi → let ↓siψi = proj₁ ↓ϕ⇔↓ψ ((s≤s{i}{i} (≤-refl{i})) , ϕi) in proj₂ ↓siψi)
  , (λ ψi → let ↓siϕi = proj₂ ↓ϕ⇔↓ψ ((s≤s{i}{i} (≤-refl{i})) , ψi) in proj₂ ↓siϕi)

