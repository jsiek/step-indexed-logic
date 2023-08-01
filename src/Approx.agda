{-# OPTIONS --without-K #-}

open import Data.Unit using (tt; ⊤)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; s≤s; _≤′_; ≤′-step)
open import Data.Nat.Properties using (<⇒≤; ≤⇒≤′; ≤′⇒≤; ≤-trans; n≤1+n; ≤-refl)
open import Data.Product
   using (_×_; _,_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
open import RawSetO
open import EquivalenceRelation
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans)

module Approx where

{-
↓ : ℕ → Setₒ → Setₒ
↓ k S zero = ⊤
↓ k S (suc j) = suc j < k × (S (suc j))
-}
↓ : ℕ → Setₒ → Setₒ
↓ k S j = j < k × (S j)

infix 2 _≡ₒ[_]_
_≡ₒ[_]_ : Setₒ → ℕ → Setₒ → Set
ϕ ≡ₒ[ k ] ψ =  ↓ k ϕ  ≡ₒ  ↓ k ψ

abstract
  ≡ₒ[]-refl : ∀ {ϕ}{ψ}{k} → ϕ ≡ ψ → ϕ ≡ₒ[ k ] ψ
  ≡ₒ[]-refl {ϕ}{ψ}{k} refl = ≡ₒ-refl{S = ↓ k ϕ} refl

  ≡ₒ[]-sym : ∀ {ϕ}{ψ}{k} → ϕ ≡ₒ[ k ] ψ → ψ ≡ₒ[ k ] ϕ
  ≡ₒ[]-sym {ϕ}{ψ}{k} ϕ=ψ = ≡ₒ-sym{S = ↓ k ϕ}{↓ k ψ} ϕ=ψ

  ≡ₒ[]-trans : ∀ {ϕ}{ψ}{þ}{k} → ϕ ≡ₒ[ k ] ψ → ψ ≡ₒ[ k ] þ → ϕ ≡ₒ[ k ] þ
  ≡ₒ[]-trans {ϕ}{ψ}{þ}{k} ϕ=ψ ψ=þ = ≡ₒ-trans{S = ↓ k ϕ}{↓ k ψ}{↓ k þ} ϕ=ψ ψ=þ
instance
  SIL-Eq[] : ∀{k} → EquivalenceRelation Setₒ
  SIL-Eq[] {k} = record { _⩦_ = λ ϕ ψ → ϕ ≡ₒ[ k ] ψ ; ⩦-refl = ≡ₒ[]-refl ; ⩦-sym = ≡ₒ[]-sym ; ⩦-trans = ≡ₒ[]-trans }

≡ₒ[0] : ∀{ϕ ψ : Setₒ} → ϕ ≡ₒ[ 0 ] ψ
≡ₒ[0] k = (λ {()}) , (λ {()})

↓ᵖ : ℕ → ∀{A} → Predₒ A → Predₒ A
↓ᵖ j P a = ↓ j (P a)

cong-↓ : ∀{A}{k : ℕ} → congruentᵖ{A}{A} (↓ᵖ k)
cong-↓ {A} {k} {P} {Q} eq a i =
  (λ {(i<k , Pa) → i<k , proj₁ (eq a i) Pa}) , λ {(i<k , Qa) → i<k , proj₂ (eq a i) Qa}
{-
cong-↓ {A} {k} {P} {Q} eq a zero = (λ _ → tt) , λ _ → tt
cong-↓ {A} {k} {P} {Q} eq a (suc i) =
   (λ {(si≤k , Pasi) → si≤k , (proj₁ (eq a (suc i)) Pasi)})
   ,
   λ {(si≤k , Qasi) → si≤k , (proj₂ (eq a (suc i)) Qasi)}
-}

j≤k⇒↓kϕ≡[j]ϕ : ∀{j k} (ϕ : Setₒ) → j ≤ k → ↓ k ϕ ≡ₒ[ j ] ϕ
j≤k⇒↓kϕ≡[j]ϕ {j} {k} ϕ j≤k i =
  (λ {(i<j , (i<k , ϕi)) → i<j , ϕi}) , (λ {(i<j , ϕi) → i<j , (≤-trans i<j j≤k , ϕi)})

{-
j≤k⇒↓kϕ≡[j]ϕ {j} {k} ϕ j≤k zero = (λ _ → tt) , (λ _ → tt)
j≤k⇒↓kϕ≡[j]ϕ {j} {k} ϕ j≤k (suc i) = (λ {(a , b , c) → a , c}) , λ {(a , b) → a , ≤-trans a j≤k , b}
-}

lemma17 : ∀ {ϕ} k → ↓ (suc k) ϕ ≡ₒ[ k ] ϕ
lemma17 {ϕ} k = j≤k⇒↓kϕ≡[j]ϕ {k}{suc k} ϕ (n≤1+n k)

equiv-approx : ∀{ϕ ψ : Setₒ} → (∀ k → ϕ ≡ₒ[ k ] ψ) → ϕ ≡ₒ ψ
equiv-approx ∀k,ϕ=[k]ψ i =
  let ↓ϕ⇔↓ψ = ∀k,ϕ=[k]ψ (suc i) i in
  (λ ϕi → let ↓siψi = proj₁ ↓ϕ⇔↓ψ ((s≤s ≤-refl) , ϕi) in proj₂ ↓siψi)
  , (λ ψi → let ↓siϕi = proj₂ ↓ϕ⇔↓ψ ((s≤s ≤-refl) , ψi) in proj₂ ↓siϕi)

