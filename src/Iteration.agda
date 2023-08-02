{-# OPTIONS --without-K #-}

open import Data.Nat using (ℕ; zero; suc; _≤_; _∸_; z≤n; s≤s)
open import Function using (id; _∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; cong-app; subst)
open import RawSetO
open import Approx
open import EquivalenceRelation

module Iteration where

infixr 8 _^_
_^_ : ∀ {ℓ} {A : Set ℓ} → (A → A) → ℕ → (A → A)
f ^ zero     =  id
f ^ (suc n)  =  f ∘ (f ^ n)

iter-subtract : ∀{ℓ}{A : Set ℓ}{a : A} (F : A → A) (j k : ℕ) → j ≤ k
  → (F ^ j) ((F ^ (k ∸ j)) a) ≡ (F ^ k) a
iter-subtract {A = A} {a} F .zero k z≤n = refl
iter-subtract {A = A} {a} F (suc j) (suc k) (s≤s j≤k)
  rewrite iter-subtract{A = A}{a} F j k j≤k = refl

contractiveᵖ : ∀ {A} → (f : Predₒ A → Predₒ A) → Set₁
contractiveᵖ f = ∀ a P k → f P a ≡ₒ[ suc k ] f (↓ᵖ k P) a

lemma15a : ∀ {A}{P Q : Predₒ A} j → (f : Predₒ A → Predₒ A) (a : A) → contractiveᵖ f → congruentᵖ f
  → (f ^ j) P a ≡ₒ[ j ] (f ^ j) Q a
lemma15a {A} {P} {Q} zero f a contr-f congr-f = ≡ₒ[0]
lemma15a {A} {P} {Q} (suc j) f a contr-f congr-f =
    f ((f ^ j) P) a
  ⩦⟨ contr-f a ((f ^ j) P) j ⟩ 
      f (↓ᵖ j ((f ^ j) P)) a
  ⩦⟨ cong-approx (congr-f λ a → lemma15a j f a contr-f congr-f) a ⟩
      f (↓ᵖ j ((f ^ j) Q)) a
  ⩦⟨ ≡ₒ-sym (contr-f a ((f ^ j) Q) j) ⟩ 
    f ((f ^ j) Q) a
  ∎

lemma15b : ∀{A}{P : Predₒ A} (k j : ℕ) (f : Predₒ A → Predₒ A) (a : A) → j ≤ k → contractiveᵖ f → congruentᵖ f
   → (f ^ j) P a ≡ₒ[ j ] (f ^ k) P a
lemma15b {A}{P} k j f a j≤k wf-f cong-f =
    (f ^ j) P a
  ⩦⟨ lemma15a j f a wf-f cong-f ⟩
    (f ^ j) ((f ^ (k ∸ j)) P) a
  ⩦⟨ cong-approx{A}{j}{(f ^ j) ((f ^ (k ∸ j)) P)}{(f ^ k) P} (λ a → ≡ᵖ-refl (iter-subtract f j k j≤k)) a ⟩
    (f ^ k) P a
  ∎

