{-# OPTIONS --without-K --prop #-}

open import Data.Nat using (ℕ; zero; suc; _∸_)
open import Function using (id; _∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; cong-app; subst)

open import PropLib
open import RawSetO
open import Approx
open import EquivalenceRelationProp

module Iteration where

infixr 8 _^_
_^_ : ∀ {ℓ} {A : Set ℓ} → (A → A) → ℕ → (A → A)
f ^ zero     =  id
f ^ (suc n)  =  f ∘ (f ^ n)

iter-subtract : ∀{ℓ}{A : Set ℓ}{a : A} (F : A → A) (j k : ℕ) → j ≤ k
  → (F ^ j) ((F ^ (k ∸ j)) a) ≡ (F ^ k) a
iter-subtract {A = A} {a} F zero k z≤n = refl
iter-subtract {A = A} {a} F (suc j) (suc k) j≤k
  rewrite iter-subtract{A = A}{a} F j k j≤k  = refl

contractiveᵖ : ∀ {A} → (f : Predₒ A → Predₒ A) → Prop₁
contractiveᵖ f = ∀ a P k → f P a ≡ₒ[ suc k ] f (↓ᵖ k P) a

lemma15a : ∀ {A}{P Q : Predₒ A} j → (f : Predₒ A → Predₒ A) (a : A) → contractiveᵖ f → congruentᵖ f
  → (f ^ j) P a ≡ₒ[ j ] (f ^ j) Q a
lemma15a {A} {P} {Q} zero f a contr-f congr-f = ≡ₒ[0]
lemma15a {A} {P} {Q} (suc j) f a contr-f congr-f =
    ↓ (suc j) (f ((f ^ j) P) a)
  ⩦⟨ contr-f a ((f ^ j) P) j ⟩
    ↓ (suc j) (f (↓ᵖ j ((f ^ j) P)) a)
  ⩦⟨ cong-approxᵖ{k = suc j} (congr-f λ a → lemma15a j f a contr-f congr-f) a ⟩ 
    ↓ (suc j) (f (↓ᵖ j ((f ^ j) Q)) a)
  ⩦⟨ ≡ₒ-sym (contr-f a ((f ^ j) Q) j) ⟩ 
    ↓ (suc j) (f ((f ^ j) Q) a)
  ∎

lemma15b : ∀{A}{P : Predₒ A} (k j : ℕ) (f : Predₒ A → Predₒ A) (a : A) → j ≤ k → contractiveᵖ f → congruentᵖ f
   → (f ^ j) P a ≡ₒ[ j ] (f ^ k) P a
lemma15b {A}{P} k j f a j≤k wf-f cong-f =
    ↓ j ((f ^ j) P a)
  ⩦⟨ lemma15a j f a wf-f cong-f ⟩
    ↓ j ((f ^ j) ((f ^ (k ∸ j)) P) a)
  ⩦⟨ cong-approxᵖ{A}{j}{(f ^ j) ((f ^ (k ∸ j)) P)}{(f ^ k) P} (λ a → ≡ᵖ-refl (iter-subtract f j k j≤k)) a ⟩
    ↓ j ((f ^ k) P a)
  ∎

down-iter : ∀(i : ℕ){A} (F : Predₒ A → Predₒ A) → downClosed-fun F → ∀ a → downClosed ((F ^ i) (λ _ _ → ⊤) a)
down-iter zero F dc-F = λ a n _ k _ → tt
down-iter (suc i) F dc-F = λ a → dc-F ((F ^ i) (λ _ _ → ⊤)) a (down-iter i F dc-F)

