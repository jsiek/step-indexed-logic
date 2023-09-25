{-# OPTIONS --without-K --prop #-}

open import Data.Nat
   using (ℕ; zero; suc; _+_; _∸_)
open import Data.List using (List; []; _∷_)
open import Data.Product
   using (_×_; _,_) -- ; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
{-
open import Data.Unit using (tt; ⊤)
-}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; cong-app; subst)

module Fixpoint where

open import PropP
open import EquivalenceRelationProp
open import RawSetO
open import Approx
open import Iteration
open import Variables
open import Env
open import SetO

⟅_⟆ : ∀{A : Set}{Γ : Context}{Δ : Times Γ} → (A → Setᵒ (A ∷ Γ) (Later ∷ Δ)) → RecEnv Γ → (Predₒ A → Predₒ A)
⟅ Sᵃ ⟆ δ P = λ a → # (Sᵃ a) (P , δ)

mu : ∀ {Γ}{Δ : Times Γ}{A} → (A → Setᵒ (A ∷ Γ) (Later ∷ Δ)) → (RecEnv Γ → A → Setₒ)
mu Sᵃ δ a k = ((⟅ Sᵃ ⟆ δ) ^ (1 + k)) ⊤ᵖ a k

lemma15b-env-fun : ∀{Γ}{Δ}{A}{δ : RecEnv Γ}{P : Predₒ A}
  (k j : ℕ) (Sᵃ : A → Setᵒ (A ∷ Γ) (Later ∷ Δ)) (a : A)
  → j ≤ₚ k → ((⟅ Sᵃ ⟆ δ) ^ j) P a ≡ₒ[ j ] ((⟅ Sᵃ ⟆ δ) ^ k) P a
lemma15b-env-fun {Γ}{Δ}{A}{δ}{P} k j Sᵃ a j≤k =
  lemma15b k j (⟅ Sᵃ ⟆ δ) a j≤k
  (λ a P k → wellformed (Sᵃ a) zeroᵒ (P , δ) k k (≤-reflₚ{k}))
  (λ P=Q a → congr (Sᵃ a) (P=Q ,ₚ ≡ᵈ-refl{_}{δ}))

lemma18a : ∀{Γ}{Δ : Times Γ}{A} (k : ℕ) (Sᵃ : A → Setᵒ (A ∷ Γ) (Later ∷ Δ)) (a : A) (δ : RecEnv Γ)
  → mu Sᵃ δ a ≡ₒ[ k ] ((⟅ Sᵃ ⟆ δ) ^ k) (λ a k → ⊤ₚ) a
lemma18a {Γ}{Δ}{A} k Sᵃ a δ j = to k j ,ₚ fro k j
  where
  to : ∀ k j → ↓ k (mu Sᵃ δ a) j → ↓ k ((⟅ Sᵃ ⟆ δ ^ k) (λ a₁ k₁ → ⊤ₚ) a) j
  to k j (j<k ,ₚ mu-j) = j<k ,ₚ
     proj₂ₚ (proj₁ₚ (lemma15b-env-fun k (suc j) Sᵃ a j<k j) (≤-reflₚ{j} ,ₚ mu-j))
  fro : ∀ k j → ↓ k ((⟅ Sᵃ ⟆ δ ^ k) (λ a₁ k₁ → ⊤ₚ) a) j → ↓ k (mu Sᵃ δ a) j
  fro k j (j<k ,ₚ Sᵏj) =
     j<k ,ₚ (proj₂ₚ (proj₂ₚ (lemma15b-env-fun k (suc j) Sᵃ a j<k j) (≤-reflₚ{j} ,ₚ Sᵏj)))

lemma18b : ∀{Γ}{Δ : Times Γ}{A} (k : ℕ) (Sᵃ : A → Setᵒ (A ∷ Γ) (Later ∷ Δ)) (a : A) (δ : RecEnv Γ)
     → # (Sᵃ a) (mu Sᵃ δ , δ) ≡ₒ[ 1 + k ] ((⟅ Sᵃ ⟆ δ) ^ (1 + k)) (λ a k → ⊤ₚ) a
lemma18b {A}{Γ}{Δ} k Sᵃ a δ =
       ↓ (1 + k) (# (Sᵃ a) (mu Sᵃ δ , δ))
   ⩦⟨ wellformed (Sᵃ a) zeroᵒ (mu Sᵃ δ , δ) k k (≤-reflₚ{k}) ⟩
       ↓ (1 + k) (# (Sᵃ a) (↓ᵖ k (mu Sᵃ δ) , δ))
   ⩦⟨ cong-approxᵖ{k = 1 + k} (λ a → congr (Sᵃ a) ((λ a → lemma18a k Sᵃ a δ) ,ₚ ≡ᵈ-refl)) a ⟩
       ↓ (1 + k) (# (Sᵃ a) (↓ᵖ k (((⟅ Sᵃ ⟆ δ) ^ k) (λ a k → ⊤ₚ)) , δ))
   ⩦⟨ ≡ₒ-sym (wellformed (Sᵃ a) zeroᵒ ((((⟅ Sᵃ ⟆ δ) ^ k) (λ a k → ⊤ₚ)) , δ) k k (≤-reflₚ{k})) ⟩
       ↓ (1 + k) (# (Sᵃ a) (((⟅ Sᵃ ⟆ δ) ^ k) (λ a k → ⊤ₚ) , δ))
   ⩦⟨ ≡ₒ-refl refl ⟩
       ↓ (1 + k) (((⟅ Sᵃ ⟆ δ) ^ (suc k)) (λ a k → ⊤ₚ) a)
   ∎

lemma19a : ∀{Γ}{Δ : Times Γ}{A} (Sᵃ : A → Setᵒ (A ∷ Γ) (Later ∷ Δ)) (a : A) (δ : RecEnv Γ) (k : ℕ)
  → mu Sᵃ δ a ≡ₒ[ k ] # (Sᵃ a) ((λ a k → mu Sᵃ δ a k) , δ)
lemma19a Sᵃ a δ k =
    let f = (⟅ Sᵃ ⟆ δ) in
      ↓ k (mu Sᵃ δ a)
  ⩦⟨ lemma18a k Sᵃ a δ  ⟩
      ↓ k ((f ^ k) (λ a k → ⊤ₚ) a)
  ⩦⟨ lemma15b-env-fun (suc k) k Sᵃ a (n≤1+nₚ k) ⟩
      ↓ k ((f ^ (suc k)) (λ a k → ⊤ₚ) a)
  ⩦⟨ ≡ₒ-sym (lemma17{((f ^ (suc k)) (λ a k → ⊤ₚ)) a} k) ⟩
      ↓ k (↓ (suc k) ((f ^ (suc k)) (λ a k → ⊤ₚ) a))
   ⩦⟨ cong-approxᵖ{k = k} (λ a → ≡ₒ-sym (lemma18b k Sᵃ a δ)) a ⟩
      ↓ k (↓ (suc k) (# (Sᵃ a) (mu Sᵃ δ , δ)))
   ⩦⟨ lemma17{(# (Sᵃ a) (mu Sᵃ δ , δ))} k ⟩
      ↓ k (# (Sᵃ a) (mu Sᵃ δ , δ))
   ∎

