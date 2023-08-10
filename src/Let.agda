{-# OPTIONS --without-K --prop #-}
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_,_;_×_) -- ; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Nat using (ℕ; zero; suc; _+_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans)

open import PropP
open import RawSetO
open import SetO
open import Variables
open import Env
open import Approx
open import EquivalenceRelationProp

module Let where

strong-let : ∀{Γ}{Δ : Times Γ}{A}{t} (T : Setᵒ (A ∷ Γ) (t ∷ Δ)) (Sᵃ : A → Setᵒ Γ Δ)
   → strong-fun Δ (λ δ → # T ((λ a → # (Sᵃ a) δ) , δ))
strong-let {Γ}{Δ}{A}{Now} T Sᵃ x
    with timeof x Δ in time-x
... | Now = λ δ j k k≤j →
    let strongTsx = strong-now⇒nonexpansive{x = sucᵒ x}{Δ = Now ∷ Δ} ((strong T) (sucᵒ x)) time-x
                 ((λ a → ↓ j (# (Sᵃ a) δ)) , δ) j k k≤j in
    let nonexpansiveSx : ∀ a → ↓ j (# (Sᵃ a) δ) ≡ₒ ↓ j (# (Sᵃ a) (↓ᵈ j x δ))
        nonexpansiveSx = (λ a → strong-now⇒nonexpansive (strong (Sᵃ a) x) time-x δ j j (≤-reflₚ{j})) in
      ↓ k (# T ((λ a → # (Sᵃ a) δ) , δ))
    ⩦⟨ ((strong T) zeroᵒ) ((λ a → # (Sᵃ a) δ) , δ) j k k≤j ⟩
      ↓ k (# T ((λ a → ↓ j (# (Sᵃ a) δ)) , δ))
    ⩦⟨ strongTsx ⟩
      ↓ k (# T ((λ a → ↓ j (# (Sᵃ a) δ)) , ↓ᵈ j x δ))
    ⩦⟨ cong-approx k (congr T (nonexpansiveSx ,ₚ ≡ᵈ-refl)) ⟩
      ↓ k (# T ((λ a → ↓ j (# (Sᵃ a) (↓ᵈ j x δ))) , ↓ᵈ j x δ))
    ⩦⟨ ≡ₒ-sym (((strong T) zeroᵒ) ((λ a → # (Sᵃ a) (↓ᵈ j x δ)) , (↓ᵈ j x δ)) j k k≤j) ⟩
      ↓ k (# T ((λ a → # (Sᵃ a) (↓ᵈ j x δ)) , ↓ᵈ j x δ))
    ∎
... | Later = λ δ j k k≤j →
    let strongTz = ((strong T) zeroᵒ) ((λ a → # (Sᵃ a) δ) , δ) (suc j) (suc k) k≤j in
    let EQ : ((λ a → ↓ (suc j) (# (Sᵃ a) δ)) , δ) ≡ᵈ ((λ a → ↓ (suc j)  (# (Sᵃ a) (↓ᵈ j x δ))) , δ)
        EQ = (λ a → strong-later⇒contractive (strong (Sᵃ a) x) time-x δ j j (≤-reflₚ{j})) ,ₚ ≡ᵈ-refl in
    let strongTsx : ↓ (suc k) (# T ((λ a → # (Sᵃ a) (↓ᵈ j x δ)) , δ))
                    ≡ₒ ↓ (suc k) (# T ((λ a → # (Sᵃ a) (↓ᵈ j x δ)) , ↓ᵈ j x δ))
        strongTsx = strong-later⇒contractive{x = sucᵒ x}{Δ = Now ∷ Δ} ((strong T) (sucᵒ x)) time-x
                 ((λ a → # (Sᵃ a) (↓ᵈ j x δ)) , δ) j k k≤j in
      ↓ (suc k) (# T ((λ a → # (Sᵃ a) δ) , δ))
    ⩦⟨ strongTz ⟩
      ↓ (suc k) (# T ((λ a → ↓ (suc j) (# (Sᵃ a) δ)) , δ))
    ⩦⟨ cong-approx (suc k) (congr T EQ) ⟩
      ↓ (suc k) (# T ((λ a → ↓ (suc j) (# (Sᵃ a) (↓ᵈ j x δ))) , δ))
    ⩦⟨ ≡ₒ-sym (((strong T) zeroᵒ) ((λ a → # (Sᵃ a) _) , _) (suc j) (suc k) k≤j) ⟩
      ↓ (suc k) (# T ((λ a → (# (Sᵃ a) (↓ᵈ j x δ))) , δ))
    ⩦⟨ strongTsx ⟩
      ↓ (suc k) (# T ((λ a → # (Sᵃ a) (↓ᵈ j x δ)) , ↓ᵈ j x δ))
    ∎
strong-let {Γ}{Δ}{A}{Later} T Sᵃ x
    with timeof x Δ in time-x
... | Now = λ δ j k k≤j →
    let strongTz = ((strong T) zeroᵒ) ((λ a → # (Sᵃ a) δ) , δ) j k k≤j in
    let strongTz2 = ((strong T) zeroᵒ) ((λ a → # (Sᵃ a) (↓ᵈ j x δ)) , (↓ᵈ j x δ))
                   j k k≤j in
    let strongTsx = strong-now⇒nonexpansive{x = sucᵒ x}{Δ = Now ∷ Δ} ((strong T) (sucᵒ x)) time-x
                 ((λ a → ↓ j (# (Sᵃ a) δ)) , δ) j k k≤j in
    let EQ : ((λ a → ↓ j (# (Sᵃ a) δ)) , ↓ᵈ j x δ)
          ≡ᵈ ((λ a → ↓ j  (# (Sᵃ a) (↓ᵈ j x δ))) , ↓ᵈ j x δ)
        EQ = (λ a → strong-now⇒nonexpansive (strong (Sᵃ a) x) time-x δ j j (≤-reflₚ{j}))
             ,ₚ ≡ᵈ-refl in
      ↓ k (# T ((λ a → # (Sᵃ a) δ) , δ))
    ⩦⟨ ≡ₒ-sym (lemma17 k) ⟩
      ↓ k (↓ (suc k) (# T ((λ a → # (Sᵃ a) δ) , δ)))
    ⩦⟨ cong-approx k strongTz ⟩
      ↓ k (↓ (suc k) (# T ((λ a → ↓ j (# (Sᵃ a) δ)) , δ)))
    ⩦⟨ lemma17 k ⟩
      ↓ k (# T ((λ a → ↓ j (# (Sᵃ a) δ)) , δ))
    ⩦⟨ strongTsx ⟩
      ↓ k (# T ((λ a → ↓ j (# (Sᵃ a) δ)) , ↓ᵈ j x δ))
    ⩦⟨ cong-approx k (congr T EQ) ⟩
      ↓ k (# T ((λ a → ↓ j (# (Sᵃ a) (↓ᵈ j x δ))) , ↓ᵈ j x δ))
    ⩦⟨ ≡ₒ-sym (lemma17 k) ⟩
      ↓ k (↓ (suc k) (# T ((λ a → ↓ j (# (Sᵃ a) (↓ᵈ j x δ))) , ↓ᵈ j x δ)))
    ⩦⟨ cong-approx k (≡ₒ-sym strongTz2) ⟩
      ↓ k (↓ (suc k) (# T ((λ a → # (Sᵃ a) (↓ᵈ j x δ)) , ↓ᵈ j x δ)))
    ⩦⟨ lemma17 k ⟩
      ↓ k (# T ((λ a → # (Sᵃ a) (↓ᵈ j x δ)) , ↓ᵈ j x δ))
    ∎
... | Later = λ δ j k k≤j →
    let strongTz = ((strong T) zeroᵒ) ((λ a → # (Sᵃ a) δ) , δ) (suc j) k (≤-transₚ{k}{j}{suc j} k≤j (n≤1+nₚ j)) in
    let strongTz2 = ((strong T) zeroᵒ) (((λ a → # (Sᵃ a) (↓ᵈ j x δ))) , δ) (suc j) k (≤-transₚ{k}{j}{suc j} k≤j (n≤1+nₚ j)) in
    let EQ : ((λ a → ↓ (suc j) (# (Sᵃ a) δ)) , δ) ≡ᵈ ((λ a → ↓ (suc j)  (# (Sᵃ a) (↓ᵈ j x δ))) , δ)
        EQ = (λ a → strong-later⇒contractive (strong (Sᵃ a) x) time-x δ j j (≤-reflₚ{j})) ,ₚ ≡ᵈ-refl in
    let strongTsx = strong-later⇒contractive{x = sucᵒ x}{Δ = Now ∷ Δ} ((strong T) (sucᵒ x)) time-x
                 ((λ a → # (Sᵃ a) (↓ᵈ j x δ)) , δ) j k k≤j in
      ↓ (suc k) (# T ((λ a → # (Sᵃ a) δ) , δ))
    ⩦⟨ strongTz ⟩
      ↓ (suc k) (# T (↓ᵖ (suc j) (λ a → # (Sᵃ a) δ) , δ))
    ⩦⟨ cong-approx (suc k) (congr T EQ) ⟩
      ↓ (suc k) (# T (↓ᵖ (suc j) (λ a → # (Sᵃ a) (↓ᵈ j x δ)) , δ))
    ⩦⟨ ≡ₒ-sym strongTz2 ⟩
      ↓ (suc k) (# T ((λ a → # (Sᵃ a) (↓ᵈ j x δ)) , δ))
    ⩦⟨ strongTsx ⟩
      ↓ (suc k) (# T ((λ a → # (Sᵃ a) (↓ᵈ j x δ)) , ↓ᵈ j x δ))
    ∎

