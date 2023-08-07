{-# OPTIONS --without-K --prop #-}
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_,_;_×_) -- ; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Nat using (ℕ; zero; suc; _+_)
--open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_; _∸_; z≤n; s≤s; _≤′_; ≤′-step)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans)
--open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; cong-app; subst)

open import PropLib renaming (_×_ to _×ₚ_; _,_ to _,ₚ_)
open import RawSetO
open import SetO
open import Variables
open import Env
open import Approx
open import Iteration
open import Fixpoint
open import EquivalenceRelationProp

module RecPred where

down-mu : ∀{Γ}{Δ}{A}(Sᵃ : A → Setᵒ (A ∷ Γ) (Later ∷ Δ)) (a : A) (δ : RecEnv Γ)
   → downClosedᵈ δ → downClosed (mu Sᵃ δ a)
down-mu Sᵃ a δ dc-δ k μSᵃa-k j j≤k =
   let F = (⟅ Sᵃ ⟆ δ) in {- F = λ P a → # (Sᵃ a) (P , δ) -}
   let dc-F : downClosed-fun F
       dc-F = λ P a′ dc-P → down (Sᵃ a′) (P , δ) (dc-P ,ₚ dc-δ) in
   let dc-iter-F : downClosed ((F ^ (1 + k)) ⊤ᵖ a)
       dc-iter-F = down-iter (suc k) F dc-F a in
   let ↓-iter-sk : (↓ (1 + j) ((⟅ Sᵃ ⟆ δ ^ (1 + k)) ⊤ᵖ a)) j
       ↓-iter-sk = (≤-refl{j}) ,ₚ (dc-iter-F k μSᵃa-k j j≤k) in
   let eq : (((⟅ Sᵃ ⟆ δ ^ (1 + j)) ⊤ᵖ) a)  ≡ₒ[ 1 + j ]  (((⟅ Sᵃ ⟆ δ ^ (1 + k)) ⊤ᵖ) a)
       eq = lemma15b-env-fun {δ = δ} (1 + k) (1 + j) Sᵃ a (s≤s{j}{k} j≤k) in
   let ↓-iter-sj : (↓ (1 + j) (((⟅ Sᵃ ⟆ δ ^ (1 + j)) ⊤ᵖ) a)) j
       ↓-iter-sj = proj₂ (eq j) ↓-iter-sk  in
   proj₂ ↓-iter-sj 

mu-nonexpansive : ∀{Γ}{Δ : Times Γ}{A}{B} (Sᵃ : A → Setᵒ (A ∷ Γ) (Later ∷ Δ)) (a : A) (x : Γ ∋ B)
   → timeof x Δ ≡ Now → (δ : RecEnv Γ) (k j : ℕ) → (k ≤ j)
   → mu Sᵃ δ a ≡ₒ[ k ] mu Sᵃ (↓ᵈ j x δ) a
mu-nonexpansive {Γ} {Δ} {A} Sᵃ a x time-x δ zero j k≤j = ≡ₒ[0]
mu-nonexpansive {Γ} {Δ} {A}{B} Sᵃ a x time-x δ (suc k′) j k≤j =
      ↓ (suc k′) (mu Sᵃ δ a)
  ⩦⟨ lemma19a Sᵃ a δ (suc k′) ⟩
      ↓ (suc k′) (# (Sᵃ a) (mu Sᵃ δ , δ))
  ⩦⟨ nonexpansive-Sa-sx ⟩
      ↓ (suc k′) (# (Sᵃ a) (mu Sᵃ δ , ↓ᵈ j x δ))
  ⩦⟨ contractive-Sa-z-δ ⟩
      ↓ (suc k′) (# (Sᵃ a) (↓ᵖ k′ (mu Sᵃ δ) , ↓ᵈ j x δ))
  ⩦⟨ cong-approx (suc k′) (congr (Sᵃ a) (IH ,ₚ ≡ᵈ-refl)) ⟩
      ↓ (suc k′) (# (Sᵃ a) (↓ᵖ k′ (mu Sᵃ (↓ᵈ j x δ)) , ↓ᵈ j x δ))
  ⩦⟨ ≡ₒ-sym contractive-Sa-z-↓δ ⟩
      ↓ (suc k′) (# (Sᵃ a) (mu Sᵃ (↓ᵈ j x δ) , ↓ᵈ j x δ))
  ⩦⟨ ≡ₒ-sym (lemma19a Sᵃ a (↓ᵈ j x δ) (suc k′)) ⟩
      ↓ (suc k′) (mu Sᵃ (↓ᵈ j x δ) a)
  ∎
  where
  nonexpansive-Sa-sx = strong-now⇒nonexpansive{x = sucᵒ x}{Δ = Later ∷ Δ}
                    (strong (Sᵃ a) (sucᵒ x)) time-x (mu Sᵃ δ , δ) j (suc k′) k≤j
  contractive-Sa-z-δ = strong (Sᵃ a) zeroᵒ (mu Sᵃ δ , ↓ᵈ j x δ) k′ k′ (≤-refl{k′})
  IH : ∀ a → ↓ k′ (mu Sᵃ δ a) ≡ₒ ↓ k′ (mu Sᵃ (↓ᵈ j x δ) a)
  IH a = mu-nonexpansive Sᵃ a x time-x δ k′ j (≤-trans{k′}{suc k′}{j} (n≤1+n k′) k≤j)
  contractive-Sa-z-↓δ = strong (Sᵃ a) zeroᵒ (mu Sᵃ (↓ᵈ j x δ) , ↓ᵈ j x δ) k′ k′ (≤-refl{k′})

mu-contractive : ∀{A}{Γ}{Δ}{B} → (Sᵃ : A → Setᵒ (A ∷ Γ) (Later ∷ Δ)) (a : A) (x : Γ ∋ B)
   → timeof x Δ ≡ Later → (δ : RecEnv Γ) (k j : ℕ) → (k ≤ j)
   → mu Sᵃ δ a ≡ₒ[ 1 + k ] mu Sᵃ (↓ᵈ j x δ) a
mu-contractive {A} {Γ} {Δ} {B} Sᵃ a x time-x δ k j k≤j =
      ↓ (suc k) (mu Sᵃ δ a)
  ⩦⟨ lemma19a Sᵃ a δ (suc k) ⟩
      ↓ (suc k) (# (Sᵃ a) (mu Sᵃ δ , δ))
  ⩦⟨ contractive-Sᵃ-sx ⟩
      ↓ (suc k) (# (Sᵃ a) (mu Sᵃ δ , ↓ᵈ j x δ))
  ⩦⟨ contractive-Sa-z-δ ⟩      
      ↓ (suc k) (# (Sᵃ a) (↓ᵖ k (mu Sᵃ δ) , ↓ᵈ j x δ))
  ⩦⟨ cong-approx (suc k) (congr (Sᵃ a) (IH k k≤j ,ₚ ≡ᵈ-refl)) ⟩      
      ↓ (suc k) (# (Sᵃ a) (↓ᵖ k (mu Sᵃ (↓ᵈ j x δ)) , ↓ᵈ j x δ))
  ⩦⟨ ≡ₒ-sym contractive-Sa-z-↓δ ⟩
      ↓ (suc k) (# (Sᵃ a) (mu Sᵃ (↓ᵈ j x δ) , (↓ᵈ j x δ)))
  ⩦⟨ ≡ₒ-sym (lemma19a Sᵃ a (↓ᵈ j x δ) (suc k)) ⟩  
      ↓ (suc k) (mu Sᵃ (↓ᵈ j x δ) a)
  ∎
  where
  contractive-Sᵃ-sx = strong-later⇒contractive {A = B}{sucᵒ x}{Δ = Later ∷ Δ}
                       (strong (Sᵃ a) (sucᵒ x)) time-x (mu Sᵃ δ , δ) j k k≤j 
  contractive-Sa-z-δ = strong (Sᵃ a) zeroᵒ (mu Sᵃ δ , ↓ᵈ j x δ) k k (≤-refl{k})
  IH : ∀ k → k ≤ j → ∀ a → ↓ k (mu Sᵃ δ a) ≡ₒ ↓ k (mu Sᵃ (↓ᵈ j x δ) a)
  IH zero  k≤j a = ≡ₒ[0]
  IH (suc k) k≤j a = mu-contractive Sᵃ a x time-x δ k j (≤-trans{k}{suc k}{j} (n≤1+n k) k≤j)
  contractive-Sa-z-↓δ = strong (Sᵃ a) zeroᵒ (mu Sᵃ (↓ᵈ j x δ) , ↓ᵈ j x δ) k k (≤-refl{k})

strong-mu : ∀{Γ}{Δ : Times Γ}{A} (Sᵃ : A → Setᵒ (A ∷ Γ) (Later ∷ Δ)) (a : A)
   → strong-fun Δ (λ δ → mu Sᵃ δ a)
strong-mu {Γ} {Δ} {A} Sᵃ a x
    with timeof x Δ in time-x
... | Now = λ δ j k k≤j → mu-nonexpansive Sᵃ a x time-x δ k j k≤j
... | Later = λ δ j k k≤j → mu-contractive Sᵃ a x time-x δ k j k≤j