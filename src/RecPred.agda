{-# OPTIONS --without-K --prop #-}
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_,_;_×_) -- ; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Nat using (suc; _+_)

open import PropLib renaming (_×_ to _×ₚ_; _,_ to _,ₚ_)
open import RawSetO
open import SetO
open import Variables
open import Env
open import Approx
open import Iteration
open import Fixpoint

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
