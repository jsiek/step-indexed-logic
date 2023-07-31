{-# OPTIONS --rewriting --without-K --allow-unsolved-metas #-}

open import Data.List using (List; []; _∷_)
open import Data.Nat
   using (ℕ; zero; suc; _≤_; _<_; _+_; _∸_; _*_; z≤n; s≤s; _≤′_; ≤′-step; ≤-pred)
open import Data.Nat.Properties
   using (≤-refl; ≤-antisym; ≤-trans; ≤-step; ≤⇒≤′; ≤′⇒≤; n≤1+n; <⇒≤; s≤′s; 0≢1+n; +-suc)
open import Data.Unit using (tt; ⊤)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
open import Data.Product
   using (_×_; _,_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; cong-app; subst)
open import Relation.Nullary using (¬_)
import Level

module Example2 where

open import StepIndexedLogic2
open import Example
open import RepRewrites

even-div2 : ∀ n k → n < k → # (μᵒ Evenᵒ n) ttᵖ k → ∃[ m ] (n ≡ 2 * m)
even-div2 zero (suc k) n<k even-n = zero , refl
even-div2 (suc n) (suc k) (s≤s n<k) even-n
    with proj₁ (even-def (suc n) ttᵖ (suc k)) even-n
... | inj₁ ()
... | inj₂ (m′ , (refl , ▷even[m′]))
    with proj₁ (▷sk{ϕ = μᵒ Evenᵒ m′}{k = k} tt) ▷even[m′] 
... | even-mu′-k
    with even-div2 m′ k (≤-trans (n≤1+n _) n<k) even-mu′-k
... | i , refl =    
    1 + i , cong suc (sym (+-suc i (i + zero)))
