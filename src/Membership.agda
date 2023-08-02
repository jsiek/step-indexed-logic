{-# OPTIONS --without-K  --prop #-}

module Membership where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product
   using (_×_; _,_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import PropLib renaming (_×_ to _×ₚ_; _,_ to _,ₚ_)
open import Variables
open import RawSetO
open import Approx
open import SetO

{---------------------- Membership in Recursive Predicate ---------------------}

lookup : ∀{Γ}{A} → Γ ∋ A → RecEnv Γ → Predₒ A
lookup {B ∷ Γ} {.B} zeroᵒ (P , δ) = P
lookup {B ∷ Γ} {A} (sucᵒ x) (P , δ) = lookup{Γ}{A} x δ

down-lookup : ∀{Γ}{A}{x}{a : A} → (δ : RecEnv Γ) → downClosedᵈ δ → downClosed (lookup x δ a)
down-lookup {x = zeroᵒ}{a} (P , δ) (dcP ,ₚ dcδ) = dcP a
down-lookup {x = sucᵒ x} (P , δ) (dcP ,ₚ dcδ) = down-lookup δ dcδ

↓-lookup : ∀{Γ}{A}{B}{a}{k}{j}{δ : RecEnv Γ}
   → (x : Γ ∋ A)
   → (y : Γ ∋ B)
   → k ≤ j
   → (lookup{Γ}{A} x δ a) ≡ₒ[ k ] (lookup{Γ}{A} x (↓ᵈ j y δ) a)
↓-lookup {a = a}{k}{j}{P , δ} zeroᵒ zeroᵒ k≤j = ≡ₒ-sym (j≤k⇒↓kϕ≡[j]ϕ{j = k} (P a) k≤j)
↓-lookup zeroᵒ (sucᵒ y) k≤j = ≡ₒ-refl refl
↓-lookup (sucᵒ x) zeroᵒ k≤j = ≡ₒ-refl refl
↓-lookup {k = k} (sucᵒ x) (sucᵒ y) k≤j = ↓-lookup{k = k} x y k≤j
