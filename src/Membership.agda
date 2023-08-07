{-# OPTIONS --without-K  --prop #-}

module Membership where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product
   using (_×_; _,_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym)

open import PropLib renaming (_×_ to _×ₚ_; _,_ to _,ₚ_) hiding (⊥-elim)
open import Variables
open import Env
open import RawSetO
open import Approx
open import SetO
open import EquivalenceRelationProp using (subst; ≐-sym; ≐-refl)

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

lookup-diff : ∀{Γ}{Δ : Times Γ}{A}{B}{δ : RecEnv Γ}{j} (x : Γ ∋ A) (y : Γ ∋ B) → timeof x Δ ≢ timeof y Δ
   → lookup{Γ}{A} x (↓ᵈ j y δ) ≡ lookup{Γ}{A} x δ
lookup-diff {C ∷ Γ} {t ∷ Δ} zeroᵒ zeroᵒ neq = ⊥-elim (neq refl)
lookup-diff {C ∷ Γ} {t ∷ Δ} zeroᵒ (sucᵒ y) neq = refl
lookup-diff {C ∷ Γ} {t ∷ Δ} (sucᵒ x) zeroᵒ neq = refl
lookup-diff {C ∷ Γ} {t ∷ Δ} (sucᵒ x) (sucᵒ y) neq = lookup-diff x y neq

timeof-var-now : ∀{Γ}{A} → (x : Γ ∋ A) → timeof x (var-now Γ x) ≡ Now
timeof-var-now {B ∷ Γ} zeroᵒ = refl
timeof-var-now {B ∷ Γ} (sucᵒ x) = timeof-var-now x

strong-lookup : ∀{Γ}{A}{a} → (x : Γ ∋ A) → strong-fun (var-now Γ x) (λ δ → lookup x δ a)
strong-lookup {a = a} zeroᵒ zeroᵒ = NE where
  NE : strongly-nonexpansive zeroᵒ (λ {(P , δ) → P a})
  NE (P , δ) j k k≤j  = ≡ₒ-sym (j≤k⇒↓kϕ≡[j]ϕ{j = k} (P a) k≤j)
strong-lookup {a = a} zeroᵒ (sucᵒ y) rewrite timeof-later y = C
  where
  C : strongly-contractive (sucᵒ y) (λ {(P , δ) → P a})
  C (P , δ) j k k≤j = ≡ₒ-refl refl
strong-lookup {a = a} (sucᵒ x) zeroᵒ = C
  where
  C : strongly-contractive zeroᵒ (λ (P , δ) → lookup x δ a)
  C (P , δ) j k k≤j = ≡ₒ-refl refl
strong-lookup {B ∷ Γ}{A}{a} (sucᵒ x) (sucᵒ y)
    with timeof y (var-now Γ x) in eq-y
... | Now = SNE where
    SNE : strongly-nonexpansive (sucᵒ y) (λ {(P , δ) → lookup x δ a})
    SNE (P , δ) j k k≤j = ↓-lookup{k = k} x y k≤j 
... | Later = SC where
    timeof-diff : ∀{Γ}{Δ : Times Γ}{A}{B} (x : Γ ∋ A) (y : Γ ∋ B) → timeof x Δ ≡ Now → timeof y Δ ≡ Later
       → timeof x Δ ≢ timeof y Δ
    timeof-diff x y eq1 eq2 rewrite eq1 | eq2 = λ ()
    SC : strongly-contractive (sucᵒ y) (λ {(P , δ) → lookup x δ a})
    SC (P , δ) j k k≤j =
      let eq = (lookup-diff{Γ}{δ = δ}{j} x y (timeof-diff x y (timeof-var-now x) eq-y)) in
      subst (λ X → (lookup x δ a) ≡ₒ[ suc k ] (X a)) (≐-sym (≐-refl eq)) (≡ₒ-refl refl)
      
congruent-lookup : ∀{Γ}{A} (x : Γ ∋ A) (a : A) → congruent (λ δ → lookup x δ a)
congruent-lookup x a d=d′ = aux x a d=d′
  where
  aux : ∀{Γ}{A}{δ δ′ : RecEnv Γ} (x : Γ ∋ A) (a : A) → δ ≡ᵈ δ′ → lookup x δ a ≡ₒ lookup x δ′ a
  aux {B ∷ Γ} {.B}{P , δ}{P′ , δ′} zeroᵒ a (P=P′ ,ₚ d=d′) = P=P′ a
  aux {B ∷ Γ} {A}{P , δ}{P′ , δ′} (sucᵒ x) a (P=P′ ,ₚ d=d′) = aux x a d=d′
