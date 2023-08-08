\begin{comment}
\begin{code}
{-# OPTIONS --rewriting --prop #-}

module July2023.STLCDeterministic2 where

open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Nat.Induction
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List using (map)
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
--open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Induction using (RecStruct)
open import Induction.WellFounded as WF
open import Data.Product.Relation.Binary.Lex.Strict
  using (×-Lex; ×-wellFounded; ×-preorder)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; cong₂; subst; trans)
--open Eq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Sig
open import Var
open import StepIndexedLogic2
open import July2023.STLC2

\end{code}
\end{comment}

\begin{code}
deterministic : ∀{M N N′} → M —→ N → M —→ N′ → N ≡ N′
deterministic (ξ (□· x₂) M—→N) (ξ (□· x₃) M—→N′) = cong₂ _·_ (deterministic M—→N M—→N′) refl
deterministic (ξ (□· x₂) M—→N) (ξ (x₃ ·□) M—→N′) = ⊥-elim (value-irreducible x₃ M—→N)
deterministic (ξ (□· x₂) M—→N) (β-ƛ x) = ⊥-elim (value-irreducible V-ƛ M—→N)
deterministic (ξ (□· x₂) M—→N) (β-μ x x₁) = ⊥-elim (value-irreducible (V-μ x) M—→N)
deterministic (ξ (x₂ ·□) M—→N) (ξ (□· x₃) M—→N′) = ⊥-elim (value-irreducible x₂ M—→N′)
deterministic (ξ (x₂ ·□) M—→N) (ξ (x₃ ·□) M—→N′)
    with deterministic M—→N M—→N′
... | refl = refl    
deterministic (ξ (x₂ ·□) M—→N) (β-ƛ x) = ⊥-elim (value-irreducible x M—→N)
deterministic (ξ (x₂ ·□) M—→N) (β-μ x x₁) = ⊥-elim (value-irreducible x₁ M—→N)
deterministic (ξ suc□ M—→N) (ξξ (□· x₄) () x₃ M—→N′)
deterministic (ξ suc□ M—→N) (ξξ (x₄ ·□) () x₃ M—→N′)
deterministic (ξ suc□ M—→N) (ξ suc□ M—→N′)
    with deterministic M—→N M—→N′
... | refl = refl    
deterministic (ξ suc□ M—→N) (ξξ (case□ x₄ x₅) () x₃ M—→N′)
deterministic (ξ (case□ x₂ x₃) M—→N) (ξ (case□ x₄ x₅) M—→N′)
    with deterministic M—→N M—→N′
... | refl = refl    
deterministic (ξ (case□ x₂ x₃) M—→N) β-zero = ⊥-elim (value-irreducible V-zero M—→N)
deterministic (ξ (case□ x₂ x₃) M—→N) (β-suc x) = ⊥-elim (value-irreducible (V-suc x) M—→N)
deterministic (β-ƛ x) (ξ (□· x₃) M—→N′) = ⊥-elim (value-irreducible V-ƛ M—→N′)
deterministic (β-ƛ x) (ξ (x₃ ·□) M—→N′) = ⊥-elim (value-irreducible x M—→N′)
deterministic (β-ƛ x) (β-ƛ x₁) = refl
deterministic β-zero (ξ (case□ x₂ x₃) M—→N′) = ⊥-elim (value-irreducible V-zero M—→N′)
deterministic β-zero β-zero = refl
deterministic (β-suc x) (ξ (case□ x₃ x₄) M—→N′) = ⊥-elim (value-irreducible (V-suc x) M—→N′)
deterministic (β-suc x) (β-suc x₁) = refl
deterministic (β-μ x x₁) (ξ (□· x₄) M—→N′) = ⊥-elim (value-irreducible (V-μ x) M—→N′)
deterministic (β-μ x x₁) (ξ (x₄ ·□) M—→N′) = ⊥-elim (value-irreducible x₁ M—→N′)
deterministic (β-μ x x₁) (β-μ x₂ x₃) = refl
\end{code}


\begin{code}
frame-inv : ∀{L N : Term}{F} → reducible L → F ⟦ L ⟧ —→ N → ∃[ L′ ] ((L —→ L′) × (N ≡ F ⟦ L′ ⟧))
frame-inv {F = □· M} (L′ , L→L′) (ξ (□· x₃) L→N) = _ , (L→N , refl)
frame-inv {F = □· M} (L′ , L→L′) (ξ (v ·□) FL→N) = ⊥-elim (value-irreducible v L→L′)
frame-inv {F = □· M} (L′ , L→L′) (β-ƛ x₁) = ⊥-elim (value-irreducible V-ƛ L→L′)
frame-inv {F = □· M} (L′ , L→L′) (β-μ x₁ x₂) = ⊥-elim (value-irreducible (V-μ x₁) L→L′)
frame-inv {F = v ·□} (L′ , L→L′) (ξ (□· x₂) FL→N) = ⊥-elim (value-irreducible v FL→N)
frame-inv {F = v ·□} (L′ , L→L′) (ξ (w ·□) FL→N)
    with deterministic FL→N L→L′
... | refl = _ , (L→L′ , refl)
frame-inv {F = v ·□} (L′ , L→L′) (β-ƛ x) = ⊥-elim (value-irreducible x L→L′)
frame-inv {F = v ·□} (L′ , L→L′) (β-μ x w) = ⊥-elim (value-irreducible w L→L′)
frame-inv {F = suc□} (L′ , L→L′) (ξ suc□ FL→N)
    with deterministic FL→N L→L′
... | refl = _ , (L→L′ , refl)
frame-inv {F = case□ x x₁} (L′ , L→L′) (ξ (case□ x₄ x₅) FL→N)
    with deterministic FL→N L→L′
... | refl = _ , (L→L′ , refl)
frame-inv {F = case□ x x₁} (L′ , L→L′) β-zero = ⊥-elim (value-irreducible V-zero L→L′)
frame-inv {F = case□ x x₁} (L′ , L→L′) (β-suc x₂) = ⊥-elim (value-irreducible (V-suc x₂) L→L′)
\end{code}
