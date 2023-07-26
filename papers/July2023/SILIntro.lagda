\begin{comment}
\begin{code}
{-# OPTIONS --without-K #-}
module July2023.SILIntro where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat
   using (ℕ; zero; suc; _≤_; _<_; _+_; _∸_; _*_; z≤n; s≤s; _≤′_; ≤′-step)
open import Data.Nat.Properties
   using (≤-refl; ≤-antisym; ≤-trans; ≤-step; ≤⇒≤′; ≤′⇒≤; n≤1+n; <⇒≤; s≤′s)
open import Data.Product
   using (_×_; _,_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt; ⊤)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; cong-app; subst)
open import Relation.Nullary using (¬_)
open import Function using (id; _∘_)
open import Level using (Lift)
open import EquivalenceRelation public
open import July2023.StepIndexedLogic

\end{code}
\end{comment}

\section{How to Use Step-Indexed Logic}




\begin{code}
_ : [] ⊢ᵒ ∀ᵒ[ x ] (2 * x ≡ x + (x + 0))ᵒ
_ = ⊢ᵒ-∀-intro λ x → pureᵒI refl
\end{code}

\begin{code}
instance
  Inhabited-ℕ : Inhabited ℕ
  Inhabited-ℕ = record { elt = zero }
\end{code}

\begin{code}
Evens : ℕ → Setˢ (ℕ ∷ []) (cons Later ∅)
Evens n = (n ≡ zero)ˢ ⊎ˢ ▷ˢ (∃ˢ[ m ] (n ≡ 2 + m)ˢ ×ˢ m ∈ zeroˢ)
\end{code}

\begin{code}
zero-even : [] ⊢ᵒ μᵒ Evens 0
zero-even = substᵒ (≡ᵒ-sym (fixpointᵒ Evens 0)) (inj₁ᵒ (pureᵒI refl))
\end{code}

\begin{code}
two-even : [] ⊢ᵒ μᵒ Evens 2
two-even = substᵒ (≡ᵒ-sym (fixpointᵒ Evens 2))
                 (inj₂ᵒ (monoᵒ (⊢ᵒ-∃-intro {ϕᵃ = λ m → (2 ≡ 2 + m)ᵒ ×ᵒ μᵒ Evens m}
                                0 (pureᵒI refl ,ᵒ zero-even))))
\end{code}


\begin{code}
_ : ∀ (δ : RecEnv Γ) → ♯ ⊤ˢ δ ≡ ⊤ ᵒ
_ = λ δ → refl
\end{code}
