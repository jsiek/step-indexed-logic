\begin{comment}
\begin{code}
{-# OPTIONS --without-K #-}
module July2023.SILReference where

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
open import July2023.StepIndexedLogic

\end{code}
\end{comment}

\section{Step-Indexed Logic Reference}
\label{sec:SIL-reference}

\subsection{The Setᵒ Type and its Connectives}

\begin{code}
_ : Set₁
_ = Setᵒ

_ : Setᵒ → ℕ → Set
_ = #

_ : ∀ (ϕ : Setᵒ) → (∀ n → # ϕ n → ∀ k → k ≤ n → # ϕ k)
_ = down

_ : ∀ (ϕ : Setᵒ) → (# ϕ 0)
_ = tz
\end{code}

\subsubsection{True}

The ``true'' formula is true at every index.

\begin{code}
_ : Setᵒ
_ = ⊤ᵒ

_ : # ⊤ᵒ n ≡ ⊤
_ = refl
\end{code}

\subsubsection{False}

The ``false'' formula is true at zero and false everywhere else.

\begin{code}
_ : Setᵒ
_ = ⊥ᵒ

_ : # ⊥ᵒ zero ≡ ⊤
_ = refl

_ : # ⊥ᵒ (suc n) ≡ ⊥
_ = refl
\end{code}

\subsubsection{Pure}

A pure formula $p ᵒ$ is true at zero and equivalent to $p$ everywhere else.

\begin{code}
_ : Set → Setᵒ
_ = _ᵒ

_ : # (p ᵒ) zero ≡ ⊤
_ = refl

_ : # (p ᵒ) (suc n) ≡ p
_ = refl
\end{code}

\subsubsection{Conjunction}

\begin{code}
_ : Setᵒ → Setᵒ → Setᵒ
_ = _×ᵒ_

_ : # (ϕ ×ᵒ ψ) n ≡ (# ϕ n × # ψ n)
_ = refl
\end{code}

\subsubsection{Disjunction}

\begin{code}
_ : Setᵒ → Setᵒ → Setᵒ
_ = _⊎ᵒ_

_ : # (ϕ ⊎ᵒ ψ) n ≡ (# ϕ n ⊎ # ψ n)
_ = refl
\end{code}


\subsubsection{For All}

\begin{code}
_ : (A → Setᵒ) → Setᵒ
_ = ∀ᵒ

_ : ∀{ϕᵃ : A → Setᵒ} →  #(∀ᵒ ϕᵃ) n ≡ ∀ a → # (ϕᵃ a) n
_ = refl
\end{code}

\subsubsection{For All}

\begin{code}
_ : {{_ : Inhabited A}} → (A → Setᵒ) → Setᵒ
_ = ∃ᵒ

_ : ∀{{_ : Inhabited A}}{ϕᵃ : A → Setᵒ} → # (∃ᵒ[ a ] (ϕᵃ a)) n ≡ (∃[ a ] (# (ϕᵃ a) n))
_ = refl
\end{code}



\subsection{Entailment and Proof Rules}


