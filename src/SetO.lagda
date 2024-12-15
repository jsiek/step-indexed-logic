\begin{comment}
\begin{code}
{-# OPTIONS --without-K --prop #-}

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product
   using (_×_; _,_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import PropP
open import EquivalenceRelationProp using (EquivalenceRelation; _⇔_; ⩦-refl; ⩦-sym; ⩦-trans)
open import RawSetO
open import Approx
open import Iteration
open import SILVariables
open import Env

module SetO where
\end{code}
\end{comment}

\subsection{Representation of SIL Propositions}

To save the user of SIL the trouble of proving that their formulas are
downward closed, wellformed, and congruent, we package the SIL logical
connectives into a record that combines their meaning (the embedding
in Agda) with proofs that their meaning satisfies this triad of properties.
So the type of a SIL proposition is given by the following definition
of \textsf{Setᵒ}.

\begin{code}
record Setᵒ (Γ : Context) (Δ : Times Γ) : Set₁ where
  field
    # : RecEnv Γ → Setₒ
    down : ∀ δ → downClosedᵈ δ → downClosed (# δ)
    wellformed : wellformed-prop Δ #
    congr : congruent #

open Setᵒ public
\end{code}

Let Γ range over contexts, Δ range over lists of times.
The meta-variables ϕ, ψ, and þ range over SIL propositions.

\begin{code}
private variable Γ : Context
private variable Δ : Times Γ
private variable ϕ ψ þ : Setᵒ Γ Δ
\end{code}

We define two SIL propositions to be equivalent when their meaning is
equivalent. We make this definition abstract because otherwise Agda
encounters difficulties regarding type inference in proofs that
involve equational reasoning. However, from the user perspective, we
do not want equivalence to be abstract, so we define conversion
functions to go back and forth between ≡ᵒ and the underlying
equivalence relations ≡ₒ and ⇔, respectively.

\begin{code}
abstract
  infix 2 _≡ᵒ_
  _≡ᵒ_ : Setᵒ Γ Δ → Setᵒ Γ Δ → Prop₁
  ϕ ≡ᵒ ψ = ∀ δ → # ϕ δ ≡ₒ # ψ δ

  ≡ₒ⇒≡ᵒ : (∀ δ → # ϕ δ ≡ₒ # ψ δ) → ϕ ≡ᵒ ψ
  ≡ₒ⇒≡ᵒ P≡ₒQ = P≡ₒQ

  ≡ᵒ⇒≡ₒ : ∀{δ} → ϕ ≡ᵒ ψ → # ϕ δ ≡ₒ # ψ δ
  ≡ᵒ⇒≡ₒ {ϕ}{ψ}{δ}{k} {δ′} eq = eq δ′

  ⇔⇒≡ᵒ : ∀{ϕ ψ : Setᵒ Γ Δ} → (∀ δ k → # ϕ δ k ⇔ # ψ δ k) → ϕ ≡ᵒ ψ
  ⇔⇒≡ᵒ P⇔Q k = P⇔Q k

  ≡ᵒ⇒⇔ : ∀{δ}{k} → ϕ ≡ᵒ ψ → # ϕ δ k ⇔ # ψ δ k
  ≡ᵒ⇒⇔ {ϕ}{ψ}{δ}{k} {δ′}{k′} eq = eq δ′ k′
\end{code}

The ≡ᵒ relation is an equivalence relation.

\begin{code}
  ≡ᵒ-refl : ϕ ≡ ψ → ϕ ≡ᵒ ψ
  ≡ᵒ-refl {ϕ} refl ttᵖ k = (λ z → z) ,ₚ (λ z → z)

  ≡ᵒ-sym : ϕ ≡ᵒ ψ → ψ ≡ᵒ ϕ
  ≡ᵒ-sym {ϕ}{ψ} PQ ttᵖ k
      with PQ ttᵖ k
  ... | (ϕ⇒ψ ,ₚ ψ⇒ϕ) = ψ⇒ϕ ,ₚ ϕ⇒ψ

  ≡ᵒ-trans : ϕ ≡ᵒ ψ → ψ ≡ᵒ þ → ϕ ≡ᵒ þ
  ≡ᵒ-trans PQ QR ttᵖ k
      with PQ ttᵖ k | QR ttᵖ k
  ... | (ϕ⇒ψ ,ₚ ψ⇒ϕ) | (ψ⇒þ ,ₚ þ⇒ψ) = (λ z → ψ⇒þ (ϕ⇒ψ z)) ,ₚ (λ z → ψ⇒ϕ (þ⇒ψ z))

instance
  SIL-Eqᵒ : ∀{Γ}{Δ} → EquivalenceRelation (Setᵒ Γ Δ)
  SIL-Eqᵒ = record { _⩦_ = _≡ᵒ_ ; ⩦-refl = ≡ᵒ-refl
                   ; ⩦-sym = ≡ᵒ-sym ; ⩦-trans = ≡ᵒ-trans }
\end{code}
