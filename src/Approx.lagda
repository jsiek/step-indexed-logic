\begin{comment}
\begin{code}
{-# OPTIONS --without-K --prop #-}

open import Data.Nat using (ℕ; zero; suc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import EquivalenceRelationProp
open import RawSetO
open import PropP

module Approx where
\end{code}
\end{comment}

\subsection{Approximation}

The proof of the \textsf{fixpoint}ᵒ theorem is inspired by the
fixpoint theorem of \citet{Appel:2001aa}. Their proof relies on a
semantic notion of approximation to test whether a functional uses its
input now (at the current step index) or later (at strictly lower step
indices). The approximation operator, here written \textsf{↓ k S},
cuts off \textsf{S} at index \textsf{k}. That is, \textsf{↓ k S}
is true at index \textsf{j} if \textsf{j} is strictly less than \textsf{k}
and if \textsf{S} is true at \textsf{j}. For \textsf{j}
equal or greater than \textsf{k}, \textsf{↓ k S} is false.

\begin{code}
↓ : ℕ → Setₒ → Setₒ
↓ k S j = j <ₚ k ×ₚ (S j)
\end{code}

We write \textsf{ϕ ≡ₒ[ k ] ψ} to say that ϕ and ψ are k-equivalent,
that is, equivalent for \textsf{k} steps.

\begin{code}
infix 2 _≡ₒ[_]_
_≡ₒ[_]_ : Setₒ → ℕ → Setₒ → Prop
ϕ ≡ₒ[ k ] ψ =  ↓ k ϕ  ≡ₒ  ↓ k ψ
\end{code}

\noindent This is an equivalence relation.

\begin{code}
≡ₒ[]-refl : ∀ {ϕ}{ψ}{k} → ϕ ≡ ψ → ϕ ≡ₒ[ k ] ψ
≡ₒ[]-refl {ϕ}{ψ}{k} refl = ≡ₒ-refl{S = ↓ k ϕ} refl

≡ₒ[]-sym : ∀ {ϕ}{ψ}{k} → ϕ ≡ₒ[ k ] ψ → ψ ≡ₒ[ k ] ϕ
≡ₒ[]-sym {ϕ}{ψ}{k} ϕ=ψ = ≡ₒ-sym{S = ↓ k ϕ}{↓ k ψ} ϕ=ψ

≡ₒ[]-trans : ∀ {ϕ}{ψ}{þ}{k} → ϕ ≡ₒ[ k ] ψ → ψ ≡ₒ[ k ] þ → ϕ ≡ₒ[ k ] þ
≡ₒ[]-trans {ϕ}{ψ}{þ}{k} ϕ=ψ ψ=þ = ≡ₒ-trans{S = ↓ k ϕ}{↓ k ψ}{↓ k þ} ϕ=ψ ψ=þ
\end{code}

Two propositions are trivially equivalent for zero steps.

\begin{code}
≡ₒ[0] : ∀{ϕ ψ : Setₒ} → ϕ ≡ₒ[ 0 ] ψ
≡ₒ[0] k = (λ ↓0ϕ → ⊥-elimₚ (n≮0ₚ{k} (proj₁ₚ ↓0ϕ))) ,ₚ λ ↓0ψ → ⊥-elimₚ (n≮0ₚ{k} (proj₁ₚ ↓0ψ))
\end{code}

If two propositions are equivalent, then they are k-equivalent.

\begin{code}
cong-approx : ∀ {ϕ ψ : Setₒ} k → ϕ ≡ₒ ψ → ϕ ≡ₒ[ k ] ψ
cong-approx {ϕ} {ψ} k ϕ=ψ i = (λ {(i<k ,ₚ ϕi) → i<k ,ₚ (proj₁ₚ (ϕ=ψ i)) ϕi })
                             ,ₚ (λ {(i<k ,ₚ ψi) → i<k ,ₚ (proj₂ₚ (ϕ=ψ i)) ψi })
\end{code}

Going in the other direction, if two propositions are k-equivalent for
every k, then they are equivalent.

\begin{code}
equiv-approx : ∀{ϕ ψ : Setₒ} → (∀ k → ϕ ≡ₒ[ k ] ψ) → ϕ ≡ₒ ψ
equiv-approx ∀k,ϕ=[k]ψ i =
  let ↓ϕ⇔↓ψ = ∀k,ϕ=[k]ψ (suc i) i in
  (λ ϕi → let ↓siψi = proj₁ₚ ↓ϕ⇔↓ψ ((s≤sₚ{i}{i} (≤-reflₚ{i})) ,ₚ ϕi) in proj₂ₚ ↓siψi)
  ,ₚ (λ ψi → let ↓siϕi = proj₂ₚ ↓ϕ⇔↓ψ ((s≤sₚ{i}{i} (≤-reflₚ{i})) ,ₚ ψi) in proj₂ₚ ↓siϕi)

\end{code}

We need to reason about the interaction of the approximation operator
and k-equivalence. In particular, cutting off a proposition at index
\textsf{k} does not matter when reasoning about equivalence at a
smaller index \textsf{j}.

\begin{code}
j≤k⇒↓kϕ≡[j]ϕ : ∀{j k} (ϕ : Setₒ) → j ≤ₚ k → ↓ k ϕ ≡ₒ[ j ] ϕ
j≤k⇒↓kϕ≡[j]ϕ {j} {k} ϕ j≤k i =
  (λ {(i<j ,ₚ (i<k ,ₚ ϕi)) → i<j ,ₚ ϕi}) ,ₚ (λ {(i<j ,ₚ ϕi) → i<j ,ₚ (≤-transₚ{suc i}{j}{k} i<j j≤k ,ₚ ϕi)})
\end{code}

\noindent A useful corollary of this fact is that ϕ is k-equivalent to ↓ (k $\plus$ 1) ϕ.

\begin{code}
lemma17 : ∀ {ϕ} k → ↓ (suc k) ϕ ≡ₒ[ k ] ϕ
lemma17 {ϕ} k = j≤k⇒↓kϕ≡[j]ϕ {k}{suc k} ϕ (n≤1+nₚ k)
\end{code}

We extend the approximation operator to predicates as follows.

\begin{code}
↓ᵖ : ℕ → ∀{A} → Predₒ A → Predₒ A
↓ᵖ j P a = ↓ j (P a)
\end{code}

\noindent The approximation operator on predicates is congruent.

\begin{code}
cong-approxᵖ : ∀{A}{k : ℕ} → congruentᵖ{A}{A} (↓ᵖ k)
cong-approxᵖ {A} {k} {P} {Q} eq a i =
  (λ {(i<k ,ₚ Pa) → i<k ,ₚ proj₁ₚ (eq a i) Pa}) ,ₚ λ {(i<k ,ₚ Qa) → i<k ,ₚ proj₂ₚ (eq a i) Qa}
\end{code}
