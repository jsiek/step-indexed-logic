\begin{comment}
\begin{code}
{-# OPTIONS --without-K --prop #-}

open import Data.Nat using (ℕ; zero; suc; _∸_)
open import Function using (id; _∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; cong-app; subst)

open import PropP
open import RawSetO
open import Approx
open import EquivalenceRelationProp

module Iteration where
\end{code}
\end{comment}

\subsection{Iteration}
\label{sec:iteration}

As is typical for fixpoint theorems, we construct the fixpoint by
iterating a function. So we start by defining function iteration as
follows.

\begin{code}
infixr 8 _^_
_^_ : ∀ {ℓ} {A : Set ℓ} → (A → A) → ℕ → (A → A)
f ^ zero     =  id
f ^ (suc n)  =  f ∘ (f ^ n)
\end{code}

Iterating a downward closed functional produces a downward closed predicate.

\begin{code}
down-iter : ∀(i : ℕ){A} (F : Funₒ A A) → downClosed-fun F → ∀ a → downClosed ((F ^ i) (λ _ _ → ⊤ₚ) a)
down-iter zero F dc-F = λ a n _ k _ → ttₚ
down-iter (suc i) F dc-F = λ a → dc-F ((F ^ i) (λ _ _ → ⊤ₚ)) a (down-iter i F dc-F)
\end{code}

How does iteration relate to subtraction?  Suppose k is greater or
equal to j. Then iterating k times is equivalent to iterator $k - j$
times and then $j$ times.

\begin{code}
iter-subtract : ∀{ℓ}{A : Set ℓ}{a : A} (f : A → A) (j k : ℕ) → j ≤ₚ k
  → (f ^ j) ((f ^ (k ∸ j)) a) ≡ (f ^ k) a
iter-subtract {A = A} {a} f zero k z≤n = refl
iter-subtract {A = A} {a} f (suc j) (suc k) j≤k rewrite iter-subtract{A = A}{a} f j k j≤k  = refl
\end{code}

Next we prove two lemmas regarding iteration and $k$-equivalence.
They are adaptations of Lemma 15 of \citet{Appel:2001aa}.  The first
lemma says that if a functional is iterated $j$ times starting with
possibly-different predicates $P$ and $Q$, the results will always be
$j$-equivalent, that is, the $P$ and $Q$ do not matter.

\begin{minipage}{\textwidth}
\begin{code}
lemma15a : ∀ {A}{P Q : Predₒ A} j → (f : Funₒ A A) (a : A) → contractiveᵖ f → congruentᵖ f
  → (f ^ j) P a ≡ₒ[ j ] (f ^ j) Q a
lemma15a {A} {P} {Q} zero f a contr-f congr-f = ≡ₒ[0]
lemma15a {A} {P} {Q} (suc j) f a contr-f congr-f =
    ↓ (suc j) (f ((f ^ j) P) a)
  ⩦⟨ contr-f a ((f ^ j) P) j ⟩
    ↓ (suc j) (f (↓ᵖ j ((f ^ j) P)) a)
  ⩦⟨ cong-approxᵖ{k = suc j} (congr-f λ a → lemma15a j f a contr-f congr-f) a ⟩ 
    ↓ (suc j) (f (↓ᵖ j ((f ^ j) Q)) a)
  ⩦⟨ ≡ₒ-sym (contr-f a ((f ^ j) Q) j) ⟩ 
    ↓ (suc j) (f ((f ^ j) Q) a)
  ∎
\end{code}
\end{minipage}

The second lemma says that when reasoning up to $j$-equivalence, it
does not matter if you iterate more than $j$ times. In particular, if
$k$ is greater or equal to $j$, then $f^j\;P \; a$ is $j$-equivalent
to $f^k\;P \; a$.

\begin{minipage}{\textwidth}
\begin{code}
lemma15b : ∀{A}{P : Predₒ A} (k j : ℕ) (f : Funₒ A A) (a : A)
   → j ≤ₚ k → contractiveᵖ f → congruentᵖ f
   → (f ^ j) P a ≡ₒ[ j ] (f ^ k) P a
lemma15b {A}{P} k j f a j≤k wf-f cong-f =
    ↓ j ((f ^ j) P a)
  ⩦⟨ lemma15a j f a wf-f cong-f ⟩
    ↓ j ((f ^ j) ((f ^ (k ∸ j)) P) a)
  ⩦⟨ cong-approxᵖ{A}{j}{(f ^ j) ((f ^ (k ∸ j)) P)}{(f ^ k) P} (λ a → ≡ᵖ-refl (iter-subtract f j k j≤k)) a ⟩
    ↓ j ((f ^ k) P a)
  ∎
\end{code}
\end{minipage}
