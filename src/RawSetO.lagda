\begin{comment}
\begin{code}
{-# OPTIONS --without-K --prop #-}

open import Data.Nat using (ℕ)
open import EquivalenceRelationProp using (EquivalenceRelation; _⇔_; ⇔-refl; ⇔-sym; ⇔-trans)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import PropP

module RawSetO where
\end{code}
\end{comment}

The basic idea for embedding the Step-Indexed Logic (SIL) in Agda is
that we represent a step-indexed proposition of SIL as an Agda function
from ℕ to \textsf{Prop}.

\begin{code}
Setₒ : Set₁
Setₒ = ℕ → Prop
\end{code}

\noindent The \textsf{Prop} type is Agda's type for propositions where
all proofs of the same proposition are considered equal.  (The
alternative would be to use the \textsf{Set} type, but we were forced
to use \textsf{Prop} for technical reasons that we discuss in due
course.)

In general, when a SIL proposition is true at a given time must also
be true at all later times (at smaller step indices). Thus, we require
that they must be downward closed.

\begin{code}
downClosed : Setₒ → Prop
downClosed S = ∀ n → S n → ∀ k → k ≤ₚ n → S k
\end{code}

Two propositions \textsf{S} and \textsf{T} are equivalent if they are
equivalent at every step index \textsf{k}. This notion of equivalence
is of course an equivalence relation.

\begin{code}
infix 2 _≡ₒ_
_≡ₒ_ : Setₒ → Setₒ → Prop
S ≡ₒ T = ∀ k → S k ⇔ T k

≡ₒ-refl : ∀{S T : Setₒ} → S ≡ T → S ≡ₒ T
≡ₒ-refl refl i = ⇔-refl refl

≡ₒ-sym : ∀{S T : Setₒ} → S ≡ₒ T → T ≡ₒ S
≡ₒ-sym ST i = ⇔-sym (ST i)

≡ₒ-trans : ∀{S T R : Setₒ} → S ≡ₒ T → T ≡ₒ R → S ≡ₒ R
≡ₒ-trans ST TR i = ⇔-trans (ST i) (TR i)
\end{code}

\noindent We create an instance of \textsf{EquivalenceRelation}
(defined in the Appendix) to obtain syntax for equational reasoning.

\begin{code}
instance
  SIL-Eqₒ : EquivalenceRelation Setₒ
  SIL-Eqₒ = record { _⩦_ = _≡ₒ_ ; ⩦-refl = ≡ₒ-refl ; ⩦-sym = ≡ₒ-sym ; ⩦-trans = ≡ₒ-trans }
\end{code}

A SIL predicate is embedded into Agda as a function from any type \textsf{A}
to \textsf{Setₒ}.

\begin{code}
Predₒ : Set → Set₁
Predₒ A = A → Setₒ
\end{code}

\noindent SIL predicates are also downward closed.

\begin{code}
downClosedᵖ : ∀{A} (P : Predₒ A) → Prop
downClosedᵖ {A} P = ∀ (a : A) → downClosed (P a)
\end{code}

\noindent The always-true predicate is defined as follows.

\begin{code}
⊤ᵖ : ∀{A} → Predₒ A
⊤ᵖ = λ _ _ → ⊤ₚ
\end{code}

\noindent The following lemma is handy for showing that when two
predicates are equal, applying them to the same argument produces
equivalent propositions.

\begin{code}
≡ᵖ-refl : ∀{A}{P Q : Predₒ A} → P ≡ Q → ∀ {a} → P a ≡ₒ Q a
≡ᵖ-refl refl {a} = ≡ₒ-refl refl
\end{code}


To define recursive predicates, we introduce the notion of a
\emph{functional}, which is a function whose input and output are
predicates. The idea is that the fixpoint operator μᵒ binds the input
parameter of the functional to the recursive predicate itself, thereby
tying the recursive knot.

\begin{code}
Funₒ : Set → Set → Set₁
Funₒ A B = Predₒ A → Predₒ B
\end{code}

\noindent The functionals are required to preserve downward closedness.

\begin{code}
downClosed-fun : ∀{A}{B} (F : Funₒ A B) → Prop₁
downClosed-fun {A}{B} F = ∀ P b → downClosedᵖ P → downClosed (F P b)
\end{code}

\noindent Furthermore, the functions should act as (mathematical)
functions with respect to equivalence. That is, a functional should
map equivalent inputs to equivalent outputs.

\begin{code}
congruentᵖ : ∀{A}{B} (F : Funₒ A B) → Prop₁
congruentᵖ F = ∀ {P Q} → (∀ a → P a ≡ₒ Q a) → ∀ b → (F P b) ≡ₒ (F Q b)
\end{code}



