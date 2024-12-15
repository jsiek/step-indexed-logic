\begin{comment}
\begin{code}
{-# OPTIONS --without-K --prop #-}

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import PropP
open import EquivalenceRelation using (EquivalenceRelation; _⇔_; ⩦-refl; ⩦-sym; ⩦-trans)
open import RawSetO
open import Approx
open import Iteration
open import SILVariables

module Env where
\end{code}
\end{comment}

\subsection{Environment of Recursive Predicates}
\label{sec:rec-env}

The semantics of a SIL formula that resides inside the definition of a
recursive predicate is a bit more complex than simply being a function
from ℕ to \textsf{Prop}. The reason is that the semantics of such
formulas are parameterized on the meaning of the recursive predicate.
SIL allows recursive predicates to be nested, so the semantics is
parameterized by a tuple of predicates, i.e., a \textit{recursive
environment}, whose type is given by the following \textsf{RecEnv}.

\begin{code}
RecEnv : Context → Set₁
RecEnv [] = topᵖ 
RecEnv (A ∷ Γ) = (Predₒ A) × RecEnv Γ
\end{code}

We define downward-closed for recursive environments as follows.

\begin{code}
downClosedᵈ : ∀{Γ} → RecEnv Γ → Prop
downClosedᵈ {[]} δ = ⊤ₚ
downClosedᵈ {A ∷ Γ} (P , δ) = (∀ a → downClosed (P a)) ×ₚ downClosedᵈ δ
\end{code}

The k-approximation operator is extended to recursive environments
with the following definition of $↓ᵈ \; k\; x\; δ$ which applies
$k$-approximation to the entry for $x$ in δ but otherwise acts as the
identity function.

\begin{code}
↓ᵈ : ℕ → ∀{Γ}{A} → Γ ∋ A → RecEnv Γ → RecEnv Γ
↓ᵈ k {A ∷ Γ} {.A} zeroᵒ (P , δ) = ↓ᵖ k P , δ
↓ᵈ k {A ∷ Γ} {B} (sucᵒ x) (P , δ) = P , ↓ᵈ k x δ
\end{code}

Two recursive environments are equivalent if their predicates are
pairwise equivalent.

\begin{code}
_≡ᵈ_ : ∀{Γ} → RecEnv Γ → RecEnv Γ → Prop
_≡ᵈ_ {[]} δ δ′ = ⊤ₚ
_≡ᵈ_ {A ∷ Γ} (P , δ) (Q , δ′) = (∀ a → P a ≡ₒ Q a) ×ₚ δ ≡ᵈ δ′
\end{code}

\noindent Of course, a recursive environment is equivalent to itself.

\begin{code}
≡ᵈ-refl : ∀{Γ}{δ : RecEnv Γ} → δ ≡ᵈ δ
≡ᵈ-refl {[]} {δ} = ttₚ
≡ᵈ-refl {A ∷ Γ} {(P , δ)} = (λ a → ≡ₒ-refl refl) ,ₚ ≡ᵈ-refl
\end{code}


\subsection{Semantic Representation, Contractive, Nonexpansive, and Congruent}

With the definition of \textsf{RecEnv} in hand, we next define the type
of the semantics of a SIL proposition. For a given context Γ, the
semantics of a SIL proposition is a function from \textsf{RecEnv Γ} to
\textsf{Setₒ}.

\begin{code}
RSetₒ : Context → Set₁
RSetₒ Γ = RecEnv Γ → Setₒ
\end{code}

A SIL proposition $P$ is \textit{contractive} with respect to variable $x$
if for any environment δ, $P \; δ$ is $(k \plus 1)$-equivalent to
$P \; (↓ᵈ \; j \; x \; δ)$, assuming that $k$ is less-or-equal $j$.

\begin{code}
contractive : ∀{Γ}{A} → (x : Γ ∋ A) → RSetₒ Γ → Prop₁
contractive x P = ∀ δ j k → k ≤ₚ j → P δ ≡ₒ[ suc k ] P (↓ᵈ j x δ)
\end{code}

\noindent This definition of contractive is an adaptation of the
notion of of well founded functional of \citet{Appel:2001aa} to the
type \textsf{RSetₒ}. However, \citet{Appel:2001aa} fix $j=k$ instead
of allowing $k ≤ j$ as we do here. This generalization is necessary to
allow nesting of recursive predicates, which was overlooked by
\citet{Appel:2001aa}. Our definition of contractive is different but
equivalent to the notion of contractive for Ordered Families of
Equalities~\citep{Di-Gianantonio:2003aa,JUNG:2018aa}.

A SIL proposition $P$ is \textit{nonexpansive} with respect to
variable $x$ if for any environment δ, $P \; δ$ is $k$-equivalent to
$P \; (↓ᵈ \; j \; x \; δ)$, assuming that $k$ is less-or-equal $j$.

\begin{code}
nonexpansive : ∀{Γ}{A} → (x : Γ ∋ A) → RSetₒ Γ → Prop₁
nonexpansive x P = ∀ δ j k → k ≤ₚ j → P δ ≡ₒ[ k ] P (↓ᵈ j x δ)
\end{code}

A SIL proposition $P$ is \textit{wellformed} with respect to variable
$x$ if (1) the time for $x$ is \textsf{Now} and $P$ is nonexpansive in
$x$ or (2) the time for $x$ is \textsf{Later} and $P$ is contractive
in $x$.

\begin{code}
wellformed-var : ∀{Γ}{A} → (x : Γ ∋ A) → Time → RSetₒ Γ → Prop₁
wellformed-var x Now P = nonexpansive x P
wellformed-var x Later P = contractive x P
\end{code}

A SIL proposition $P$ is \textit{wellformed} if it is wellformed with
respect to all of the variables that are in scope.

\begin{code}
wellformed-prop : ∀{Γ} → Times Γ → RSetₒ Γ → Prop₁
wellformed-prop {Γ} Δ P = ∀{A} (x : Γ ∋ A) → wellformed-var x (timeof x Δ) P
\end{code}

As a direct consequence of the above definitions, if $P$ is well
formed in $x$, and the time of $x$ is \textsf{Now}, then $P$ is
nonexpansive in $x$.

\begin{code}
wellformed-now⇒nonexpansive : ∀{Γ}{A}{x : Γ ∋ A}{Δ : Times Γ}{P : RSetₒ Γ}
   → wellformed-var x (timeof x Δ) P → timeof x Δ ≡ Now
   → nonexpansive x P
wellformed-now⇒nonexpansive gP eq rewrite eq = gP
\end{code}

\noindent Similarly, if $P$ is well formed in $x$, and the time of $x$
is \textsf{Later}, then $P$ is contractive in $x$.

\begin{code}
wellformed-later⇒contractive : ∀{Γ}{A}{x : Γ ∋ A}{Δ : Times Γ}{P : RSetₒ Γ}
   → wellformed-var x (timeof x Δ) P → timeof x Δ ≡ Later
   → contractive x P
wellformed-later⇒contractive gP eq rewrite eq = gP
\end{code}

We define a \textsf{congruent} proposition $P$ to be one in which
applying $P$ to equivalent environments yields equivalent step-indexed
propositions.

\begin{code}
congruent : ∀{Γ : Context} → RSetₒ Γ → Prop₁
congruent P = ∀{δ δ′} → δ ≡ᵈ δ′ → (P δ) ≡ₒ (P δ′)
\end{code}



