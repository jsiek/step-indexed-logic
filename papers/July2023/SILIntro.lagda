\begin{comment}
\begin{code}
{-# OPTIONS --rewriting --without-K --prop --allow-unsolved-metas #-}
module July2023.SILIntro where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
   using (_×_; _,_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Unit using (tt; ⊤)
open import Relation.Nullary using (¬_)
open import EquivalenceRelation public

open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Data.List using (List; []; _∷_)
open import Data.Nat
   using (ℕ; zero; suc; _≤_; _<_; _+_; _∸_; _*_; z≤n; s≤s; _≤′_; ≤′-step; ≤-pred)
open import Data.Nat.Properties
   using (≤-refl; ≤-antisym; ≤-trans; ≤-step; ≤⇒≤′; ≤′⇒≤; n≤1+n; <⇒≤; s≤′s; 0≢1+n; *-distribˡ-+; +-comm)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; cong-app; subst)
open import Function using (id; _∘_)
open import Level using (Lift)
open import StepIndexedLogic2
open import PropP

\end{code}
\end{comment}

\section{Introduction to Step-Indexed Logic for PL Mechanizers}
\label{sec:SIL-intro}

The first thing to know about SIL is that it is a logic that emulates
Agda's logic. For example, the type of a logical formula in Agda is
\textsf{Set} and in SIL it is \textsf{Set}ᵒ. To distinguish SIL from
Agda, we add a superscript ``o'' to most names. Unlike \textsf{Set},
\textsf{Set}ᵒ type is parameterized by two lists that enable SIL to
ensure that recursively-defined predicates are well defined, but we
get ahead of ourselves.

\begin{code}
_ : Set₁
_ = Setᵒ [] []
\end{code}

\noindent Let the following variables range over \textsf{Set}ᵒ.

\begin{code}
variable ϕ ϕ′ ψ ψ′ χ : Setᵒ [] []
\end{code}

SIL defines an entailment relation 𝒫 ⊢ᵒ ϕ to express that a SIL
formula ϕ is provable from the list of formulas 𝒫. If 𝒫 is empty, then
ϕ is just plain true.

The ``pure'' connective imports an Agda proposition into SIL.

\begin{code}
_ : Set → Setᵒ [] []
_ = _ᵒ
\end{code}

\noindent For example, we can use the pure connective to express
properties of numbers, such as $1 \plus 1 = 2$.  The \textsf{pureᵒI}
function is a proof constructor, which we discuss in
Section~\ref{sec:proof-rules}.

\begin{code}
_ : Setᵒ [] []
_ = (1 + 1 ≡ 2)ᵒ
\end{code}

\subsection{SIL is a propositional logic}

The ``true'' formula in SIL is written ⊤ᵒ and
the ``false'' formula is ⊥ᵒ.

\begin{code}
_ : Setᵒ [] []
_ = ⊤ᵒ

_ : Setᵒ [] []
_ = ⊥ᵒ
\end{code}

\noindent SIL includes the logical connectives for conjunction,
disjunction, and implication.

\begin{code}
_ : Setᵒ [] [] → Setᵒ [] [] → Setᵒ [] []
_ = _×ᵒ_

_ : Setᵒ [] [] → Setᵒ [] [] → Setᵒ [] []
_ = _⊎ᵒ_

_ : Setᵒ [] [] → Setᵒ [] [] → Setᵒ [] []
_ = _→ᵒ_
\end{code}

\noindent The meanings of these quantifiers match those of the
corresponding ones in Agda.


\subsection{SIL is a first-order logic}

\begin{code}
variable A B C : Set
\end{code}

SIL is a first-order logic, so it includes the universal and
existential quantifiers. SIL uses Agda functions to handle the
quantification.  So the ``for all'' quantifier ∀ᵒ has the following
type.

\begin{code}
_ : (A → Setᵒ [] []) → Setᵒ [] []
_ = ∀ᵒ
\end{code}

\noindent As a simple example, the following SIL formula says that
for any $x$, $2x = x \plus x$.

\begin{code}
_ : Setᵒ [] []
_ = ∀ᵒ λ x → (2 * x ≡ x + (x + 0))ᵒ
\end{code}

\noindent SIL provides alternate notation for universal
quantification, replacing the λ with a pair of brackets around the
bound variable.

\begin{code}
_ : Setᵒ [] []
_ = ∀ᵒ[ x ⦂ ℕ ] (2 * x ≡ x + (x + 0))ᵒ
\end{code}

For the existential quantifier of SIL, we also use Agda functions for
quantification. However, for technical reasons we require the type $A$
to be inhabited, which we express using an implicit instance argument
to avoid cluttering the uses of ∃ᵒ.

\begin{code}
_ : (A → Setᵒ [] []) → Setᵒ [] []
_ = ∃ᵒ
\end{code}

\noindent The following formula shows an example use of the
existential in SIL to state that there exists an $x$ such that
$2x =6$.

\begin{code}
_ : Setᵒ [] []
_ = ∃ᵒ[ x ] (2 * x ≡ 6)ᵒ
\end{code}

\subsection{SIL has User-defined Recursive Predicates}
\label{sec:intro-recursive-predicates}

The central feature of SIL is user-defined recursive predicates, via
the μᵒ operator. To present a familiar example, we shall define the
even numbers in SIL. Recall that in Agda we could define the even
numbers as follows using a \textsf{data} definition.

\begin{code}
data Even : ℕ → Set where
  Even-zero : Even zero
  Even-plus-two : ∀ m → Even m → Even (2 + m)
\end{code}

To define a recursive predicate in SIL, we apply the μᵒ connective to
a function from the predicate's domain to a SIL formula. Here's the
definition of \textsf{Even}′ in SIL, which we explain in detail below.

\begin{code}
Even′ : ℕ → Setᵒ [] []
Even′ = μᵒ λ n → (n ≡ zero)ᵒ ⊎ᵒ (∃ᵒ[ m ] (n ≡ 2 + m)ᵒ ×ᵒ ▷ᵒ (m ∈ recᵒ))
\end{code}

\noindent The formula \textsf{recᵒ} stands for ``this recursive
predicate``.  So $m ∈ \mathsf{rec}ᵒ$ is morally equivalent to saying
$m ∈ \mathsf{Even}′$.  More precisely, \textsf{rec}ᵒ refers to the
nearest enclosing μᵒ.

The use of ▷ᵒ in $▷ᵒ (m ∈ \mathsf{rec}ᵒ)$ serves to guard the
recursion to ensure that the recursive definition is well defined.
SIL uses the two parameters of \textsf{Set}ᵒ for this purpose. The
first parameter is a list of the domain types for all the recursive
predicates in scope (often just zero or one). We refer to such as list
as a \textsf{Context}. Let Γ range over contexts.

\begin{code}
variable Γ : Context
\end{code}

\noindent The second parameter of \textsf{Set}ᵒ tracks the usage time
(\textsf{Now} or \textsf{Later}) for each recursive predicate that is
in scope.

\begin{code}
variable Δ Δ₁ Δ₂ : Times Γ
\end{code}

\noindent When SIL sees the use of a recursive predicate, such as
$\mathsf{rec}ᵒ$, it clasifies that the predicate as being used
\textsf{Now}. (The \textsf{laters} function creates a list of the same
length as Γ whose elements are all \textsf{Later}.)

\begin{code}
_ : A → Setᵒ (A ∷ Γ) (Now ∷ laters Γ)
_ = _∈ recᵒ
\end{code}

In the unlikely event that you have multiple nested μᵒ in a formula,
you can replace \textsf{recᵒ} with a natural number (a de Bruijn index
built from \textsf{zero}ᵒ and \textsf{suc}ᵒ) that specifies which μᵒ
you want to refer to.  (\textsf{recᵒ} is just defined to be the de
Bruijn index \textsf{zero}ᵒ.) In general, the membership connective
$a ∈ x$ has the following type, where the \textsf{var-now} function
assigns variable $x$ the time \textsf{Now} and all the other variables
in $Γ$ are assigned \textsf{Later}.

\begin{code}
_ : A → (x : Γ ∋ A) → Setᵒ Γ (var-now Γ x)
_ = _∈_
\end{code}

When the ▷ᵒ operator is applied to a subformula, all the predicates
that were used \textsf{Now} inside the subformula are instead
considered to be used \textsf{Later}.

\begin{code}
_ : Setᵒ Γ Δ → Setᵒ Γ (laters Γ)
_ = ▷ᵒ
\end{code}

Finally, when we apply the μᵒ operator, SIL checks to make sure that
the recursive uses of this predicate in its own body were categorized
as \textsf{Later}.

\begin{code}
_ : (A → Setᵒ (A ∷ Γ) (Later ∷ Δ)) → (A → Setᵒ Γ Δ)
_ = μᵒ
\end{code}


\subsection{The Proof Language of SIL}
\label{sec:proof-rules}

Let 𝒫 range over lists of propositions.

\begin{code}
variable 𝒫 : List (Setᵒ [] [])
\end{code}

\noindent We write $𝒫 ⊢ᵒ ϕ$ for entailment, which means that ϕ is true when
the list of formulas in 𝒫 are true.

\begin{code}
_ : List (Setᵒ [] []) → Setᵒ [] [] → Prop
_ = _⊢ᵒ_
\end{code}

\noindent When $𝒫$ is the empty list, as in $[] ⊢ᵒ ϕ$, then we say
that ϕ is unconditionally true (or just true).  In the rest of this
section we discuss the rules of SIL that can be used to prove an
entailment.

Let the following variables range over formulas in Agda.
\begin{code}
variable p q r : Set
\end{code}

We start with the pure connective. Given a proof of an Agda formula
$p$, the rule \textsf{pureᵒI} produces a proof of $𝒫 ⊢ᵒ p ᵒ$.

\begin{code}
_ : p → 𝒫 ⊢ᵒ p ᵒ
_ = pureᵒI
\end{code}

\noindent For example, we can prove that $1 \plus 1 = 2$ in SIL as
follows.

\begin{code}
_ : [] ⊢ᵒ ((1 + 1 ≡ 2)ᵒ)
_ = pureᵒI refl
\end{code}

If instead you have a proof of $pᵒ$ and have some goal χ to prove,
then you can assume that $p$ is true while proving χ.  That is,
$\mathsf{pure}ᵒE\, ϕ\, F$ is a proof of χ if ϕ is a proof of pᵒ and $F$ is a
function from $p$ to a proof of χ.

\begin{code}
_ : 𝒫 ⊢ᵒ p ᵒ  →  (p → 𝒫 ⊢ᵒ χ)  →  𝒫 ⊢ᵒ χ
_ = pureᵒE
\end{code}

\noindent For example, we can prove that $(x ≡ y)ᵒ$
implies $(y ≡ x)ᵒ$ using \textsf{pureᵒE} as follows.

\begin{code}
_ : ∀(x y : ℕ) → [] ⊢ᵒ (x ≡ y) ᵒ → [] ⊢ᵒ (y ≡ x)ᵒ
_ = λ x y x=yᵒ → pureᵒE x=yᵒ λ {refl → pureᵒI refl}
\end{code}

\subsubsection{Reasoning in Propositional Logic}

For the propositional connectives, many of the proof rules are the
same as those in Agda but with a superscript ``o''.  For example, the
introduction rule for ⊤ in Agda is \textsf{tt} so in SIL it's
\textsf{tt}ᵒ.

\begin{code}
_ : 𝒫 ⊢ᵒ ⊤ᵒ 
_ = ttᵒ
\end{code}

For conjunction, the introduction rule is the comma and elimination is
\textsf{proj₁ᵒ} and \textsf{proj₂ᵒ}.

\begin{code}
_ : 𝒫 ⊢ᵒ ϕ → 𝒫 ⊢ᵒ ψ → 𝒫 ⊢ᵒ ϕ ×ᵒ ψ
_ = _,ᵒ_

_ : 𝒫 ⊢ᵒ ϕ ×ᵒ ψ  →  𝒫 ⊢ᵒ ϕ
_ = proj₁ᵒ

_ : 𝒫 ⊢ᵒ ϕ ×ᵒ ψ  →  𝒫 ⊢ᵒ ψ
_ = proj₂ᵒ
\end{code}

\noindent As an example use of the rules for conjuction, here's one
direction of the associativity of conjunction.

\begin{code}
_ : 𝒫 ⊢ᵒ ϕ ×ᵒ (ψ ×ᵒ χ) → 𝒫 ⊢ᵒ (ϕ ×ᵒ ψ) ×ᵒ χ
_ = λ ϕ×[ψ×χ] → (proj₁ᵒ ϕ×[ψ×χ] ,ᵒ (proj₁ᵒ (proj₂ᵒ ϕ×[ψ×χ]))) ,ᵒ proj₂ᵒ (proj₂ᵒ ϕ×[ψ×χ])
\end{code}

For disjunction, the introduction rules are \textsf{inj₁ᵒ} and
\textsf{inj₂ᵒ}.

\begin{code}
_ : 𝒫 ⊢ᵒ ϕ  →  𝒫 ⊢ᵒ ϕ ⊎ᵒ ψ
_ = inj₁ᵒ

_ : 𝒫 ⊢ᵒ ψ  →  𝒫 ⊢ᵒ ϕ ⊎ᵒ ψ
_ = inj₂ᵒ
\end{code}

\noindent Agda uses its builtin pattern-matching to eliminate
disjunction. So for SIL, we must instead define the following
\textsf{case} rule. If you have a proof of $ϕ ⊎ᵒ ψ$ and would like to
prove χ, then it suffices to prove two cases: 1) assuming ϕ show χ and
2) assuming ψ show χ.

\begin{code}
_ : 𝒫 ⊢ᵒ ϕ ⊎ᵒ ψ  →  ϕ ∷ 𝒫 ⊢ᵒ χ  →  ψ ∷ 𝒫 ⊢ᵒ χ  →  𝒫 ⊢ᵒ χ
_ = caseᵒ
\end{code}

\noindent The \textsf{case}ᵒ rule adds assumptions to the left-hand
side of the entailment. To make use of such assumptions, specify its
position in the list using a natural number. So zero refers to the
front of the list:

\begin{code}
_ : ϕ ∷ 𝒫 ⊢ᵒ ϕ
_ = Zᵒ
\end{code}

\noindent and the successor operator skips over the front of the list
(aka. weakening).

\begin{code}
_ : 𝒫 ⊢ᵒ ψ  →  ϕ ∷ 𝒫 ⊢ᵒ ψ
_ = Sᵒ
\end{code}

Putting these ingredients together, the following proof shows that
disjunction is commutative using its introduction and elimination
rules and also the \textsf{Z}ᵒ rule for accessing the assumption.

\begin{code}
_ : 𝒫 ⊢ᵒ ϕ ⊎ᵒ ψ  →  𝒫 ⊢ᵒ ψ ⊎ᵒ ϕ
_ = λ ϕ⊎ψ → caseᵒ ϕ⊎ψ (inj₂ᵒ Zᵒ) (inj₁ᵒ Zᵒ)
\end{code}

Implication is introduced by λᵒ.

\begin{code}
_ : ∀ ϕ → (ϕ ∷ 𝒫 ⊢ᵒ ϕ → ϕ ∷ 𝒫 ⊢ᵒ ψ)  →  𝒫 ⊢ᵒ ϕ →ᵒ ψ
_ = λᵒ
\end{code}

\noindent For example, the following is the trivial proof that ϕ implies ϕ.

\begin{code}
_ : ∀ ϕ →  [] ⊢ᵒ ϕ →ᵒ ϕ
_ = λ ϕ →  λᵒ ϕ λ x → x
\end{code}

\noindent SIL provides an alternative syntax that replaces the extra λ
with brackets.

\begin{code}
_ : ∀ ϕ →  [] ⊢ᵒ ϕ →ᵒ ϕ
_ = λ ϕ →  λᵒ[ x ⦂ ϕ ] x
\end{code}

\noindent Implication is eliminated by →ᵒE.
\begin{code}
_ : 𝒫 ⊢ᵒ ϕ →ᵒ ψ  →  𝒫 ⊢ᵒ ϕ  →  𝒫 ⊢ᵒ ψ
_ = →ᵒE
\end{code}

\noindent The following example proof applies the introduction and
elimination rules for implication to prove that implication is
transitive.

\begin{code}
_ : 𝒫 ⊢ᵒ ϕ →ᵒ ψ  →  𝒫 ⊢ᵒ ψ →ᵒ χ  →  𝒫 ⊢ᵒ ϕ →ᵒ χ
_ = λ ϕ→ψ ψ→χ → →ᵒI (→ᵒE (Sᵒ ψ→χ) (→ᵒE (Sᵒ ϕ→ψ) Zᵒ))
\end{code}

\subsubsection{Reasoning in First-Order Logic}

Moving on to the proof rules for universal and existential
quantifiers.  The universal quantifier is introduced by Λᵒ. So to
prove $∀ᵒ[ a ⦂ A ]\, ϕᵃ\, a$, you apply Λᵒ to an Agda function that,
given an arbitrary $a$, produces a proof of $ϕᵃ\, a$.

\begin{code}
_ : {ϕᵃ : A → Setᵒ [] []} → (∀ a → 𝒫 ⊢ᵒ ϕᵃ a)  →  𝒫 ⊢ᵒ ∀ᵒ[ a ⦂ A ] ϕᵃ a
_ = Λᵒ
\end{code}

\noindent SIL also provides a bracket notation for Λᵒ. As an example
use of ∀ᵒ and Λᵒ, we state and prove that addition is commutative.

\begin{code}
∀x,y,x+y=y+x : [] ⊢ᵒ ∀ᵒ[ x ⦂ ℕ ] ∀ᵒ[ y ⦂ ℕ ] (x + y ≡ y + x)ᵒ
∀x,y,x+y=y+x = Λᵒ[ x ] Λᵒ[ y ] pureᵒI (+-comm x y)
\end{code}

\noindent The universal quantifier is eliminated by ∀ᵒE.

\begin{code}
_ : ∀{ϕᵃ : A → Setᵒ [] []} → 𝒫 ⊢ᵒ ∀ᵒ ϕᵃ  →  (a : A)  →  𝒫 ⊢ᵒ ϕᵃ a
_ = ∀ᵒE
\end{code}

\noindent For example, the following proves that $x = x + 0$ using the
above fact about the commutativity of addition.

\begin{code}
_ : ∀ (x : ℕ) → [] ⊢ᵒ (x ≡ x + 0)ᵒ
_ = λ x → pureᵒE (∀ᵒE (∀ᵒE ∀x,y,x+y=y+x x) 0) λ x+0=x → pureᵒI (sym x+0=x)
\end{code}

The existential quantifier of SIL is introduced by the rule ∃ᵒI and
eliminated by the rule unpackᵒ.

\begin{code}
_ : ∀{ϕᵃ : A → Setᵒ [] []} →  (a : A)  →  𝒫 ⊢ᵒ ϕᵃ a  →  𝒫 ⊢ᵒ ∃ᵒ ϕᵃ
_ = ∃ᵒI

_ : ∀{ϕᵃ : A → Setᵒ [] []}{χ : Setᵒ [] []}
     → 𝒫 ⊢ᵒ ∃ᵒ ϕᵃ  →  (∀ a  →  ϕᵃ a ∷ 𝒫 ⊢ᵒ ϕᵃ a  →  ϕᵃ a ∷ 𝒫 ⊢ᵒ χ)  →  𝒫 ⊢ᵒ χ
_ = unpackᵒ
\end{code}

\noindent The following example proves that doubling an even number
yields an even number.

\begin{code}
private variable i j k m n : ℕ
\end{code}

\begin{code}
_ : ([] ⊢ᵒ ∃ᵒ[ x ] (n ≡ 2 * x)ᵒ) → ([] ⊢ᵒ ∃ᵒ[ x ] (2 * n ≡ 2 * x)ᵒ)
_ = λ n-even → unpackᵒ n-even λ x n=2xᵒ →
               pureᵒE n=2xᵒ λ {refl → ∃ᵒI (2 * x) (pureᵒI refl)}
\end{code}

\subsubsection{Reasoning about ``later''}

\begin{code}
_ : 𝒫 ⊢ᵒ ϕ  →  𝒫 ⊢ᵒ  ▷ᵒ ϕ
_ = monoᵒ
\end{code}

\begin{code}
_ : 𝒫 ⊢ᵒ ▷ᵒ (ϕ ×ᵒ ψ)  →  𝒫 ⊢ᵒ (▷ᵒ ϕ) ×ᵒ (▷ᵒ ψ)
_ = ▷×
\end{code}

\begin{code}
_ : 𝒫 ⊢ᵒ ▷ᵒ ϕ  →  ϕ ∷ 𝒫 ⊢ᵒ ψ  →  𝒫 ⊢ᵒ ▷ᵒ ψ
_ = ▷→▷
\end{code}

\begin{code}
_ : ℕ → Setᵒ Γ Δ → Setᵒ Γ (laters Γ)
_ = ◇ᵒ
\end{code}

\begin{code}
_ : ◇ᵒ 0 ϕ ≡ ▷ᵒ ϕ
_ = refl
\end{code}

\begin{code}
_ : ◇ᵒ (suc k) ϕ ≡ ◇ᵒ k (▷ᵒ ϕ)
_ = refl
\end{code}

\begin{code}
_ : ∀ i → 𝒫 ⊢ᵒ ▷ᵒ (◇ᵒ i ϕ) → 𝒫 ⊢ᵒ ◇ᵒ i (▷ᵒ ϕ)
_ = ▷◇⇒◇▷
\end{code}

\begin{code}
_ : [] ⊢ᵒ ▷ᵒ ϕ → [] ⊢ᵒ ϕ
_ = ▷ϕ⇒ϕ

_ : ∀ k → [] ⊢ᵒ ◇ᵒ k ϕ → [] ⊢ᵒ ϕ
_ = ◇ϕ⇒ϕ
\end{code}


\subsubsection{Recursive Predicates}

The introduction rule for recursive predicates is \textsf{fold}ᵒ. The
rule involves a new operator named \textsf{let}ᵒ that we discuss
below.

\begin{code}
_ : ∀{𝒫} (Sᵃ : A → Setᵒ (A ∷ []) (Later ∷ [])) (a : A) →  𝒫 ⊢ᵒ letᵒ (μᵒ Sᵃ) (Sᵃ a)  →  𝒫 ⊢ᵒ μᵒ Sᵃ a
_ = foldᵒ
\end{code}

As an example use of \textsf{fold}ᵒ, we prove that $0$ is even.
Recall that we defined \textsf{Even}′ as follows.

\begin{code}
_ : Even′  ≡  μᵒ λ n → (n ≡ zero)ᵒ ⊎ᵒ (∃ᵒ[ m ] (n ≡ 2 + m)ᵒ ×ᵒ ▷ᵒ (m ∈ recᵒ))
_ = refl
\end{code}

\noindent The first argument of \textsf{fold}ᵒ needs to be the body of
the μᵒ.  To give it a name, we define \textsf{Evenᵒ} as follows.

\begin{code}
Evenᵒ : ℕ → Setᵒ (ℕ ∷ []) (Later ∷ [])
Evenᵒ = λ n → (n ≡ zero)ᵒ ⊎ᵒ (∃ᵒ[ m ] (n ≡ 2 + m)ᵒ ×ᵒ ▷ᵒ (m ∈ recᵒ))
\end{code}

\noindent The second arugment of \textsf{fold}ᵒ is the element in the
predicate, in this case $0$, and the third argument is a proof that
the body of the predicate is true of the given element ($0$). Here's
the proof that $0$ is even, with more discussion of \textsf{even-z} in
the next paragraph.

\begin{code}
even-zero : [] ⊢ᵒ Even′ 0
even-zero = foldᵒ Evenᵒ 0 even-z
  where
  even-z : [] ⊢ᵒ ((0 ≡ zero) ᵒ) ⊎ᵒ (∃ᵒ[ m ] (0 ≡ 2 + m)ᵒ ×ᵒ ▷ᵒ (μᵒ Evenᵒ m))
  even-z = inj₁ᵒ (pureᵒI refl)
\end{code}

Looking back at the type of \textsf{fold}ᵒ, there seems to be a
mismatch between the type of the third parameter of \textsf{fold}ᵒ,
which involves \textsf{let}ᵒ, and the type of \textsf{even-z}. What's
going on here is that SIL defines a bunch of rewrite rules that
automatically propagate the \textsf{let}ᵒ down into the formula until
it reaches the membership operator $a ∈ x$, at which point the $x$ is
replaced by the right-hand side of the \textsf{let}ᵒ.  In this
example, the relevant rewrite is:

\begin{code}
_ : ∀ {m} → letᵒ (μᵒ Evenᵒ) (m ∈ recᵒ)  ≡  μᵒ Evenᵒ m
_ = refl
\end{code}

The eleminiation rule for μᵒ is \textsf{unfold}ᵒ.

\begin{code}
_ : ∀{𝒫} (Sᵃ : A → Setᵒ (A ∷ []) (Later ∷ [])) (a : A) →  𝒫 ⊢ᵒ μᵒ Sᵃ a  →  𝒫 ⊢ᵒ letᵒ (μᵒ Sᵃ) (Sᵃ a)
_ = unfoldᵒ
\end{code}

\noindent For example, if we unfold $μᵒ Evenᵒ 1$, we obtain that
either $1 = 0$ or $1 = 2 \plus m$ for some $m$. Either case is
impossible, so we conclude false.

\begin{code}
not-even-one : [] ⊢ᵒ μᵒ Evenᵒ 1 → [] ⊢ᵒ ⊥ᵒ
not-even-one even-one =
  (caseᵒ (unfoldᵒ Evenᵒ 1 even-one)
    (pureᵒE Zᵒ λ{()})
    (unpackᵒ Zᵒ λ m [0=2+m]×[even-m] → pureᵒE (proj₁ᵒ [0=2+m]×[even-m]) λ{()}))
\end{code}

In addition to \textsf{foldᵒ} and \textsf{unfoldᵒ}, one often needs to
use induction when reasoning about recursive defintions. For example,
in plain old Agda, we can prove that \textsf{Even n} implies that $n$
is a multiple of $2$ by defining the recursive function
\textsf{even-mul2}.

\begin{code}
even-mul2 : ∀ n → Even n → ∃[ m ] n ≡ 2 * m
even-mul2 .zero Even-zero = 0 , refl
even-mul2 .(2 + m) (Even-plus-two m even-m)
    with even-mul2 m even-m
... | m′ , refl = suc m′ , sym (*-distribˡ-+ 2 1 m′)
\end{code}

\noindent SIL provides one kind of induction, the \textsf{lobᵒ} rule.
It states that when trying to prove ϕ, it is permissible to assume $▷ᵒ ϕ$.

\begin{code}
_ : ▷ᵒ ϕ ∷ 𝒫 ⊢ᵒ ϕ  →  𝒫 ⊢ᵒ ϕ
_ = lobᵒ
\end{code}

\noindent At first the \textsf{lobᵒ} rule may seem somewhat
mysterious, so let's see its use in an example. Let's prove that
\textsf{Even′ n} implies that $n$ is a multiple of $2$.  When we use
the \textsf{lobᵒ} rule, we must state the property entirely within
SIL, so in the following proof we restate our goal with the definition
of \textsf{aux}.


\begin{code}
even′-mul2 : ∀ n → [] ⊢ᵒ Even′ n → [] ⊢ᵒ (Σ[ m ∈ ℕ ] n ≡ 2 * m)ᵒ
even′-mul2 n even-n = ◇ϕ⇒ϕ n (→ᵒE (∀ᵒE aux n) even-n)
  where
  aux : [] ⊢ᵒ ∀ᵒ[ n ⦂ ℕ ] (μᵒ Evenᵒ n) →ᵒ ◇ᵒ n ((∃[ m ] n ≡ 2 * m)ᵒ)
  aux = lobᵒ (Λᵒ[ n ] λᵒ[ even-n ⦂ μᵒ Evenᵒ n ]
          caseᵒ (unfoldᵒ Evenᵒ n even-n)
          {- Case n = 0 -}
            (pureᵒE Zᵒ λ{ refl → monoᵒ (pureᵒI (0 , refl)) })
          {- Case n = 2 + m and ▷ (Even m) -}
            (unpackᵒ Zᵒ λ m [n=2+m]×[even-m] →
              pureᵒE (proj₁ᵒ [n=2+m]×[even-m]) λ{ refl →
              let IH : _ ⊢ᵒ ▷ᵒ (◇ᵒ m ((∃[ m′ ] m ≡ 2 * m′)ᵒ))
                  IH = →ᵒE (▷→ (∀ᵒE (▷∀ (Sᵒ (Sᵒ (Sᵒ Zᵒ)))) m)) (proj₂ᵒ Zᵒ) in
              ◇→◇{k = m} (▷◇⇒◇▷ m IH) (▷→▷ Zᵒ (pureᵒE Zᵒ λ {(m′ , refl) →
              monoᵒ (pureᵒI ((suc m′) , sym (*-distribˡ-+ 2 1 m′)))}))}))
\end{code}

\subsection{Encoding Mutually Recursive Predicates in SIL}
\label{sec:mutually-recursive}

In our case study in Section~\ref{sec:log-rel}, we define two mutually
recursive predicates 𝒱 and ℰ, so here we introduce how to encode
mutual recursion using a more familiar example. We define the even and
odd numbers in SIL. Here's the equivalent definition in Agda.

\begin{code}
data Evens : ℕ → Set 
data Odds : ℕ → Set

data Evens where
  Evens-zero : Evens zero
  Evens-suc : ∀ m → Odds m → Evens (suc m)
  
data Odds where
  Odds-suc : ∀ m → Evens m → Odds (suc m)
\end{code}

The technique that we use for encoding mutual recursion is to merge
the two predicates into a single predicate whose domain is the sum of
the domains of the two predicates. In this case, the first injection
indicate a request to test if the number is even and the second
injection indicates a request to test if the number is odd.

\begin{code}
Evens⊎Odds : ℕ ⊎ ℕ → Setᵒ ((ℕ ⊎ ℕ) ∷ []) (Later ∷ [])
Evens⊎Odds (inj₁ n) = (n ≡ zero)ᵒ ⊎ᵒ (∃ᵒ[ m ] (n ≡ suc m)ᵒ ×ᵒ ▷ᵒ (inj₂ m ∈ zeroᵒ))
Evens⊎Odds (inj₂ n) = ∃ᵒ[ m ] (n ≡ suc m)ᵒ ×ᵒ ▷ᵒ (inj₁ m ∈ zeroᵒ)
\end{code}

Now that in the first line of \textsf{Evens⊎Odds}, we write
$\mathsf{inj}₂ m ∈ \mathsf{zero}ᵒ$ to test whether $m$ is odd.
In the second line of \textsf{Evens⊎Odds}, we write 
$\mathsf{inj}₁ m ∈ \mathsf{zero}ᵒ$ to test whether $m$ is even.

We apply the μᵒ connective to \textsf{Evens⊎Odds} to define
\textsf{Evens}′ and then \textsf{Odds}′, using \textsf{inj₁ n} for the
argument in \textsf{Evens}′ and using \textsf{inj₂ n} for the argument
in \textsf{Odds}′.

\begin{code}
Evens′ : ℕ → Prop
Evens′ n = [] ⊢ᵒ μᵒ Evens⊎Odds (inj₁ n)

Odds′ : ℕ → Prop
Odds′ n = [] ⊢ᵒ μᵒ Evens⊎Odds (inj₂ n)
\end{code}


