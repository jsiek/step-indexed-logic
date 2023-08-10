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
   using (≤-refl; ≤-antisym; ≤-trans; ≤-step; ≤⇒≤′; ≤′⇒≤; n≤1+n; <⇒≤; s≤′s; 0≢1+n; *-distribˡ-+)
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
variable ϕ ϕ′ ψ ψ′ þ : Setᵒ [] []
\end{code}

\begin{comment}
\noindent The representation, or meaning, of a SIL formula is an Agda
function from a natural number (the step index) to \textsf{Set}. This
representation can be accessed by applying $\#$ to the SIL formula. So
we write $\#\, ϕ\, k$ to mean that formula $ϕ$ is true at time $k$, or
just say ``ϕ at $k$''.

\begin{code}
--_ : Setᵒ → ℕ → Prop
--_ = #
\end{code}

\noindent The purpose of the step indexing in SIL is to support the
definition of recursive predicates using a technique called guarded
recursion, which we discuss in
Section~\ref{sec:intro-recursive-predicates}. The purpose of
Step-Indexed Logic is to hide that step indexing from the PL
metatheorist. So the PL metatheorist generally won't care about SIL's
notion of time and just wants to reason about formulas that are true
or false. This can be recovered by saying that a SIL formula ϕ is
really true, written [] ⊢ᵒ ϕ, if and only if the formula is true at
all times. (We recommend ignoring the Agda proofs in this section as
they involve ideas that we have not yet discussed.)

\begin{code}
--_ : ([] ⊢ᵒ ϕ)  ⇔  (∀ n → # ϕ n)
--_ = (λ ⊢ϕ k → ⊢ᵒE ⊢ϕ k tt) , λ ∀nϕn → ⊢ᵒI λ n _ → ∀nϕn n
\end{code}

\noindent We discuss the entailment relation ⊢ᵒ in more detail in
Section~\ref{sec:proof-rules}.
\end{comment}

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
predicates in scope (usually just one). We refer to such as list as a
\textsf{Context}.  Let Γ range over contexts.

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
$p$, \textsf{(pureᵒI p)} produces a proof of $𝒫 ⊢ᵒ p ᵒ$.

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

If instead you have a proof of $pᵒ$ and have some goal þ to prove,
then you can assume that $p$ is true while proving þ.  That is,
$(pureᵒE ϕ F)$ is a proof of þ if ϕ is a proof of pᵒ and $F$ is a
function from $p$ to a proof of þ.

\begin{code}
_ : 𝒫 ⊢ᵒ p ᵒ  →  (p → 𝒫 ⊢ᵒ þ)  →  𝒫 ⊢ᵒ þ
_ = pureᵒE
\end{code}

\noindent For example, we can prove that $(x ≡ y)ᵒ$
implies $(y ≡ x)ᵒ$ using \textsf{pureᵒE} as follows.

\begin{code}
_ : ∀(x y : ℕ) → [] ⊢ᵒ (x ≡ y) ᵒ → [] ⊢ᵒ (y ≡ x)ᵒ
_ = λ x y x=yᵒ → pureᵒE x=yᵒ λ {refl → pureᵒI refl}
\end{code}

For the propositional connectives, many of the SIL proof rules are the
same as the Agda proof rules, but with a superscript ``o''.  For
example, in Agda the introduction rule for ⊤ is \textsf{tt} so in SIL
it is \textsf{tt}ᵒ.

\begin{code}
_ : 𝒫 ⊢ᵒ ⊤ᵒ 
_ = ttᵒ
\end{code}

\noindent For conjunction, the introduction rule is the comma
and elimination is \textsf{proj₁ᵒ} and \textsf{proj₂ᵒ}.

\begin{code}
_ : 𝒫 ⊢ᵒ ϕ → 𝒫 ⊢ᵒ ψ → 𝒫 ⊢ᵒ ϕ ×ᵒ ψ
_ = _,ᵒ_

_ : 𝒫 ⊢ᵒ ϕ ×ᵒ ψ  →  𝒫 ⊢ᵒ ϕ
_ = proj₁ᵒ

_ : 𝒫 ⊢ᵒ ϕ ×ᵒ ψ  →  𝒫 ⊢ᵒ ψ
_ = proj₂ᵒ
\end{code}

\noindent For disjunction, the introduction rules are \textsf{inj₁ᵒ} and
\textsf{inj₂ᵒ}.

\begin{code}
_ : 𝒫 ⊢ᵒ ϕ → 𝒫 ⊢ᵒ ϕ ⊎ᵒ ψ
_ = inj₁ᵒ

_ : 𝒫 ⊢ᵒ ψ → 𝒫 ⊢ᵒ ϕ ⊎ᵒ ψ
_ = inj₂ᵒ
\end{code}

\noindent Agda uses its builtin pattern-matching to eliminate
disjunction. So for SIL, we instead define the following \textsf{case}
rule. If you have a proof of $ϕ ⊎ᵒ ψ$ and would like to prove þ, then
it suffices to prove two cases: 1) assuming ϕ show þ and 2)
assuming ψ show þ.

\begin{code}
_ : 𝒫 ⊢ᵒ ϕ ⊎ᵒ ψ  →  ϕ ∷ 𝒫 ⊢ᵒ þ  →  ψ ∷ 𝒫 ⊢ᵒ þ  →  𝒫 ⊢ᵒ þ
_ = caseᵒ
\end{code}

Implication is introduced by λᵒ.

\begin{code}
_ : ∀ ϕ → (ϕ ∷ 𝒫 ⊢ᵒ ϕ → ϕ ∷ 𝒫 ⊢ᵒ ψ) → 𝒫 ⊢ᵒ ϕ →ᵒ ψ
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

\noindent Implication is eliminated by →ᵒE
\begin{code}
_ : 𝒫 ⊢ᵒ ϕ →ᵒ ψ  →  𝒫 ⊢ᵒ ϕ  →  𝒫 ⊢ᵒ ψ
_ = →ᵒE
\end{code}

Moving on to the proof rules for universal and existential quantifiers.
The universal quantifier is introduced by Λᵒ.

\begin{code}
_ : {ϕᵃ : A → Setᵒ [] []} → (∀ a → 𝒫 ⊢ᵒ ϕᵃ a)  →  𝒫 ⊢ᵒ ∀ᵒ ϕᵃ
_ = Λᵒ
\end{code}

\noindent SIL also provides a bracket notation for Λᵒ. For example,
the following is a proof that for any natural $x$, $x = x$.

\begin{code}
∀x,x=x : [] ⊢ᵒ ∀ᵒ[ x ⦂ ℕ ] (x ≡ x)ᵒ
∀x,x=x = Λᵒ[ x ] pureᵒI refl
\end{code}

\noindent The universal quantifier is eliminated by ∀ᵒE.

\begin{code}
_ : ∀{ϕᵃ : A → Setᵒ [] []} → 𝒫 ⊢ᵒ ∀ᵒ ϕᵃ  →  (a : A)  →  𝒫 ⊢ᵒ ϕᵃ a
_ = ∀ᵒE
\end{code}

\noindent For example, the following proves that $1 = 1$ using the
above fact that we proved about naturals. 

\begin{code}
_ : [] ⊢ᵒ (1 ≡ 1)ᵒ
_ = ∀ᵒE{ϕᵃ = λ x → (x ≡ x)ᵒ} ∀x,x=x 1
\end{code}

The existential quantifier of SIL is introduced by the rule ∃ᵒI and
eliminated by the rule unpackᵒ.

\begin{code}
_ : ∀{ϕᵃ : A → Setᵒ [] []}{{_ : Inhabited A}} →  (a : A)  →  𝒫 ⊢ᵒ ϕᵃ a  →  𝒫 ⊢ᵒ ∃ᵒ ϕᵃ
_ = ∃ᵒI

_ : ∀{ϕᵃ : A → Setᵒ [] []}{þ : Setᵒ [] []}{{_ : Inhabited A}}
     → 𝒫 ⊢ᵒ ∃ᵒ ϕᵃ  →  (∀ a  →  ϕᵃ a ∷ 𝒫 ⊢ᵒ ϕᵃ a  →  ϕᵃ a ∷ 𝒫 ⊢ᵒ þ)  →  𝒫 ⊢ᵒ þ
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

Finally, regarding recursive predicates, the introduction rule is
\textsf{fold}ᵒ. The rule uses a new operator named \textsf{let}ᵒ that
we discuss below.

\begin{code}
_ : ∀{𝒫} (Sᵃ : A → Setᵒ (A ∷ []) (Later ∷ [])) (a : A) →  𝒫 ⊢ᵒ letᵒ (μᵒ Sᵃ) (Sᵃ a)  →  𝒫 ⊢ᵒ μᵒ Sᵃ a
_ = foldᵒ
\end{code}


\begin{code}
Evenᵒ : ℕ → Setᵒ (ℕ ∷ []) (Later ∷ [])
Evenᵒ n = (n ≡ zero)ᵒ ⊎ᵒ (∃ᵒ[ m ] (n ≡ 2 + m)ᵒ ×ᵒ ▷ᵒ (m ∈ recᵒ))
\end{code}

The following two proofs use \textsf{fold}ᵒ to show that zero is
even. The first proof is short but Agda's powerful notion of equality
is doing a lot of work behind the scenes.

\begin{code}
even-zero : [] ⊢ᵒ Even′ 0
even-zero = foldᵒ Evenᵒ 0 (inj₁ᵒ (pureᵒI refl))
\end{code}

\noindent To better see what's going on, let's take it slower. The
proof starts with the use of the \textsf{fold}ᵒ rule, after which it
remains to prove
\[
   \text{even-0 : letᵒ (μᵒ Evenᵒ) (Evenᵒ 0)}
\]
This \textsf{let}ᵒ operator substitutes the predicate \textsf{(μᵒ Evenᵒ)} for the
\textsf{zero}ᵒ de Bruijn index inside \textsf{Even}ᵒ. Recall the definition
of \textsf{Even}ᵒ:
\[
  \text{Evenᵒ n = (n ≡ zero)ᵒ ⊎ᵒ (∃ᵒ[ m ] (n ≡ 2 + m)ᵒ ×ᵒ ▷ᵒ (m ∈ zeroᵒ))}
\]
So \textsf{even-0} above is equivalent to the following, where
\textsf{m ∈ zeroᵒ} has been replaced by \textsf{μᵒ Evenᵒ m}.
\[
  \text{(0 ≡ zero)ᵒ ⊎ᵒ (∃ᵒ[ m ] (0 ≡ 2 + m)ᵒ ×ᵒ ▷ᵒ (μᵒ Evenᵒ m))}
\]
Finally, we conclude the proof by choosing the first branch of the disjunction
with \textsf{inj₁ᵒ} and then proving \textsf{(0 ≡ zero)ᵒ} by \textsf{pureᵒI refl}.

\begin{code}
_ : [] ⊢ᵒ Even′ 0
_ = foldᵒ Evenᵒ 0 even-0
 where
 even-0 : [] ⊢ᵒ letᵒ (μᵒ Evenᵒ) (Evenᵒ 0)
 even-0 = substᵒ (≡ᵒ-sym (≡ᵒ-refl let-eq)) even-body-0
  where
  let-eq : letᵒ (μᵒ Evenᵒ) (Evenᵒ 0)  ≡  (0 ≡ zero)ᵒ ⊎ᵒ (∃ᵒ[ m ] (0 ≡ 2 + m)ᵒ ×ᵒ ▷ᵒ (μᵒ Evenᵒ m))
  let-eq = refl
  even-body-0 : [] ⊢ᵒ (0 ≡ zero)ᵒ ⊎ᵒ (∃ᵒ[ m ] (0 ≡ 2 + m)ᵒ ×ᵒ ▷ᵒ (μᵒ Evenᵒ m))
  even-body-0 = inj₁ᵒ (pureᵒI refl)
\end{code}

TODO: keep this or delete?
\begin{code}
even-two : [] ⊢ᵒ μᵒ Evenᵒ 2
even-two = foldᵒ Evenᵒ 2 (inj₂ᵒ (∃ᵒI 0 (pureᵒI refl ,ᵒ monoᵒ even-zero)))
\end{code}

The eleminiation rule for μᵒ is \textsf{unfold}ᵒ.

\begin{code}
_ : ∀{𝒫} (Sᵃ : A → Setᵒ (A ∷ []) (Later ∷ [])) (a : A) →  𝒫 ⊢ᵒ μᵒ Sᵃ a  →  𝒫 ⊢ᵒ letᵒ (μᵒ Sᵃ) (Sᵃ a)
_ = unfoldᵒ
\end{code}

\noindent For example, if we unfold $μᵒ Evenᵒ 1$, we obtain that either
$1 = 0$ or $1 = 2 + m$ for some $m$. Either case is impossible, so it must
be that $1$ is not even.

\begin{code}
{-
not-even-one : ¬ ([] ⊢ᵒ μᵒ Evenᵒ 1)
not-even-one even-one = ⊥ᵒ⇒⊥ (caseᵒ (unfoldᵒ Evenᵒ 1 even-one)
                               (pureᵒE Zᵒ λ{()})
                               (unpackᵒ Zᵒ λ m [0=2+m]×[even-m] → pureᵒE (proj₁ᵒ [0=2+m]×[even-m]) λ{()}))
-}
\end{code}



\begin{code}
even-div2 : ∀ n → Even n → ∃[ m ] n ≡ 2 * m
even-div2 .zero Even-zero = 0 , refl
even-div2 .(2 + m) (Even-plus-two m even-m)
    with even-div2 m even-m
... | m′ , refl = suc m′ , sym (*-distribˡ-+ 2 1 m′)
\end{code}

\begin{code}
even′-div2-proof : [] ⊢ᵒ ∀ᵒ[ n ⦂ ℕ ] (μᵒ Evenᵒ n) →ᵒ ◇ᵒ n ((∃[ m ] n ≡ 2 * m)ᵒ)
even′-div2-proof =
  lobᵒ (Λᵒ[ n ] λᵒ[ even-n ⦂ μᵒ Evenᵒ n ]
        caseᵒ (unfoldᵒ Evenᵒ n even-n)
          {- Case n = 0 -}
          (pureᵒE Zᵒ λ{ refl → monoᵒ (pureᵒI (0 , refl)) })
          {- Case n = 2 + m and ▷ (Even m) -}
          (unpackᵒ Zᵒ λ m [n=2+m]×[even-m] →
            pureᵒE (proj₁ᵒ [n=2+m]×[even-m]) λ{ refl →
            let IH : _ ⊢ᵒ ◇ᵒ m (▷ᵒ ((∃[ m′ ] m ≡ 2 * m′)ᵒ))
                IH = ▷◇⇒◇▷ m (→ᵒE (▷→ (∀ᵒE (▷∀ (Sᵒ (Sᵒ (Sᵒ Zᵒ)))) m)) (proj₂ᵒ Zᵒ)) in
            ◇→◇{k = m} IH (▷→▷ Zᵒ (pureᵒE Zᵒ λ {(m′ , refl) →
            monoᵒ (pureᵒI ((suc m′) , sym (*-distribˡ-+ 2 1 m′)))}))}))
            
even′-div2 : ∀ n → [] ⊢ᵒ Even′ n → ⌊ Σ[ m ∈ ℕ ] n ≡ 2 * m ⌋
even′-div2 n even-n = pureᵒE[] (◇ϕ⇒ϕ n (→ᵒE (∀ᵒE even′-div2-proof n) even-n))
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


