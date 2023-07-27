\begin{comment}
\begin{code}
{-# OPTIONS --without-K #-}
module July2023.SILIntro where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat
   using (ℕ; zero; suc; _≤_; _<_; _+_; _∸_; _*_; z≤n; s≤s; _≤′_; ≤′-step; ≤-pred)
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

postulate excl-mid : ∀ (P : Set) → P ⊎ ¬ P

\end{code}
\end{comment}

\section{Introduction to Step-Indexed Logic for PL Metatheorists}
\label{sec:SIL-intro}

The first thing to know about SIL is that it is a logic that emulates
Agda's logic. For example, the type of a logical formula in Agda is
\textsf{Set} and in SIL it is \textsf{Set}ᵒ. To distinguish SIL from
Agda, we add a superscript ``o'' to most names.

\begin{code}
_ : Set₁
_ = Setᵒ
\end{code}

\noindent The representation, or meaning, of a SIL formula is an Agda
function from a natural number (the step index) to \textsf{Set}. This
representation can be accessed by applying $\#$ to the SIL formula. So
we write $\#\, ϕ\, k$ to mean that formula $ϕ$ is true at time $k$, or
just say ``ϕ at $k$''.

\begin{code}
_ : Setᵒ → ℕ → Set
_ = #
\end{code}

\noindent The purpose of the step indexing in SIL is to support the
definition of recursive predicates using a technique called guarded
recursion, which we discuss in
Section~\ref{sec:intro-recursive-predicates}. The purpose of
Step-Indexed Logic is to hide that step indexing from the PL
metatheorist. So the PL metatheorist generally won't care about SIL's
notion of time and just wants to reason about formulas that are true
or false. This can be recovered by saying that a SIL formula is really
true (it is a tautology) if and only if the formula is true at all
times.

\begin{code}
tautology : Setᵒ → Set
tautology ϕ = ∀ n → # ϕ n
\end{code}

The ``pure'' connective imports (timeless) Agda propositions into SIL.

\begin{code}
_ : Set → Setᵒ
_ = _ᵒ
\end{code}

\noindent For example, we can use the pure connective to express
properties of numbers, such as $1 \plus 1 = 2$. (We recommend ignoring
the Agda proofs in this section as they involve ideas that we have not
yet discussed.)

\begin{code}
_ : tautology ((1 + 1 ≡ 2)ᵒ)
_ = λ {zero → tt ; (suc k) → refl}
\end{code}

\noindent Of course, it is not true that $0 = 1$. 

\begin{code}
_ : ¬ tautology ((0 ≡ 1)ᵒ)
_ = λ taut[0=1] → aux (taut[0=1] 1) 
  where
  aux : 0 ≡ 1  →  ⊥
  aux ()
\end{code}


\subsection{SIL is a propositional logic}

The ``true'' formula in SIL is written ⊤ᵒ

\begin{code}
_ : Setᵒ
_ = ⊤ᵒ
\end{code}

\noindent and of course it's true!

\begin{code}
_ : tautology ⊤ᵒ
_ = λ k → tt
\end{code}

\noindent SIL includes the logical connectives for false, conjunction,
disjunction, and implication.

\begin{code}
_ : Setᵒ
_ = ⊥ᵒ

_ : Setᵒ → Setᵒ → Setᵒ
_ = _×ᵒ_

_ : Setᵒ → Setᵒ → Setᵒ
_ = _⊎ᵒ_

_ : Setᵒ → Setᵒ → Setᵒ
_ = _→ᵒ_
\end{code}

The meanings of these quantifiers match those of the corresponding
ones in Agda. For example, conjunction in SIL is equivalent to
conjunction in Agda.

\begin{code}
_ : tautology (ϕ ×ᵒ ψ) ⇔ tautology ϕ × tautology ψ
_ = (λ taut[ϕ×ψ] → (λ k → proj₁ (taut[ϕ×ψ] k)) , (λ k → proj₂ (taut[ϕ×ψ] k)))
   , (λ {(taut[ϕ] , taut[ψ]) k → (taut[ϕ] k) , (taut[ψ] k)})
\end{code}


\subsection{SIL is a first-order logic}

SIL is a first-order logic, so it includes the universal and
existential quantifiers. SIL uses Agda functions to handle the
quantification.  So the ``for all'' quantifier ∀ᵒ has the following
type.

\begin{code}
_ : (A → Setᵒ) → Setᵒ
_ = ∀ᵒ
\end{code}

\noindent Its meaning is equivalent to Agda′s ∀ quantifier.

\begin{code}
_ : ∀{ϕᵃ : A → Setᵒ} →  tautology (∀ᵒ ϕᵃ) ⇔ (∀ a → tautology (ϕᵃ a))
_ = (λ taut∀ϕ a k → taut∀ϕ k a) , λ ∀a→taut[ϕa] k a → ∀a→taut[ϕa] a k
\end{code}

\noindent As a simple example, the following SIL formula asserts that,
for any $x$, $2x = x \plus x$.

\begin{code}
_ : tautology (∀ᵒ λ x → (2 * x ≡ x + (x + 0))ᵒ)
_ = λ {zero x → tt ; (suc k) x → refl }
\end{code}

\noindent SIL provides alternate notation for universal
quantification, replacing the λ with a pair of brackets around the
bound variable.

\begin{code}
_ : tautology (∀ᵒ[ x ] (2 * x ≡ x + (x + 0))ᵒ)
_ = λ {zero x → tt ; (suc k) x → refl }
\end{code}

For the existential quantifier of SIL, we also use Agda functions for
quantification. However, for technical reasons we require the type $A$
to be inhabited, which we express using an implicit instance argument
to avoid cluttering the uses of ∃ᵒ.

\begin{code}
_ : {{_ : Inhabited A}} → (A → Setᵒ) → Setᵒ
_ = ∃ᵒ
\end{code}

\noindent The following formula shows an example use of the
existential in SIL to state that there exists an $x$ such that
$2x =6$.

\begin{code}
_ : tautology (∃ᵒ[ x ] (2 * x ≡ 6)ᵒ)
_ = λ {zero → zero , tt ; (suc k) → 3 , refl}
\end{code}


\subsection{SIL has User-defined Recursive Predicates}
\label{sec:intro-recursive-predicates}

The central feature of SIL is user-defined recursive predicates, via
the μᵒ operator. To present a familiar example, we start by defining
the even numbers, that is, we wish to define a predicate in SIL
equivalent to the following one in Agda:

\begin{code}
data Even : ℕ → Set where
  Even-zero : Even zero
  Even-plus-two : ∀ m → Even m → Even (2 + m)
\end{code}

To define a recursive predicate in SIL, we typically start by defining
a function from the domain of the predicate to a formula in the type
\textsf{Set}ˢ, which requires some explanation. So we define the
\textsf{Even}′ function from ℕ to \textsf{Set}ˢ.

\begin{code}
Evenˢ : ℕ → Setˢ (ℕ ∷ []) (Later ∷ [])
Evenˢ n = (n ≡ zero)ˢ ⊎ˢ (∃ˢ[ m ] (n ≡ 2 + m)ˢ ×ˢ ▷ˢ (m ∈ zeroˢ))
\end{code}

\noindent We then define \textsf{Even}′ as follows using
\textsf{Even}ˢ, μᵒ, and \textsf{tautology}.

\begin{code}
Even′ : ℕ → Set
Even′ n = tautology (μᵒ Evenˢ n)
\end{code}

\begin{comment}

Sanity check to make sure that the two definitions are equivalent.

\begin{code}
even⇒even′ : ∀ n → Even n → Even′ n
even⇒even′ .zero Even-zero zero = inj₁ tt
even⇒even′ .zero Even-zero (suc k) = inj₁ refl
even⇒even′ .(2 + m) (Even-plus-two m even-n) zero = inj₁ tt
even⇒even′ .(2 + m) (Even-plus-two m even-n) (suc k) = inj₂ (m , (refl , even⇒even′ m even-n k))
\end{code}

\begin{code}
even′⇒even : ∀ n → Even′ n → Even n
even′⇒even n even′-n = induct n n ≤-refl (even′-n n) where
  induct : ∀ n k → n ≤ k → # (μᵒ Evenˢ n) k → Even n
  induct .zero zero z≤n even′-n-k = Even-zero
  induct n (suc k) n≤k even′-n-k
      with even′-n-k
  ... | inj₁ refl = Even-zero
  ... | inj₂ (m , refl , even′-m-k) = Even-plus-two m (induct m k m≤k even′-m-k)
      where m≤k = ≤-trans (n≤1+n m) (≤-pred n≤k)
\end{code}
\end{comment}

\noindent There are a few odd things in the definition of
\textsf{Even}ˢ.  First, the superscripts have changed from "0" to
"s". Second, where one would have expected $m ∈ \mathsf{Even}$,
instead we have $▷ˢ (m ∈ \mathsf{zero}ˢ)$.  The $\mathsf{zero}ˢ$ is a
de Bruijn index for refering to recursively defined predicates. In
general one can nest recursive definitions in SIL, so the de Bruijn
index specifies which one is being used. In this example there is just
one recursive predicate being defined, so its de Bruijn index is
\textsf{zero}ˢ. The first argument of \textsf{Set}ˢ is a list
containing the domain type for each recursive predicate. The domain of
\textsf{Even} is ℕ, so the first argument of \textsf{Set}ˢ is (ℕ ∷ []).

The use of ▷ˢ in $▷ˢ (m ∈ \mathsf{zero}ˢ)$
serves to guard the recursion to ensure that the
recursive definition is well founded. SIL enforces the following rules.  When
SIL sees the use of a recursive predicate, such as $\mathsf{zero}ˢ$,
it clasifyies that the predicate as being used \textsf{Now}.  When the
▷ˢ operator is applied to a subformula, all the predicates that were
used \textsf{Now} inside the subformula are instead considered to be
used \textsf{Later}. Finally, when we apply the μᵒ operator, SIL
checks to make sure that the zero de Bruijn index is used
\textsf{Later}. The second argument of \textsf{Set}ˢ tracks this
\textsf{Now}/\textsf{Later} categorization for each recursive predicate.
For \textsf{Even}ˢ, the second argument is (\textsf{Later} ∷ [])
because the recursive use of the predicate (the $m ∈ \mathsf{zero}ˢ$) is
under the ▷ˢ operator.

Finally, to explain why the superscripts in \textsf{Even}ˢ changed to
"s", one of the reasons is that the "s" connectives build formulas of
type \textsf{Set}ˢ instead of \textsf{Set}ᵒ and the types of those
connectives do the enforcement of the rules described above.
The membership operator $a ∈ x$ assigns $x$ the time \textsf{Now}
and all the other variables in $Γ$ the time \textsf{Later},
which is accomplished by the \textsf{var-now} function.

\begin{code}
_ : A → (x : Γ ∋ A) → Setˢ Γ (var-now Γ x)
_ = _∈_
\end{code}

\noindent The $▷ˢ S$ formula disregards the usage times in subformula $S$
and instead assigns \textsf{Later} to every variable in Γ, using the
\textsf{laters} function.

\begin{code}
_ : Setˢ Γ Δ → Setˢ Γ (laters Γ)
_ = ▷ˢ
\end{code}

The formula $μᵒ Sᵃ$ requires that for any $a ∈ A$, the subformula
$Sᵃ\, a$ used de Bruijn index zero (for this recursive predicate) at
time \textsf{Later}.

\begin{code}
_ : (A → Setˢ (A ∷ []) (Later ∷ [])) → (A → Setᵒ)
_ = μᵒ
\end{code}

\noindent The μᵒ connective is a special case of the μˢ connective,
which can be nested inside the definition of other recursive
predicates.

\begin{code}
_ : (A → Setˢ (A ∷ Γ) (Later ∷ Δ)) → (A → Setˢ Γ Δ)
_ = μˢ
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
Evens⊎Odds : ℕ ⊎ ℕ → Setˢ ((ℕ ⊎ ℕ) ∷ []) (Later ∷ [])
Evens⊎Odds (inj₁ n) = (n ≡ zero)ˢ ⊎ˢ (∃ˢ[ m ] (n ≡ suc m)ˢ ×ˢ ▷ˢ (inj₂ m ∈ zeroˢ))
Evens⊎Odds (inj₂ n) = ∃ˢ[ m ] (n ≡ suc m)ˢ ×ˢ ▷ˢ (inj₁ m ∈ zeroˢ)
\end{code}

Now that in the first line of \textsf{Evens⊎Odds}, we write
$\mathsf{inj}₂ m ∈ \mathsf{zero}ˢ$ to test whether $m$ is odd.
In the second line of \textsf{Evens⊎Odds}, we write 
$\mathsf{inj}₁ m ∈ \mathsf{zero}ˢ$ to test whether $m$ is even.

We apply the μᵒ connective to \textsf{Evens⊎Odds} to define
\textsf{Evens}′ and then \textsf{Odds}′, using \textsf{inj₁ n} for the
argument in \textsf{Evens}′ and using \textsf{inj₂ n} for the argument
in \textsf{Odds}′.

\begin{code}
Evens′ : ℕ → Set
Evens′ n = tautology (μᵒ Evens⊎Odds (inj₁ n))

Odds′ : ℕ → Set
Odds′ n = tautology (μᵒ Evens⊎Odds (inj₂ n))
\end{code}


\subsection{The Proof Language of SIL}
\label{sec:proof-rules}

The proofs in the prior section were written in raw Agda, relying on
the definitions of the SIL connectives and explicitly reasoning about
the step indices. Sometimes that is an expedient route to take and the
Reference Section~\ref{sec:SIL-reference} lists the defining equation
for each of SIL connective. However, the goal of SIL is to hide the
step-indexing, so SIL provides proof rules for its logical connectives
and this section shows how to use them.

We write $𝒫 ⊢ᵒ ϕ$ for entailment, which means that ϕ is true when
the list of formulas in 𝒫 are true.

\begin{code}
_ : List Setᵒ → Setᵒ → Set
_ = _⊢ᵒ_
\end{code}

\noindent When $𝒫$ is the empty list, entailment is the same as the
\textsf{tautology} function we defined above.

We discuss the proof rules in the same order as the discussion of
SIL formulas in the beginning of this Section~\ref{sec:SIL-intro}.
The following are the introduction and elimination rules for
the pure connective. So given a proof of an Agda formula $p$,
\textsf{(pureᵒI p)} produces a proof of $pᵒ$.

\begin{code}
_ : ∀{p : Set} → p → 𝒫 ⊢ᵒ p ᵒ
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




For example, we can change our previous definition of the even
numbers, \textsf{Even}′, to instead use entailment.

\begin{code}
Even″ : ℕ → Set
Even″ n = [] ⊢ᵒ (μᵒ Evenˢ n)
\end{code}

\begin{code}
_ : [] ⊢ᵒ μᵒ Evenˢ 0
_ = foldᵒ Evenˢ 0 (inj₁ᵒ (pureᵒI refl))
\end{code}
