\begin{comment}
\begin{code}
{-# OPTIONS --rewriting #-}

module July2023.STLC where

open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Nat.Induction
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List using (map)
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
--open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Induction using (RecStruct)
open import Induction.WellFounded as WF
open import Data.Product.Relation.Binary.Lex.Strict
  using (×-Lex; ×-wellFounded; ×-preorder)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; cong₂; subst; trans)
--open Eq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Sig
open import Var
open import July2023.StepIndexedLogic
open import EquivalenceRelation public

\end{code}
\end{comment}

\section{Case Study: Type Safety of the STLC with Recursive Functions}
\label{sec:STLC}

We provide an example application of our Step-Indexed Logic with a
case study in proving semantic type safety for the STLC with recursive
functions. We choose to extend STLC with recursive functions because
otherwise, one does not need step-indexed logical relations; logical
relations that are only indexed by types are sufficient.  The next few
subsections give the definition of this variant of the STLC (syntax in
§\ref{sec:STLC-syntax}, reduction semantics in
§\ref{sec:STLC-reduction}, type system in
§\ref{sec:STLC-type-system}). We then define the step-indexed logical
relation in Section~\ref{sec:log-rel} and use it to define semantic
type safety in Section~\ref{sec:sem-type-safety}. The rest of the
subsections give the proof of semantic type safety, starting
with the Bind Lemma (§\ref{sec:bind-lemma}), then the many
Compatibility Lemmas (§\ref{sec:compatibility-lemmas}) that
lead up to the Fundamental Lemma (§\ref{sec:fundamental}).
We conclude with the proof of semantic type safety
in Section~\ref{sec:proof-sem-safety}.

\subsection{Syntax of STLC with Recursive Functions}
\label{sec:STLC-syntax}

This variant of the STLC includes the type of natural numbers and
function types.

\begin{code}
data Type : Set where
  `ℕ  : Type
  _⇒_ : Type → Type → Type
\end{code}

Our definition of STLC terms is isomorphic to the following data type.

\begin{code}
module AsIf where
  data Term : Set where
    `_ : Var → Term
    ƛ : Term → Term
    _·_ : Term → Term → Term
    `zero : Term
    `suc : Term → Term
    case : Term → Term → Term → Term
    μ : Term → Term
\end{code}

\noindent Instead of using the above data type, we instead use
Abstract Binding Tree (ABT) library~\citep{Siek:2021to} to define the
syntax of terms. The reason is that the proof of semantic type safety
relies on a lemma regarding substitution whose proof is quite involved
but standard.  We can obtain this substitution lemma for free if we
use the ABT library.

The ABT library is parameterized by a type \textsf{Op} that specifies
the constructors and a function \textsf{sig} that describes the arity
and binding structure of each term constructor. For this variant of
the STLC, the terms include lambda abstraction, application, the zero
numeral, the successor operation, case analysis on natural numbers,
and a recursive fixpoint operator. The ABT library automatically
includes a constructor for variables (de Bruijn indices), so we do not
need to include them in \textsf{Op}.

\begin{code}
data Op : Set where
  op-lam : Op
  op-app : Op
  op-zero : Op
  op-suc : Op
  op-case : Op
  op-rec : Op
\end{code}

Next we define the \textsf{sig} function for this variant of the STLC.
For each \textsf{Op}, it returns a list of \textsf{Sig}, which
specifies the number of variable bindings that are introduced for each
subterm. The ■ means zero bindings and ν means add one binding.  So we
see below that lambda abstraction has one subterm with one variable
binding. The \textsf{case} operator has three subterms with one
variable binding for the third subterm.

\begin{code}
sig : Op → List Sig
sig op-lam = (ν ■) ∷ []
sig op-app = ■ ∷ ■ ∷ []
sig op-zero = []
sig op-suc = ■ ∷ []
sig op-case = ■ ∷ ■ ∷ (ν ■) ∷ []
sig op-rec = (ν ■) ∷ []
\end{code}

\noindent We import the ABT library to obtain the definition of terms,
whose type we name \textsf{Term}, the definition of substitution,
and lemmas about substitution.

\begin{code}
open import rewriting.AbstractBindingTree Op sig renaming (ABT to Term) public
\end{code}

\noindent The following metavariables range over \textsf{Term}.

\begin{code}
variable L L′ M M′ N N′ V V′ W W′ : Term
\end{code}

The notation for constructing terms from the ABT library is rather
verbose, so we define the following shorthand notations use Agda's
\textsf{pattern} facility.

\begin{code}
pattern ƛ N  = op-lam ⦅ cons (bind (ast N)) nil ⦆

infixl 7  _·_
pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆

pattern `zero = op-zero ⦅ nil ⦆
pattern `suc M = op-suc ⦅ cons (ast M) nil ⦆

pattern case L M N = op-case ⦅ cons (ast L) (cons (ast M) (cons (bind (ast N)) nil)) ⦆

pattern μ N = op-rec ⦅ cons (bind (ast N)) nil ⦆
\end{code}

The ABT library defines a bracket notation for substitution. For example, the
follow substitution replaces the de Bruijn index zero with the term $N$.
\begin{code}
_ : (` 0) [ N ] ≡ N
_ = refl
\end{code}

\noindent When substitution is applied to a non-zero variable, its de
Bruijn index is decreased by one. The reason for this is that one
typically performs substitution when removing a variable binding, as
we shall see in the β-ƛ reduction rule in the next section.

\begin{code}
_ = example where
  example : ∀ N → (` 1) [ N ] ≡ ` 0
  example N rewrite sub-var (N • id) 1 = refl
\end{code}

The ABT library also defines parallel substitution, which takes a function σ from natural
numbers to terms, and applies it to a term $M$ by replacing all the free variables in $M$
according to σ, written $⟪ σ ⟫ M$. We refer to a function from natural numbers to terms
as a \emph{substitution}. The identity substitution is named \textsf{id}.

\begin{code}
_ : ⟪ id ⟫ (` 0) ≡ ` 0
_ = refl
\end{code}

\noindent The ABT library defines a cons-like operator on substitutions, written $M • σ$,
that maps $0$ to $M$ and an other $x$ to $σ\, (x \minus 1)$. Here are a few example
that demonstrate the application of the substitution $M • N • \mathsf{id}$ to several different
variables.

\begin{code}
_ : ∀{M N} → ⟪ M • N • id ⟫ (` 0) ≡ M
_ = refl

_ = example where
  example : ∀ M N → ⟪ M • N • id ⟫ (` 1) ≡ N
  example M N rewrite sub-var (M • N • id) 1 = refl

_ = example where
  example : ∀ M N → ⟪ M • N • id ⟫ (` 2) ≡ ` 0
  example M N rewrite sub-var (M • N • id) 2 = refl
\end{code}

\noindent The ↑ operator increments the de Bruijn indices.

\begin{code}
_ = example where
  example : ⟪ ↑ ⟫ (` 0) ≡ ` 1
  example rewrite sub-var ↑ 0 | ren-def suc 0 = refl
\end{code}

\noindent The sequencing operator (σ ⨟ τ) creates a substitution that is equivalent
to applying σ and then τ.

\begin{code}
_ : ∀ σ τ M → ⟪ σ ⨟ τ ⟫ M ≡ ⟪ τ ⟫ (⟪ σ ⟫ M)
_ = λ σ τ M → refl
\end{code}

\noindent The \textsf{ext} operator transports a substitution
underneath one variable binder. For example, applying the substitution
σ to a lambda abstraction pushes through to apply $\mathsf{ext}\,σ$ to
its body.

\begin{code}
_ : ∀ σ N → ⟪ σ ⟫ (ƛ N) ≡ ƛ (⟪ ext σ ⟫ N)
_ = λ σ N → refl
\end{code}

\noindent The \textsf{ext} operator is equivalent to 

\begin{code}
_ : ∀ σ → ext σ ≡ ` 0 • (σ ⨟ ↑)
_ = λ σ → refl
\end{code}

\noindent The following is the substitution lemma that we shall need
from the ABT library.

\begin{code}
_ : ∀ σ N V → (⟪ ext σ ⟫ N) [ V ] ≡ ⟪ V • σ ⟫ N
_ = λ σ N V → exts-sub-cons {σ}{N}{V}
\end{code}


\subsection{Dynamic Semantics of STLC}
\label{sec:STLC-reduction}

The standard reduction semantics for the STLC with recursive functions~\citep{Pierce:2002hj}
includes the following reduction rule for the fixpoint operator.
\[
  μx.M \longrightarrow M[x ↦ μx.M]
\]
This rule involves the substitution of an arbitrary term (not a
value). Unfortunately, the usual formulation of logical relations for
call-by-value languages requires that substitutions map variables to
values. We therefore use an alternative reduction semantics in which
$μx.V$ is categorized as a value and replace the above reduction
rule with the following one.
\[
(μx.V) \app W \longrightarrow V[x ↦ μx.V] \app W
\]
To that end, we begin with the following definition of the
\textsf{Value} predicate.

\begin{code}
data Value : Term → Set where
  V-ƛ : Value (ƛ N)
  V-zero : Value `zero
  V-suc : Value V → Value (`suc V)
  V-μ : Value V → Value (μ V)
\end{code}

\noindent The \textsf{value} function extracts the term from
a proof that the term is a value.

\begin{code}
value : Value V → Term
value {V} v = V
\end{code}

\noindent The following lemma is the inversion principle for a
fixpoint value.

\begin{code}
Value-μ-inv : Value (μ V) → Value V
Value-μ-inv (V-μ v) = v
\end{code}

The result of applying a sustitution to a value is also a value.

\begin{code}
subst-preserves-value : ∀ σ V → Value V → Value (⟪ σ ⟫ V)
subst-preserves-value σ .(ƛ _) V-ƛ = V-ƛ
subst-preserves-value σ .`zero V-zero = V-zero
subst-preserves-value σ (`suc V) (V-suc v) = V-suc (subst-preserves-value σ V v)
subst-preserves-value σ (μ V) (V-μ v) = V-μ (subst-preserves-value (ext σ) V v)
\end{code}

Our reduction semantics will employ frames, a kind of shallow evaluation context,
which we define as follows.

\begin{code}
infix  6 □·_
infix  6 _·□

data Frame : Set where
  □·_ : Term → Frame
  _·□ : Value V → Frame
  suc□ : Frame
  case□ : Term → Term → Frame
\end{code}

\noindent The notation $F ⟦ N ⟧$ is for plugging the term $N$ into
the frame $F$.

\begin{code}
_⟦_⟧ : Frame → Term → Term
(□· M) ⟦ L ⟧        =  L · M
(v ·□) ⟦ M ⟧        =  value v · M
suc□ ⟦ M ⟧          = `suc M
(case□ M N) ⟦ L ⟧   = case L M N
\end{code}

The reduction relation for this STLC are defined as follows.  

\begin{code}
infix 2 _—→_
data _—→_ : Term → Term → Set where
  β-ƛ : Value W → (ƛ N) · W —→ N [ W ]
  β-zero : case `zero M N —→ M
  β-suc : Value V → case (`suc V) M N —→ N [ V ]
  β-μ : Value V → Value W → (μ V) · W —→ V [ μ V ] · W
  ξξ : (F : Frame) →  M′ ≡ F ⟦ M ⟧  →  N′ ≡ F ⟦ N ⟧  →  M —→ N  →  M′ —→ N′
\end{code}

\noindent The ξξ rule will most often be used with \textsf{refl} as
arguments for the second and third premise, so we define the following
shorthand.

\begin{code}
pattern ξ F M—→N = ξξ F refl refl M—→N
\end{code}

We define \textsf{reducible} in the standard way.

\begin{code}
reducible : (M : Term) → Set
reducible M = ∃[ N ] (M —→ N)
\end{code}

\noindent Values are not reducible.

\begin{code}
value-irreducible : ∀ {V M : Term} → Value V → ¬ (V —→ M)
value-irreducible V-ƛ (ξξ (□· x₂) () x₁ V—→M)
value-irreducible V-ƛ (ξξ (x₂ ·□) () x₁ V—→M)
value-irreducible V-ƛ (ξξ suc□ () x₁ V—→M)
value-irreducible V-zero (ξξ (□· x₂) () x₁ V—→M)
value-irreducible V-zero (ξξ (x₂ ·□) () x₁ V—→M)
value-irreducible V-zero (ξξ suc□ () x₁ V—→M)
value-irreducible (V-suc v) (ξ suc□ V—→M) = value-irreducible v V—→M
value-irreducible (V-μ v) (ξξ (□· x₂) () x₁ V—→M)
value-irreducible (V-μ v) (ξξ (x₂ ·□) () x₁ V—→M)
value-irreducible (V-μ v) (ξξ suc□ () x₁ V—→M)
\end{code}

We need the following inversion principle for the reduction of a
fixpoint applied to an argument.

\begin{code}
β-μ-inv : ∀{V W N} → Value V → Value W → μ V · W —→ N  →  N ≡ V [ μ V ] · W
β-μ-inv v w (ξ (□· x₂) r) = ⊥-elim (value-irreducible (V-μ v) r)
β-μ-inv v w (ξξ (x₂ ·□) refl x₁ r) = ⊥-elim (value-irreducible w r)
β-μ-inv v w (β-μ x x₁) = refl
\end{code}

We define the reflexive and transitive closure of reduction as follows.

\begin{code}
infix  2 _—↠_
infixr 2 _—→⟨_⟩_
infix  3 _END

data _—↠_ : Term → Term → Set where
  _END : (M : Term) → M —↠ M
  _—→⟨_⟩_ : (L : Term) {M N : Term} → L —→ M  →  M —↠ N  →  L —↠ N
\end{code}

\noindent The length of a reduction sequence is computed by the \textsf{len} function.

\begin{code}
len : ∀{M N : Term} → (M→N : M —↠ N) → ℕ
len (_ END) = 0
len (_ —→⟨ _ ⟩ red) = suc (len red)
\end{code}


\subsection{Type System of STLC}
\label{sec:STLC-type-system}

The type system for this STLC is comprised of two mutually recursive
judgments, one for values and one for terms.

\begin{code}
infix 3 _⊢ⱽ_⦂_
data _⊢ⱽ_⦂_ : List Type → Term → Type → Set

infix 3 _⊢_⦂_
data _⊢_⦂_ : List Type → Term → Type → Set
\end{code}

\noindent We define the well-typed values as follows. Note that we
restrict the fixpoint operator to only be applicable to functions.

\begin{code}
data _⊢ⱽ_⦂_ where
  ⊢ⱽzero : ∀ {Γ} → Γ ⊢ⱽ `zero ⦂ `ℕ
  ⊢ⱽsuc : ∀ {Γ V} → Γ ⊢ⱽ V ⦂ `ℕ  →  Γ ⊢ⱽ `suc V ⦂ `ℕ
  ⊢ⱽƛ : ∀ {Γ N A B} → (A ∷ Γ) ⊢ N ⦂ B  →  Γ ⊢ⱽ ƛ N ⦂ (A ⇒ B)
  ⊢ⱽμ : ∀ {Γ V A B} → (A ⇒ B ∷ Γ) ⊢ⱽ V ⦂ A ⇒ B  →  Γ ⊢ⱽ μ V ⦂ A ⇒ B
\end{code}

\noindent The well-typed values are of course a subset of the values.

\begin{code}
⊢ⱽ⇒Value : ∀{Γ V A} → Γ ⊢ⱽ V ⦂ A → Value V
⊢ⱽ⇒Value ⊢ⱽzero = V-zero
⊢ⱽ⇒Value (⊢ⱽsuc ⊢V) = V-suc (⊢ⱽ⇒Value ⊢V)
⊢ⱽ⇒Value (⊢ⱽƛ ⊢N) = V-ƛ
⊢ⱽ⇒Value (⊢ⱽμ ⊢V) = V-μ (⊢ⱽ⇒Value ⊢V)
\end{code}

The type system for terms is define below. The notation $Γ ∋ x ⦂ A$ is defined
in the ABT library and simply means that $A$ is the type at position $x$ of Γ.
The rule ${⊢}{\mathsf{val}}$ turns a well-typed value into a well-typed term.
The other typing rules are standard.

\begin{code}
data _⊢_⦂_ where
  ⊢` : ∀ {Γ x A} → Γ ∋ x ⦂ A  →  Γ ⊢ ` x ⦂ A
  ⊢suc : ∀ {Γ M} → Γ ⊢ M ⦂ `ℕ  →  Γ ⊢ `suc M ⦂ `ℕ
  ⊢case : ∀{Γ L M N A} → Γ ⊢ L ⦂ `ℕ  →  Γ ⊢ M ⦂ A  →  `ℕ ∷ Γ ⊢ N ⦂ A  →  Γ ⊢ case L M N ⦂ A
  ⊢· : ∀ {Γ L M A B} → Γ ⊢ L ⦂ (A ⇒ B)  →  Γ ⊢ M ⦂ A  →  Γ ⊢ L · M ⦂ B
  ⊢val : ∀ {Γ V A} → Γ ⊢ⱽ V ⦂ A  →  Γ ⊢ V ⦂ A
\end{code}


\subsection{Definition of the Logical Relation}
\label{sec:log-rel}

The logical relation is comprised of two mutually recursive
predicates, 𝒱 for values and ℰ for terms. The intuitive meaning
of the predicates is that, for a given type $A$, 
$𝒱⟦ A ⟧\, V$ means that value $V$ is well behaved according to type $A$
and $ℰ⟦ A ⟧\, M$ means that $M$ is well behaved according to type $A$.

SIL does not directly support mutual recursion, but we can merge the
two predicates into one predicate named 𝒱⊎ℰ, using a sum type.  We
define 𝒱⊎ℰ by an application of μᵒ, so we first need to define the
non-recursive version of 𝒱⊎ℰ, which we call \textsf{pre}-𝒱⊎ℰ, defined
below. It simply dispatches to the non-recursive \textsf{pre}-ℰ and
\textsf{pre}-ℰ which we will get to shortly.

\begin{code}
Γ₁ : Context
Γ₁ = ((Type × Term) ⊎ (Type × Term)) ∷ []

pre-ℰ : Type → Term → Setˢ Γ₁ (Later ∷ [])
pre-𝒱 : Type → Term → Setˢ Γ₁ (Later ∷ [])

pre-𝒱⊎ℰ : ((Type × Term) ⊎ (Type × Term)) → Setˢ Γ₁ (Later ∷ [])
pre-𝒱⊎ℰ (inj₁ (A , V)) = pre-𝒱 A V
pre-𝒱⊎ℰ (inj₂ (A , M)) = pre-ℰ A M

𝒱⊎ℰ : ((Type × Term) ⊎ (Type × Term)) → Setᵒ
𝒱⊎ℰ X = μᵒ pre-𝒱⊎ℰ X

𝒱⟦_⟧ : Type → Term → Setᵒ
𝒱⟦ A ⟧ V = 𝒱⊎ℰ (inj₁ (A , V))

ℰ⟦_⟧ : Type → Term → Setᵒ
ℰ⟦ A ⟧ M = 𝒱⊎ℰ (inj₂ (A , M))
\end{code}

When we use 𝒱 and ℰ recursively in their definition, we do so by using
the membership operator of SIL with a de Bruijn index to select
which recursive predicate we wish to refer to. In this case, there is
only one recursive predicate in scope and its de Bruijn index is zero.
We define the following shorthand notation for refering to 𝒱 and ℰ.

\begin{code}
𝒱ˢ⟦_⟧ : Type → Term → Setˢ Γ₁ (Now ∷ [])
𝒱ˢ⟦ A ⟧ V = inj₁ (A , V) ∈ zeroˢ

ℰˢ⟦_⟧ : Type → Term → Setˢ Γ₁ (Now ∷ [])
ℰˢ⟦ A ⟧ M = inj₂ (A , M) ∈ zeroˢ
\end{code}

The definition of \textsf{pre-ℰ}, i.e., what it means for a term to be
well behaved, is essentially a statement of what we'd like to prove:
``progress'' and ``preservation''. In particular, the progress part
says that either $M$ is a well-behaved value or it is reducible. The
preservation part says that if $M$ reduces to $N$, then $N$ is also
well behaved. Note that we insert the ▷ˢ operator in front of the
recursive use of ℰ because when we use the μᵒ operator, it will
require the zero de Bruijn index to be at time \textsf{Later}.

\begin{code}
pre-ℰ A M = (pre-𝒱 A M ⊎ˢ (reducible M)ˢ) ×ˢ (∀ˢ[ N ] (M —→ N)ˢ →ˢ ▷ˢ (ℰˢ⟦ A ⟧ N))
\end{code}

The definition of \textsf{pre-𝒱} defines what it means to be a
well-behaved value according to a given type. For type ℕ, the value
must be the literal for zero or be the successor of a well-behaved
value at type ℕ. For function types, the value must be either a lambda
abstraction or fixpoint. In the former case, given an arbitrary
well-behaved values $W$, substituting it into the lambda's body $N$
produces a well-behaved term.  In the later case, for the fixpoint
value $μ\,V$, the $V$ must be a value (syntactically) and substituting
the whose fixpoint value into $V$ produces a well-behaved value. We
insert the ▷ˢ operator around each recursive use of 𝒱 and ℰ.

\begin{code}
pre-𝒱 `ℕ `zero       = topᵖ ˢ
pre-𝒱 `ℕ (`suc V)    = pre-𝒱 `ℕ V
pre-𝒱 (A ⇒ B) (ƛ N)  = ∀ˢ[ W ] ▷ˢ (𝒱ˢ⟦ A ⟧ W) →ˢ ▷ˢ (ℰˢ⟦ B ⟧ (N [ W ]))
pre-𝒱 (A ⇒ B) (μ V)  = (Value V)ˢ ×ˢ (▷ˢ (𝒱ˢ⟦ A ⇒ B ⟧ (V [ μ V ])))
pre-𝒱 A M            = ⊥ ˢ
\end{code}

Next we prove several lemmas that encapsulate uses of the fixpoint
theorem.  We define the following shorthand for referring to the two
parts of the ℰ predicate.

\begin{code}
progress : Type → Term → Setᵒ
progress A M = 𝒱⟦ A ⟧ M ⊎ᵒ (reducible M)ᵒ

preservation : Type → Term → Setᵒ
preservation A M = ∀ᵒ[ N ] ((M —→ N)ᵒ →ᵒ ▷ᵒ (ℰ⟦ A ⟧ N))
\end{code}

\noindent The first lemma states that $ℰ⟦ A ⟧ M$ is equivalent to the
conjunction of progress and preservation. The proof uses the fixpoint
theorem twice, once to unfold the definintion of ℰ and then again
to fold the definition of 𝒱.

\begin{code}
ℰ-stmt : ∀{A}{M} → ℰ⟦ A ⟧ M ≡ᵒ progress A M ×ᵒ preservation A M
ℰ-stmt {A}{M} =
  ℰ⟦ A ⟧ M                                 ⩦⟨ ≡ᵒ-refl refl ⟩
  μᵒ pre-𝒱⊎ℰ (inj₂ (A , M))                ⩦⟨ fixpointᵒ pre-𝒱⊎ℰ (inj₂ (A , M)) ⟩
  ♯ (pre-𝒱⊎ℰ (inj₂ (A , M))) (𝒱⊎ℰ , ttᵖ)
      ⩦⟨ cong-×ᵒ (cong-⊎ᵒ (≡ᵒ-sym (fixpointᵒ pre-𝒱⊎ℰ (inj₁ (A , M)))) (≡ᵒ-refl refl)) (≡ᵒ-refl refl) ⟩
  progress A M ×ᵒ preservation A M           ∎
\end{code}

\noindent The following introduction rule for ℰ is a directly
corollary of the above.

\begin{code}
ℰ-intro : ∀ {𝒫}{A}{M} → 𝒫 ⊢ᵒ progress A M → 𝒫 ⊢ᵒ preservation A M → 𝒫 ⊢ᵒ ℰ⟦ A ⟧ M
ℰ-intro 𝒫⊢prog 𝒫⊢pres = substᵒ (≡ᵒ-sym ℰ-stmt) (𝒫⊢prog ,ᵒ 𝒫⊢pres)
\end{code}

Next we turn several uses of the fixpoint theorem for 𝒱.
The successor of a value is a well-behaved ℕ if-and-only-if the value
is a well-behaved ℕ.

\begin{code}
𝒱-suc : 𝒱⟦ `ℕ ⟧ (`suc V) ≡ᵒ 𝒱⟦ `ℕ ⟧ V
𝒱-suc {V} = let X = inj₁ (`ℕ , `suc V) in
  𝒱⟦ `ℕ ⟧ (`suc V)              ⩦⟨ ≡ᵒ-refl refl ⟩
  𝒱⊎ℰ X                         ⩦⟨ fixpointᵒ pre-𝒱⊎ℰ X ⟩
  ♯ (pre-𝒱⊎ℰ X) (𝒱⊎ℰ , ttᵖ)     ⩦⟨ ≡ᵒ-sym (fixpointᵒ pre-𝒱⊎ℰ (inj₁ (`ℕ , V))) ⟩ 
  𝒱⟦ `ℕ ⟧ V                     ∎
\end{code}

\noindent A lambda abstraction $ƛ N$ is well-behaved at type $A ⇒ B$
if-and-only-if $N [ W ]$ is well-behaved at $B$ assuming that $W$ is
well-behaved at $A$.

\begin{code}
𝒱-fun : ∀{A B}{N} → 𝒱⟦ A ⇒ B ⟧ (ƛ N) ≡ᵒ (∀ᵒ[ W ] ((▷ᵒ (𝒱⟦ A ⟧ W)) →ᵒ (▷ᵒ (ℰ⟦ B ⟧ (N [ W ])))))
𝒱-fun {A}{B}{N} = let X = (inj₁ (A ⇒ B , ƛ N)) in
   𝒱⟦ A ⇒ B ⟧ (ƛ N)                                         ⩦⟨ ≡ᵒ-refl refl ⟩
   𝒱⊎ℰ X                                                    ⩦⟨ fixpointᵒ pre-𝒱⊎ℰ X ⟩
   ♯ (pre-𝒱⊎ℰ X) (𝒱⊎ℰ , ttᵖ)                                ⩦⟨ ≡ᵒ-refl refl ⟩ 
   (∀ᵒ[ W ] ((▷ᵒ (𝒱⟦ A ⟧ W)) →ᵒ (▷ᵒ (ℰ⟦ B ⟧ (N [ W ])))))    ∎
\end{code}

\noindent A fixpoint value $μ\,V$ is well-behaved at type $A ⇒ B$ if-and-only-if $V$ is
a value and $V[μ\, V]$ is well behaved at $A ⇒ B$.

\begin{code}
𝒱-μ : ∀{A B}{V} → 𝒱⟦ A ⇒ B ⟧ (μ V) ≡ᵒ (Value V)ᵒ ×ᵒ (▷ᵒ (𝒱⟦ A ⇒ B ⟧ (V [ μ V ])))
𝒱-μ {A}{B}{V} = let X = (inj₁ (A ⇒ B , μ V)) in
   𝒱⟦ A ⇒ B ⟧ (μ V)                                         ⩦⟨ ≡ᵒ-refl refl ⟩
   𝒱⊎ℰ X                                                    ⩦⟨ fixpointᵒ pre-𝒱⊎ℰ X ⟩
   ♯ (pre-𝒱⊎ℰ X) (𝒱⊎ℰ , ttᵖ)                                ⩦⟨ ≡ᵒ-refl refl ⟩ 
   (Value V)ᵒ ×ᵒ (▷ᵒ (𝒱⟦ A ⇒ B ⟧ (V [ μ V ])))               ∎
\end{code}

If we have a well-behaved value at a function type $A ⇒ B$,
then it must either be a lambda abstraction or a fixpoint value.

\begin{code}
𝒱-fun-case : ∀{𝒫}{A}{B}{V}{R} → 𝒫 ⊢ᵒ 𝒱⟦ A ⇒ B ⟧ V
  → (∀ N → V ≡ ƛ N → 𝒫 ⊢ᵒ R)  →  (∀ V′ → V ≡ μ V′ → 𝒫 ⊢ᵒ R)  →  𝒫 ⊢ᵒ R
𝒱-fun-case {𝒫}{A}{B}{V}{R} ⊢𝒱V contλ contμ =
  ⊢ᵒ-sucP ⊢𝒱V λ { 𝒱Vsn → aux{V} 𝒱Vsn contλ contμ }
  where aux : ∀{V n} → # (𝒱⟦ A ⇒ B ⟧ V) (suc n)  →  (∀ N → V ≡ ƛ N → 𝒫 ⊢ᵒ R)
            →  (∀ V′ → V ≡ μ V′ → 𝒫 ⊢ᵒ R)  →  𝒫 ⊢ᵒ R
        aux {ƛ N} 𝒱sn contλ contμ = contλ N refl
        aux {μ V′} 𝒱sn contλ contμ = contμ V′ refl
\end{code}

\noindent A well-behaved value is of course a value.

\begin{code}
𝒱⇒Value : ∀ {k} A M → # (𝒱⟦ A ⟧ M) (suc k) → Value M
𝒱⇒Value `ℕ `zero 𝒱M = V-zero
𝒱⇒Value `ℕ (`suc M) 𝒱M = V-suc (𝒱⇒Value `ℕ M 𝒱M)
𝒱⇒Value (A ⇒ B) (ƛ N) 𝒱M = V-ƛ
𝒱⇒Value (A ⇒ B) (μ V) (v , ▷𝒱V[μV]) = V-μ v
\end{code}

\noindent A well-behaved value is also a well-behaved term.

\begin{code}
𝒱⇒ℰ : ∀{A}{𝒫}{V} →  𝒫 ⊢ᵒ 𝒱⟦ A ⟧ V  →  𝒫 ⊢ᵒ ℰ⟦ A ⟧ V
𝒱⇒ℰ {A}{𝒫}{V} 𝒫⊢𝒱V = ℰ-intro prog pres
    where prog = inj₁ᵒ 𝒫⊢𝒱V
          pres = Λᵒ[ N ] →ᵒI (pureᵒE Zᵒ λ V—→N →
                   ⊢ᵒ-sucP (Sᵒ 𝒫⊢𝒱V) λ 𝒱V →
                      ⊥-elim (value-irreducible (𝒱⇒Value A V 𝒱V ) V—→N))
\end{code}

\subsection{Definition of Semantic Type Safety for Open Terms}
\label{sec:sem-type-safety}

The predicates 𝒱 and ℰ characterize well-behaved terms without any
free variables, that is, closed terms. (Note that the definition of
\textsf{pre-𝒱} does not include a case for variables.)  However, we
shall also need to handle terms with free variables, i.e., open
terms.  The standard approach is to apply a substitution,
mapping variables to closed values, to turn the open term into a
closed term.

The following defines a well-behaved substitution, that is, a
substitution that maps variables to well-behaved values.

\begin{code}
𝓖⟦_⟧ : (Γ : List Type) → Subst → List Setᵒ
𝓖⟦ [] ⟧ σ = []
𝓖⟦ A ∷ Γ ⟧ σ = (𝒱⟦ A ⟧ (σ 0)) ∷ 𝓖⟦ Γ ⟧ (λ x → σ (suc x))
\end{code}

\noindent A term $V$ is a well-behaved open value at type $A$ in type
environment Γ if, for any well-behaved substitution γ, $⟪ γ ⟫\, V$ is
a well behaved value.

\begin{code}
infix 3 _⊨ⱽ_⦂_
_⊨ⱽ_⦂_ : List Type → Term → Type → Set
Γ ⊨ⱽ V ⦂ A = ∀ (γ : Subst) → 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝒱⟦ A ⟧ (⟪ γ ⟫ V)
\end{code}

\noindent A term $M$ is well-behaved open term at type $A$ in
type environment Γ if, for any well-behaved substitution γ,
$⟪ γ ⟫\, M$ is well behaved.

\begin{code}
infix 3 _⊨_⦂_
_⊨_⦂_ : List Type → Term → Type → Set
Γ ⊨ M ⦂ A = ∀ (γ : Subst) → 𝓖⟦ Γ ⟧ γ ⊢ᵒ ℰ⟦ A ⟧ (⟪ γ ⟫ M)
\end{code}

The proof of semantic type safety will make use of the Fundamental
Lemma for this logical relation, which states that a well-typed term
is also a well-behaved open term. More formally, $Γ ⊢ M ⦂ A$ implies
$Γ ⊨ M ⦂ A$ (and likewise for well-typed values).  The proof will be
by induction on the derivation of $Γ ⊢ M ⦂ A$, with a case for each
typing rule. Each of those cases will be proved in a separate
``compatibility`` lemma in Section~\ref{sec:compatibility-lemmas}.
But first we prove the ``bind'' lemma.



