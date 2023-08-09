\begin{comment}
\begin{code}
{-# OPTIONS --rewriting --prop #-}

module July2023.STLC2 where

open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Nat.Induction
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List using (map)
open import Data.Nat.Properties

open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import PropLib using (⊥-elimₛ) renaming (_⊎_ to _⊎ₚ_; ⊥-elim to ⊥-elimₚ; Σ to Σₚ; ¬_ to ¬ₚ_)

{-
open import Data.Product using () renaming (_×_ to _×ₐ_; _,_ to _,ₐ_; Σ to Σₐ)
open import Data.Sum using () renaming (_⊎_ to _⊎ₐ_; inj₁ to inj₁ₐ; inj₂ to inj₂ₐ)
open import PropLib
-}

open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Induction using (RecStruct)
--open import Induction.WellFounded as WF
--open import Data.Product.Relation.Binary.Lex.Strict using (×-Lex; ×-wellFounded; ×-preorder)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; cong₂; subst; trans)
open import Sig
open import Var
open import StepIndexedLogic2
open import EquivalenceRelationProp public

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


