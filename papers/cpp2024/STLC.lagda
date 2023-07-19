\begin{comment}
\begin{code}
{-# OPTIONS --rewriting #-}

module cpp2024.STLC where

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
open import cpp2024.StepIndexedLogic

\end{code}
\end{comment}

\section{Case Study: Type Safety of the STLC with Recursive Functions}

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

The proof of semantic type safety relies on a lemma regarding
substitution whose proof is quite involved but quite standard.  We can
obtain the substitution lemma for free if we use the Abstract Binding
Tree (ABT) library~\citep{Siek:2021to} to define the syntax of terms.  The
library is parameterized by a type \textsf{Op} that specifies the
constructors and a function \textsf{sig} that describes the arity and
binding structure of each term constructor. For this variant of the
STLC, the terms include lambda abstraction, application, the zero
numeral, the successor operation, case analysis on natural numbers,
and a recursive fixpoint operator.

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
whose type we name \textsf{Term}, and we obtain all of the
substitution lemmas provided by the library.

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
  ξξ : ∀ {M N : Term} {M′ N′ : Term}
    → (F : Frame) →  M′ ≡ F ⟦ M ⟧  →  N′ ≡ F ⟦ N ⟧  →  M —→ N  →  M′ —→ N′
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

\begin{code}
infix 3 _⊢_⦂_
data _⊢_⦂_ : List Type → Term → Type → Set

infix 3 _⊢ⱽ_⦂_
data _⊢ⱽ_⦂_ : List Type → Term → Type → Set
\end{code}


\begin{code}
data _⊢ⱽ_⦂_ where
  ⊢ⱽzero : ∀ {Γ} → Γ ⊢ⱽ `zero ⦂ `ℕ
  ⊢ⱽsuc : ∀ {Γ V} → Γ ⊢ⱽ V ⦂ `ℕ  →  Γ ⊢ⱽ `suc V ⦂ `ℕ
  ⊢ⱽƛ : ∀ {Γ N A B} → (A ∷ Γ) ⊢ N ⦂ B  →  Γ ⊢ⱽ ƛ N ⦂ (A ⇒ B)
  ⊢ⱽμ : ∀ {Γ V A B} → (A ⇒ B ∷ Γ) ⊢ⱽ V ⦂ A ⇒ B  →  Γ ⊢ⱽ μ V ⦂ A ⇒ B
\end{code}

\begin{code}
data _⊢_⦂_ where

  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ⦂ A

  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ⦂ `ℕ
      ---------------
    → Γ ⊢ `suc M ⦂ `ℕ
    
  ⊢case : ∀{Γ L M N A}
    → Γ ⊢ L ⦂ `ℕ
    → Γ ⊢ M ⦂ A
    → `ℕ ∷ Γ ⊢ N ⦂ A
      ------------------
    → Γ ⊢ case L M N ⦂ A

  ⊢· : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ (A ⇒ B)
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B

  ⊢val : ∀ {Γ V A}
    → Γ ⊢ⱽ V ⦂ A
      ----------
    → Γ ⊢ V ⦂ A
\end{code}

\begin{code}
⊢ⱽ⇒Value : ∀{Γ V A} → Γ ⊢ⱽ V ⦂ A → Value V
⊢ⱽ⇒Value ⊢ⱽzero = V-zero
⊢ⱽ⇒Value (⊢ⱽsuc ⊢V) = V-suc (⊢ⱽ⇒Value ⊢V)
⊢ⱽ⇒Value (⊢ⱽƛ ⊢N) = V-ƛ
⊢ⱽ⇒Value (⊢ⱽμ ⊢V) = V-μ (⊢ⱽ⇒Value ⊢V)
\end{code}

\subsection{Definition of the Logical Relation}
\label{sec:log-rel}

\begin{code}
ℰ⊎𝒱-type : Set
ℰ⊎𝒱-type = (Type × Term) ⊎ (Type × Term)

ℰ⊎𝒱-ctx : Context
ℰ⊎𝒱-ctx = ℰ⊎𝒱-type ∷ []
\end{code}



\begin{code}
ℰˢ⟦_⟧ : Type → Term → Setˢ ℰ⊎𝒱-ctx (cons Now ∅)
ℰˢ⟦ A ⟧ M = (inj₂ (A , M)) ∈ zeroˢ

𝒱ˢ⟦_⟧ : Type → Term → Setˢ ℰ⊎𝒱-ctx (cons Now ∅)
𝒱ˢ⟦ A ⟧ V = (inj₁ (A , V)) ∈ zeroˢ
\end{code}

\begin{code}
pre-ℰ : Type → Term → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)
pre-𝒱 : Type → Term → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)

pre-ℰ A M = (pre-𝒱 A M ⊎ˢ (reducible M)ˢ) ×ˢ (∀ˢ[ N ] (M —→ N)ˢ →ˢ ▷ˢ (ℰˢ⟦ A ⟧ N))

pre-𝒱 `ℕ `zero       = topᵖ ˢ
pre-𝒱 `ℕ (`suc V)    = pre-𝒱 `ℕ V
pre-𝒱 (A ⇒ B) (ƛ N)  = ∀ˢ[ W ] ▷ˢ (𝒱ˢ⟦ A ⟧ W) →ˢ ▷ˢ (ℰˢ⟦ B ⟧ (N [ W ]))
pre-𝒱 (A ⇒ B) (μ V)  = (Value V)ˢ ×ˢ (▷ˢ (𝒱ˢ⟦ A ⇒ B ⟧ (V [ μ V ])))
pre-𝒱 A M            = ⊥ ˢ
\end{code}

\begin{code}
pre-ℰ⊎𝒱 : ℰ⊎𝒱-type → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)
pre-ℰ⊎𝒱 (inj₁ (A , V)) = pre-𝒱 A V
pre-ℰ⊎𝒱 (inj₂ (A , M)) = pre-ℰ A M

ℰ⊎𝒱 : ℰ⊎𝒱-type → Setᵒ
ℰ⊎𝒱 X = μᵒ pre-ℰ⊎𝒱 X
\end{code}

\begin{code}
ℰ⟦_⟧ : Type → Term → Setᵒ
ℰ⟦ A ⟧ M = ℰ⊎𝒱 (inj₂ (A , M))

𝒱⟦_⟧ : Type → Term → Setᵒ
𝒱⟦ A ⟧ V = ℰ⊎𝒱 (inj₁ (A , V))
\end{code}


\begin{code}
progress : Type → Term → Setᵒ
progress A M = 𝒱⟦ A ⟧ M ⊎ᵒ (reducible M)ᵒ

preservation : Type → Term → Setᵒ
preservation A M = ∀ᵒ[ N ] ((M —→ N)ᵒ →ᵒ ▷ᵒ (ℰ⟦ A ⟧ N))
\end{code}

\begin{code}
open import EquivalenceRelation public
\end{code}

\begin{code}
ℰ-stmt : ∀{A}{M} → ℰ⟦ A ⟧ M ≡ᵒ progress A M ×ᵒ preservation A M
ℰ-stmt {A}{M} =
  ℰ⟦ A ⟧ M                                 ⩦⟨ ≡ᵒ-refl refl ⟩
  μᵒ pre-ℰ⊎𝒱 (inj₂ (A , M))               ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 (inj₂ (A , M)) ⟩
  ♯ (pre-ℰ⊎𝒱 (inj₂ (A , M))) (ℰ⊎𝒱 , ttᵖ) ⩦⟨ cong-×ᵒ (cong-⊎ᵒ (≡ᵒ-sym (fixpointᵒ pre-ℰ⊎𝒱 (inj₁ (A , M))))
                                                  (≡ᵒ-refl refl)) (≡ᵒ-refl refl) ⟩
  progress A M ×ᵒ preservation A M         ∎
\end{code}

\begin{code}
ℰ-intro : ∀ {𝒫}{A}{M} → 𝒫 ⊢ᵒ progress A M → 𝒫 ⊢ᵒ preservation A M → 𝒫 ⊢ᵒ ℰ⟦ A ⟧ M
ℰ-intro 𝒫⊢prog 𝒫⊢pres = substᵒ (≡ᵒ-sym ℰ-stmt) (𝒫⊢prog ,ᵒ 𝒫⊢pres)

ℰ-progress : ∀ {𝒫}{A}{M} → 𝒫 ⊢ᵒ ℰ⟦ A ⟧ M → 𝒫 ⊢ᵒ progress A M
ℰ-progress 𝒫⊢ℰM = proj₁ᵒ (substᵒ ℰ-stmt 𝒫⊢ℰM )

ℰ-preservation : ∀ {𝒫}{A}{M} → 𝒫 ⊢ᵒ ℰ⟦ A ⟧ M → 𝒫 ⊢ᵒ preservation A M
ℰ-preservation 𝒫⊢ℰM = proj₂ᵒ (substᵒ ℰ-stmt 𝒫⊢ℰM )
\end{code}

\begin{code}
𝒱-suc : ∀{M} → 𝒱⟦ `ℕ ⟧ (`suc M) ≡ᵒ 𝒱⟦ `ℕ ⟧ M
𝒱-suc {M} = let X = inj₁ (`ℕ , `suc M) in
  𝒱⟦ `ℕ ⟧ (`suc M)              ⩦⟨ ≡ᵒ-refl refl ⟩
  ℰ⊎𝒱 X                         ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X ⟩
  ♯ (pre-ℰ⊎𝒱 X) (ℰ⊎𝒱 , ttᵖ)     ⩦⟨ ≡ᵒ-sym (fixpointᵒ pre-ℰ⊎𝒱 (inj₁ (`ℕ , M))) ⟩ 
  𝒱⟦ `ℕ ⟧ M                     ∎
\end{code}

\begin{code}
𝒱-fun : ∀{A B}{N} → 𝒱⟦ A ⇒ B ⟧ (ƛ N) ≡ᵒ (∀ᵒ[ W ] ((▷ᵒ (𝒱⟦ A ⟧ W)) →ᵒ (▷ᵒ (ℰ⟦ B ⟧ (N [ W ])))))
𝒱-fun {A}{B}{N} =
   let X = (inj₁ (A ⇒ B , ƛ N)) in
   𝒱⟦ A ⇒ B ⟧ (ƛ N)                                         ⩦⟨ ≡ᵒ-refl refl ⟩
   ℰ⊎𝒱 X                                                    ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X ⟩
   ♯ (pre-ℰ⊎𝒱 X) (ℰ⊎𝒱 , ttᵖ)                               ⩦⟨ ≡ᵒ-refl refl ⟩ 
   (∀ᵒ[ W ] ((▷ᵒ (𝒱⟦ A ⟧ W)) →ᵒ (▷ᵒ (ℰ⟦ B ⟧ (N [ W ])))))   ∎
\end{code}

\begin{code}
𝒱-μ : ∀{A B}{V} → 𝒱⟦ A ⇒ B ⟧ (μ V) ≡ᵒ (Value V)ᵒ ×ᵒ (▷ᵒ (𝒱⟦ A ⇒ B ⟧ (V [ μ V ])))
𝒱-μ {A}{B}{V} =
   let X = (inj₁ (A ⇒ B , μ V)) in
   𝒱⟦ A ⇒ B ⟧ (μ V)                                         ⩦⟨ ≡ᵒ-refl refl ⟩
   ℰ⊎𝒱 X                                                    ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X ⟩
   ♯ (pre-ℰ⊎𝒱 X) (ℰ⊎𝒱 , ttᵖ)                               ⩦⟨ ≡ᵒ-refl refl ⟩ 
   (Value V)ᵒ ×ᵒ (▷ᵒ (𝒱⟦ A ⇒ B ⟧ (V [ μ V ])))              ∎
\end{code}

\begin{code}
safe-body : List Setᵒ → Term → Type → Type → Set
safe-body 𝒫 N A B = ∀{W} → 𝒫 ⊢ᵒ (▷ᵒ (𝒱⟦ A ⟧ W)) →ᵒ (▷ᵒ (ℰ⟦ B ⟧ (N [ W ])))

𝒱-fun-elim : ∀{𝒫}{A}{B}{V}{R}
   → 𝒫 ⊢ᵒ 𝒱⟦ A ⇒ B ⟧ V
   → (∀ N → V ≡ ƛ N → safe-body 𝒫 N A B → 𝒫 ⊢ᵒ R)
   → (∀ V′ → V ≡ μ V′ → 𝒫 ⊢ᵒ ▷ᵒ (𝒱⟦ A ⇒ B ⟧ (V′ [ V ])) → 𝒫 ⊢ᵒ R)
    ---------------------------------------------------------------
   → 𝒫 ⊢ᵒ R
𝒱-fun-elim {𝒫}{A}{B}{V}{R} ⊢𝒱V contλ contμ =
  ⊢ᵒ-sucP ⊢𝒱V λ { 𝒱Vsn → aux {V} 𝒱Vsn ⊢𝒱V contλ contμ}
  where
  aux : ∀{V}{n}
     → # (𝒱⟦ A ⇒ B ⟧ V) (suc n)
     → 𝒫 ⊢ᵒ 𝒱⟦ A ⇒ B ⟧ V
     → (∀ N → V ≡ ƛ N → safe-body 𝒫 N A B → 𝒫 ⊢ᵒ R)
     → (∀ V′ → V ≡ μ V′ → 𝒫 ⊢ᵒ ▷ᵒ (𝒱⟦ A ⇒ B ⟧ (V′ [ V ])) → 𝒫 ⊢ᵒ R)
     → 𝒫 ⊢ᵒ R
  aux{ƛ N}{n} 𝒱V ⊢𝒱V contλ contμ = contλ N refl λ {W} →
      instᵒ{ϕᵃ = λ W → (▷ᵒ (𝒱⟦ A ⟧ W)) →ᵒ (▷ᵒ (ℰ⟦ B ⟧ (N [ W ])))}
                 (substᵒ 𝒱-fun ⊢𝒱V) W
  aux{μ V}{n} 𝒱V ⊢𝒱V contλ contμ = contμ V refl (⊢ᵒ-intro
     λ { zero 𝒫k → tt
       ; (suc k) → λ 𝒫sk → let (v , 𝒱V[μV]) = ⊢ᵒ-elim ⊢𝒱V (suc k) 𝒫sk in  𝒱V[μV]})
\end{code}

\begin{code}
𝒱⇒Value : ∀ {k} A M → # (𝒱⟦ A ⟧ M) (suc k) → Value M
𝒱⇒Value `ℕ `zero 𝒱M = V-zero
𝒱⇒Value `ℕ (`suc M) 𝒱M = V-suc (𝒱⇒Value `ℕ M 𝒱M)
𝒱⇒Value (A ⇒ B) (ƛ N) 𝒱M = V-ƛ
𝒱⇒Value (A ⇒ B) (μ V) (v , ▷𝒱V[μV]) = V-μ v
\end{code}

\begin{code}
𝒱⇒ℰ : ∀{A}{𝒫}{V}
   → 𝒫 ⊢ᵒ 𝒱⟦ A ⟧ V
     ---------------
   → 𝒫 ⊢ᵒ ℰ⟦ A ⟧ V
𝒱⇒ℰ {A}{𝒫}{V} 𝒫⊢𝒱V = ℰ-intro prog pres
    where
    prog = inj₁ᵒ 𝒫⊢𝒱V
    pres = Λᵒ[ N ] →ᵒI (constᵒE Zᵒ λ V—→N →
             ⊢ᵒ-sucP (Sᵒ 𝒫⊢𝒱V) λ 𝒱V →
                ⊥-elim (value-irreducible (𝒱⇒Value A V 𝒱V ) V—→N))
\end{code}

\subsection{Definition of Semantic Type Safety for Open Terms}
\label{sec:sem-type-safety}


\begin{code}
𝓖⟦_⟧ : (Γ : List Type) → Subst → List Setᵒ
𝓖⟦ [] ⟧ σ = []
𝓖⟦ A ∷ Γ ⟧ σ = (𝒱⟦ A ⟧ (σ 0)) ∷ 𝓖⟦ Γ ⟧ (λ x → σ (suc x))
\end{code}

\begin{code}
infix 3 _⊨_⦂_
_⊨_⦂_ : List Type → Term → Type → Set
Γ ⊨ M ⦂ A = ∀ (γ : Subst) → 𝓖⟦ Γ ⟧ γ ⊢ᵒ ℰ⟦ A ⟧ (⟪ γ ⟫ M)
\end{code}

\begin{code}
infix 3 _⊨ⱽ_⦂_
_⊨ⱽ_⦂_ : List Type → Term → Type → Set
Γ ⊨ⱽ V ⦂ A = ∀ (γ : Subst) → 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝒱⟦ A ⟧ (⟪ γ ⟫ V)
\end{code}


