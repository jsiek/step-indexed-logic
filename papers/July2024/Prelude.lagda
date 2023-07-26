\begin{comment}
\begin{code}
{-# OPTIONS --without-K #-}
module July2024.Prelude where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat
   using (ℕ; zero; suc; _≤_; _<_; _+_; _∸_; z≤n; s≤s; _≤′_; ≤′-step)
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

\end{code}
\end{comment}

%===============================================================================
\section{Representation of Step-Indexed Propositions}
\label{sec:propositions}

We represent the meaning of a step-indexed proposition with an Agda
function from natural numbers to \textsf{Set}, which is the Agda type
for propositions. The step-indexed propositions should always be
downward closed and true at step zero, so we bundle the representing
function with proofs of these properties into a dependent record.

Here is the definition of \textsf{downClosed}
\begin{code}
downClosed : (ℕ → Set) → Set
downClosed P = ∀ n → P n → ∀ k → k ≤ n → P k
\end{code}

\noindent and here is the definition of $\mathsf{Set}ᵒ$, the type for
step-indexed propositions.

\begin{code}
record Setᵒ : Set₁ where
  field
    # : ℕ → Set
    down : downClosed #
    tz : # 0
open Setᵒ public
\end{code}
Let $ϕ, ψ, þ$ range over step-indexed propositions.
\begin{code}
variable ϕ ϕ′ ψ ψ′ þ : Setᵒ
\end{code}
Let $p, q, r$ range over (regular) propositions.
\begin{code}
variable p q r : Set
\end{code}

\noindent The rest of the SIL formulas are defined in
Section~\ref{sec:open-propositions}.

We define equivalence of step-indexed propositions $ϕ$ and $ψ$ to be
that for any step $k$, $ϕ$ at $k$ is true if and only if $ψ$ at $k$ is
true. We make the definition abstract in Agda because that improves
Agda's ability to perform inference.

\begin{code}
abstract
  infix 2 _≡ᵒ_
  _≡ᵒ_ : Setᵒ → Setᵒ → Set
  ϕ ≡ᵒ ψ = ∀ k → # ϕ k ⇔ # ψ k

  ≡ᵒ-intro : ∀{ϕ ψ : Setᵒ} → (∀ k → # ϕ k ⇔ # ψ k) → ϕ ≡ᵒ ψ
  ≡ᵒ-intro P⇔Q k = P⇔Q k
  
  ≡ᵒ-elim : ∀{S T : Setᵒ}{k} → S ≡ᵒ T → # S k ⇔ # T k
  ≡ᵒ-elim {S}{T}{k} eq = eq k
\end{code}

\noindent This is an equivalence relation and we make use of a library
named \textsf{EquivalenceRelation} to provide nice syntax for
equational reasoning.

\begin{code}
abstract
  ≡ᵒ-refl : ϕ ≡ ψ → ϕ ≡ᵒ ψ
  ≡ᵒ-refl refl i = (λ x → x) , (λ x → x)
  
  ≡ᵒ-sym : ϕ ≡ᵒ ψ → ψ ≡ᵒ ϕ
  ≡ᵒ-sym PQ i = (proj₂ (PQ i)) , (proj₁ (PQ i))
  
  ≡ᵒ-trans : ϕ ≡ᵒ ψ → ψ ≡ᵒ þ → ϕ ≡ᵒ þ
  ≡ᵒ-trans PQ QR i = (λ z → proj₁ (QR i) (proj₁ (PQ i) z)) , (λ z → proj₂ (PQ i) (proj₂ (QR i) z))
instance
  SIL-Eqᵒ : EquivalenceRelation Setᵒ
  SIL-Eqᵒ = record { _⩦_ = _≡ᵒ_ ; ⩦-refl = ≡ᵒ-refl ; ⩦-sym = ≡ᵒ-sym ; ⩦-trans = ≡ᵒ-trans }
\end{code}

\section{Representation of Step-Indexed Predicates}
\label{sec:predicates}

To express step-indexed predicates over arbitrary Agda types, we
define the type $\mathsf{Pred}ᵒ A$ to be a function from $A$ to
$\mathsf{Set}ᵒ$.

\begin{code}
Predᵒ : Set → Set₁
Predᵒ A = A → Setᵒ
\end{code}

\noindent Let $A,B,C$ range over Agda types (element of \textsf{Set})

\begin{code}
variable A B C : Set
\end{code}

\noindent Let $P, Q$ range over step-indexed predicates.

\begin{code}
variable P Q R : Predᵒ A
\end{code}

We define the constantly true predicate as follows.
\begin{code}
⊤ᵖ : ∀{A} → Predᵒ A
⊤ᵖ = (λ a → record { # = λ n → ⊤ ; down = λ n _ k _ → tt ; tz = tt })
\end{code}

The equivalence of predicates applied to the same argument forms an
equivalence relation.

\begin{code}
≡ᵖ-refl : P ≡ Q → ∀ {a} → P a ≡ᵒ Q a
≡ᵖ-refl refl {a} = ≡ᵒ-refl refl

≡ᵖ-sym : (∀ {a} → P a ≡ᵒ Q a) → ∀ {a} → Q a ≡ᵒ P a
≡ᵖ-sym P=Q {a} = ≡ᵒ-sym P=Q

≡ᵖ-trans : (∀ {a} → P a ≡ᵒ Q a) → (∀ {a} → Q a ≡ᵒ R a) → ∀ {a} → P a ≡ᵒ R a
≡ᵖ-trans P=Q Q=R {a} = ≡ᵒ-trans P=Q Q=R
\end{code}

A \textsf{Context} is a list of types. The metavariable $Γ$ ranges
over contexts.

\begin{code}
Context : Set₁
Context = List Set
variable Γ : Context
\end{code}

\noindent The following data type defines well-typed de Bruijn indices.

\begin{code}
data _∋_ : Context → Set → Set₁ where
  zeroˢ : (A ∷ Γ) ∋ A
  sucˢ : Γ ∋ B → (A ∷ Γ) ∋ B
variable x y z : Γ ∋ A
\end{code}

To keep track of whether a variable has been used underneath a later
operator or not, we introduce a notion of time and we introduce a
specialized list type to record the times for all the variables in a
context.

\begin{code}
data Time : Set where
  Now : Time
  Later : Time

data Times : Context → Set₁ where
  ∅ : Times []
  cons : Time → Times Γ → Times (A ∷ Γ)
\end{code}
Let $Δ$ range over these lists of times.
\begin{code}
variable Δ Δ₁ Δ₂ : Times Γ
\end{code}

\begin{code}
laters : ∀ (Γ : Context) → Times Γ
laters [] = ∅
laters (A ∷ Γ) = cons Later (laters Γ)

var-now : ∀ (Γ : Context) → ∀{A} → (x : Γ ∋ A) → Times Γ
var-now (B ∷ Γ) zeroˢ = cons Now (laters Γ)
var-now (B ∷ Γ) (sucˢ x) = cons Later (var-now Γ x)
\end{code}

\begin{code}
choose : Time → Time → Time
choose Now Now = Now
choose Now Later = Now
choose Later Now = Now
choose Later Later = Later
\end{code}

\begin{code}
_∪_ : ∀{Γ} (Δ₁ Δ₂ : Times Γ) → Times Γ
_∪_ {[]} Δ₁ Δ₂ = ∅
_∪_ {A ∷ Γ} (cons x Δ₁) (cons y Δ₂) = cons (choose x y) (Δ₁ ∪ Δ₂)
\end{code}

\begin{code}
record Inhabited (A : Set) : Set where
  field elt : A
open Inhabited {{...}} public
\end{code}

\begin{code}
RecEnv : Context → Set₁
RecEnv [] = topᵖ 
RecEnv (A ∷ Γ) = Predᵒ A × RecEnv Γ
\end{code}

