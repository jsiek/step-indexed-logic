\begin{comment}
\begin{code}
{-# OPTIONS --without-K #-}
module July2023.StepIndexedLogic where

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

postulate impossible : {A : Set} → A
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
Let $i, j, k, m , n$ range over natural numbers.
\begin{code}
variable i j k m n : ℕ
\end{code}

The ``true'' formula of SIL is embedded in Agda by constructing an
instance of the $\mathsf{Set}ᵒ$ record type, with the representation
function mapping every natural number to true. The proofs of
downward-closedness and true-at-zero are straightforward.

\begin{code}
⊤ᵒ : Setᵒ
⊤ᵒ = record { # = λ k → ⊤ ; down = λ n _ k _ → tt ; tz = tt }
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

\noindent and let $P, Q$ range over step-indexed predicates.

\begin{code}
variable P Q R : Predᵒ A
\end{code}

We define the constantly true predicate as follows.
\begin{code}
⊤ᵖ : ∀{A} → Predᵒ A
⊤ᵖ = (λ a → ⊤ᵒ)
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

\section{Functionals, Approximation, and Iteration}
\label{sec:fun-approx-iter}

The definition of recursive predicates and their fixpoint theorem rely
on three concepts that we define in this section: functionals,
$k$-approximation, and iteration.  We also prove several important
lemmas concerning them. These definitions and lemmas are adapted from
\citet{Appel:2001aa}.

In our setting, a \emph{functional} is a function over step-indexed
predicates.  Let $f,g,h$ range over functionals.

\begin{code}
variable f g h : Predᵒ A → Predᵒ B
\end{code}

We say that a functional is congruent if it maps equivalent predicates
to equivalent predicates.

\begin{code}
congruentᵖ : (Predᵒ A → Predᵒ B) → Set₁
congruentᵖ f = ∀ {P Q} → (∀ a → P a ≡ᵒ Q a) → ∀ b → (f P b) ≡ᵒ (f Q b)
\end{code}

The $k$-approximation of a step-indexed proposition, written $↓\, k\, ϕ$,
is true at $i$ if $ϕ$ at $i$ is true and $i < k$, except when $k = 0$, in which
case $↓\, k\, ϕ$ is true unconditionally.

\begin{code}
↓ : ℕ → (ℕ → Set) → (ℕ → Set)
↓ k ϕ zero = ⊤
↓ k ϕ (suc j) = suc j < k × (ϕ (suc j))
\end{code}

\noindent The $k$-approximation operator is downward closed.

\begin{code}
↓-down : ∀ k → downClosed (↓ k (# ϕ))
↓-down {ϕ} k = λ { zero x .zero z≤n → tt
                 ; (suc n) (sn<k , ϕn) zero j≤n → tt
                 ; (suc n) (sn<k , ϕsn) (suc j) (s≤s j≤n) →
                     (≤-trans (s≤s (s≤s j≤n)) sn<k) , (down ϕ (suc n) ϕsn (suc j) (s≤s j≤n))}
\end{code}

\noindent So we can define $k$-approximation for step-indexed
propositions as follows.

\begin{code}
↓ᵒ : ℕ → Setᵒ → Setᵒ
↓ᵒ k ϕ = record { # = ↓ k (# ϕ) ; down = ↓-down {ϕ} k ; tz = tt }
\end{code}

\begin{code}
infix 2 _≡[_]_
_≡[_]_ : Setᵒ → ℕ → Setᵒ → Set
ϕ ≡[ k ] ψ =  ↓ᵒ k ϕ  ≡ᵒ  ↓ᵒ k ψ
\end{code}

\begin{code}
abstract
  ≡[]-refl : ∀ {k} → ϕ ≡ ψ → ϕ ≡[ k ] ψ
  ≡[]-refl {ϕ}{ψ}{k} refl = ≡ᵒ-refl{ϕ = ↓ᵒ k ϕ} refl

  ≡[]-sym : ∀ {k} → ϕ ≡[ k ] ψ → ψ ≡[ k ] ϕ
  ≡[]-sym {ϕ}{ψ}{k} ϕ=ψ = ≡ᵒ-sym{ϕ = ↓ᵒ k ϕ}{↓ᵒ k ψ} ϕ=ψ

  ≡[]-trans : ∀ {k} → ϕ ≡[ k ] ψ → ψ ≡[ k ] þ → ϕ ≡[ k ] þ
  ≡[]-trans {ϕ}{ψ}{þ}{k} ϕ=ψ ψ=þ = ≡ᵒ-trans{ϕ = ↓ᵒ k ϕ}{↓ᵒ k ψ}{↓ᵒ k þ} ϕ=ψ ψ=þ
instance
  SIL-Eq[] : ∀{k} → EquivalenceRelation Setᵒ
  SIL-Eq[] {k} = record { _⩦_ = λ ϕ ψ → ϕ ≡[ k ] ψ ; ⩦-refl = ≡[]-refl ; ⩦-sym = ≡[]-sym ; ⩦-trans = ≡[]-trans }
\end{code}

\begin{code}
≡[]ᵖ-refl : P ≡ Q → ∀ {k a} → P a ≡[ k ] Q a
≡[]ᵖ-refl refl {k}{a} = ≡[]-refl refl
\end{code}

\noindent The $k$-approximations of any two step-indexed propositions
are equivalent when $k=0$ and $k=1$.

\begin{code}
↓ᵒ-zero : ϕ ≡[ 0 ] ψ
↓ᵒ-zero = ≡ᵒ-intro λ {zero → (λ _ → tt) , λ _ → tt
                     ; (suc i) → (λ {()}) , (λ {()})}

↓ᵒ-one : ϕ ≡[ 1 ] ψ
↓ᵒ-one = ≡ᵒ-intro λ {zero → (λ _ → tt) , λ _ → tt
                     ; (suc i) → (λ { (s≤s () , _)}) , (λ { (s≤s () , _)})}
\end{code}

Given two equivalent propositions $ϕ$ and $ψ$, their
$k$-approximations are also eqivalent.

\begin{code}
cong-↓ᵒ : ∀ k → ϕ ≡ᵒ ψ → ϕ ≡[ k ] ψ
cong-↓ᵒ {ϕ} {ψ} k ϕ=ψ = ≡ᵒ-intro aux
  where
  aux : (i : ℕ) → # (↓ᵒ k ϕ) i ⇔ # (↓ᵒ k ψ) i
  aux zero = (λ _ → tt) , (λ _ → tt)
  aux (suc i) = let ϕ⇔ψ = ≡ᵒ-elim ϕ=ψ in
                (λ {(a , b) → a , ⇔-to ϕ⇔ψ b}) , λ {(a , b) → a , ⇔-fro ϕ⇔ψ b}
\end{code}

We lift $k$-approximation to be an operator on predicates with the
following definition.

\begin{code}
↓ᵖ : ℕ → Predᵒ A → Predᵒ A
↓ᵖ j P a = ↓ᵒ j (P a)
\end{code}

\noindent The $↓ᵖ$ operator is congruent.

\begin{code}
cong-↓ : ∀{k} → congruentᵖ{A}{A} (↓ᵖ k)
cong-↓ {A} {k} {P} {Q} P=Q a = ≡ᵒ-intro aux
  where
  aux : (i : ℕ) → ↓ k (# (P a)) i ⇔ ↓ k (# (Q a)) i
  aux zero = (λ _ → tt) , λ _ → tt
  aux (suc i) = (λ {(si≤k , Pasi) → si≤k , ⇔-to (≡ᵒ-elim (P=Q a)) Pasi})
              , (λ {(si≤k , Qasi) → si≤k , ⇔-fro (≡ᵒ-elim (P=Q a)) Qasi})
\end{code}

A functional is \emph{contractive} if applying $k$-approximation to
its input does not change the $k{\plus}1$-approximation of its output.
Intuitively, this corresponds to functions that only use their input
at one step later in time.

\begin{code}
contractiveᵖ : ∀ (f : Predᵒ A → Predᵒ A) → Set₁
contractiveᵖ f = ∀ a P k → f P a ≡[ suc k ] f (↓ᵖ k P) a
\end{code}

The nth iteration of a function, $f^n$, is implemented by the
following $\mathsf{iter}$ function.

\begin{code}
infixr 8 _^_
_^_ : ∀ {ℓ} {A : Set ℓ} → (A → A) → ℕ → (A → A)
f ^ zero     =  id
f ^ (suc n)  =  f ∘ (f ^ n)
\end{code}

\noindent Iterating $k$ times is equivalent to iterating $j$ times
followed by $k ∸ j$ times, assuming that $j \leq k$.

\begin{code}
iter-subtract : ∀{ℓ}{A : Set ℓ}{a : A} (F : A → A) (j k : ℕ) → j ≤ k
  → (F ^ j) ((F ^ (k ∸ j)) a) ≡ (F ^ k) a
iter-subtract {A = A} {a} F .zero k z≤n = refl
iter-subtract {A = A} {a} F (suc j) (suc k) (s≤s j≤k)
  rewrite iter-subtract{A = A}{a} F j k j≤k = refl
\end{code}

Suppose a functional is contractive and congruent.  If you iterate the
functional $j$ times and then take the $j$-approximation, the
initial predicate doesn't matter. This corresponds to Lemma 15 (part 1)
of \citet{Appel:2001aa}.

\begin{code}
lemma15a : ∀ j (f : Predᵒ A → Predᵒ A) (a : A) → contractiveᵖ f → congruentᵖ f
  → (f ^ j) P a ≡[ j ] (f ^ j) Q a
lemma15a zero f a wf-f cong-f = ↓ᵒ-zero
lemma15a {A}{P}{Q} (suc j) f a wf-f cong-f =
      f ((f ^ j) P) a
  ⩦⟨ wf-f a ((f ^ j) P) j ⟩ 
      f (↓ᵖ j ((f ^ j) P)) a
  ⩦⟨ cong-↓ (cong-f λ a → lemma15a j f a wf-f cong-f) a ⟩
      f (↓ᵖ j ((f ^ j) Q)) a
  ⩦⟨ ≡ᵒ-sym (wf-f a ((f ^ j) Q) j) ⟩
      f ((f ^ j) Q) a
  ∎
\end{code}

Again assuming that the functional is contractive and congruent, if
you take the $j$ approximation of the output, iterating the
functional more then $j$ times does not change the result.  This
corresponds to Lemma 15 (part 2) of \citet{Appel:2001aa}.

\begin{code}
lemma15b : (k j : ℕ) (f : Predᵒ A → Predᵒ A) (a : A) → j ≤ k → contractiveᵖ f → congruentᵖ f
   → (f ^ j) P a ≡[ j ] (f ^ k) P a
lemma15b {A}{P} k j f a j≤k wf-f cong-f =
    (f ^ j) P a
  ⩦⟨ lemma15a j f a wf-f cong-f ⟩
    (f ^ j) ((f ^ (k ∸ j)) P) a
  ⩦⟨ cong-↓{A}{j}{(f ^ j) ((f ^ (k ∸ j)) P)}{(f ^ k) P} (λ a → ≡ᵖ-refl (iter-subtract f j k j≤k)) a ⟩
    (f ^ k) P a
  ∎
\end{code}

Appoximations are idempotent in the sense that applying the $k$ and
$j$ approximations in sequence, when $j \leq k$, is equivalent to
just applying the $j$ approximation.

\begin{code}
double-↓ᵒ : ∀{j k} (ϕ : Setᵒ) → j ≤ k → ↓ᵒ k ϕ ≡[ j ] ϕ
double-↓ᵒ {j}{k} ϕ j≤k = ≡ᵒ-intro aux
  where aux : ∀ i → ↓ j (↓ k (# ϕ)) i ⇔ ↓ j (# ϕ) i
        aux zero = (λ _ → tt) , (λ _ → tt)
        aux (suc i) = (λ {(a , b , c) → a , c}) , λ {(a , b) → a , ≤-trans a j≤k , b}
\end{code}

This is a generalization of Lemma 17 of \citet{Appel:2001aa}, in which $j = k - 1$.

\begin{code}
lemma17ᵒ : ∀ k → ↓ᵒ (suc k) ϕ ≡[ k ] ϕ
lemma17ᵒ {ϕ} k = double-↓ᵒ{k}{suc k} ϕ (n≤1+n k)
\end{code}

%===============================================================================
\section{Open Step-Indexed Propositions}
\label{sec:open-propositions}

For the purposes of defining recursive predicates, we need to
introduce variables that can refer to the recursively-bound
predicates. Furthermore, we shall require that each variable occurence
be separated from its binding by at least one ``later'' operator. To
enforce this restriction, we use an explicit representation for
variables. We choose de Bruijn indices that are well typed. That is,
the type of the variable specifies the input type of the predicate.
(For relations, the input type is a product.) So a \textsf{Context}
is a list of types. The metavariable $Γ$ ranges over contexts.

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

These de Bruijn indices are used to access elements in the
environment, which is represented by a tuple of predicates. The
following is the type for such a tuple, with one predicate for each
variable in the context.\footnote{$\mathsf{top}ᵖ$ is how to say
``true`` in $\mathsf{Set}₁$.} 

\begin{code}
RecEnv : Context → Set₁
RecEnv [] = topᵖ 
RecEnv (A ∷ Γ) = (Predᵒ A) × RecEnv Γ
\end{code}

\noindent Let $δ$ range over environments.
\begin{code}
variable δ : RecEnv Γ
\end{code}

\noindent We refer to a function of type $\mathsf{RecEnv}\app Γ → \mathsf{Set}ᵒ$ as a
\emph{environment functional}. Let $F, G, H$ range over environment functionals.
\begin{code}
variable F G H : RecEnv Γ → Setᵒ
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
  [] : Times []
  _∷_ : Time → Times Γ → Times (A ∷ Γ)
\end{code}
Let $Δ$ range over these lists of times.
\begin{code}
variable Δ Δ₁ Δ₂ : Times Γ
\end{code}

We declare another record type, $\mathsf{Set}ˢ$ for open step-indexed
propositions, that is, propositions that may contain free variables.
\begin{code}
record Setˢ (Γ : Context) (Δ : Times Γ) : Set₁
\end{code}
Let $S,T,R$ range over $\mathsf{Set}ˢ$.
\begin{code}
variable S T U : Setˢ Γ Δ
\end{code}

We explain the type system for \textsf{Set}$^s$ in
Figure~\ref{fig:SIL-type-system}.  The membership formula $a ∈ x$ is
well-typed when variable $x$ is bound to a predicate on $A$ in $Γ$,
$a$ has type $A$, and $Δ$ assigns $x$ to $\Now$ and all
the other variables in $Γ$ to $\Later$. We use the function $\varnow$
to express this constraint, which also relies on the
following auxiliary $\laters$ function.
\begin{code}
laters : ∀ (Γ : Context) → Times Γ
laters [] = []
laters (A ∷ Γ) = Later ∷ (laters Γ)

var-now : ∀ (Γ : Context) → ∀{A} → (x : Γ ∋ A) → Times Γ
var-now (B ∷ Γ) zeroˢ = Now ∷ (laters Γ)
var-now (B ∷ Γ) (sucˢ x) = Later ∷ (var-now Γ x)
\end{code}

\noindent There is some redundancy in the type system, for example, in
this rule for membership we could instead simply check that $Δ$ maps
$x$ to $\Now$ and not place any constraints on the other variables.
However, the redundancy helps Agda's inference algorithm when working
with partial proofs.

The later formula $▷ˢ S$ is well-typed at $\laters(Γ)$ when $S$ is
well-typed at $Δ$.
%
The approximation formula $↓ˢ\,k\,S$ is well-typed when $S$ is well-typed.
%
The ``let`` formula $\mathsf{let}ˢ\,Sᵃ\,T$ binds a predicate Sᵃ in the
scope of the body $T$. So it is well-typed in $Γ$ at $Δ$ if
$Sᵃ$ is a predicate over $A$ that is well-typed in $Γ$ at $Δ$ and if the
body $T$ is well-typed in $Γ,A$ at $Δ,\mathsf{Later}$.
%
The recursive formula $μˢ S$ is well-typed in $Γ$ at $Δ$ if $S$ is
well typed in $Γ,A$ at $Δ,\Later$. That is, the variable $\zero$ bound
by the $μˢ$ has type $A$ and may only be used later.

The implication formula $S →ˢ T$ is well-typed in $Γ$ at the combined
times $Δ₁ ∪ Δ₂$ when $S$ is well-typed in $Γ$ at $Δ₁$ and $T$ is
well-typed in $Γ$ at $Δ₂$. We combine lists of times using the
following auxiliary functions. The story is similar for conjunction $S ×ˢ T$
and disjunction $S ⊎ˢ T$. 

\begin{code}
choose : Time → Time → Time
choose Now Now = Now
choose Now Later = Now
choose Later Now = Now
choose Later Later = Later
\end{code}

\begin{code}
_∪_ : ∀{Γ} (Δ₁ Δ₂ : Times Γ) → Times Γ
_∪_ {[]} Δ₁ Δ₂ = []
_∪_ {A ∷ Γ} (x ∷ Δ₁) (y ∷ Δ₂) = choose x y ∷ Δ₁ ∪ Δ₂
\end{code}

The universal and existential quantifiers of SIL use Agda functions,
as one would do in higher-order abstract syntax.  The existential
quantifier requires that the type $A$ be inhabited to obtain the
true-at-zero property. We do not wish this requirement to clutter
every use of the exists quantifier, so we use Agda's support for
instance arguments~\citep{Devriese:2011aa} (an adaptation of type
classes~\citep{hall96:_typeclasses}). So we define the following
record type and use it as an implicit instance argument in the
definition of the existential quantifier.

\begin{code}
record Inhabited (A : Set) : Set where
  field elt : A
open Inhabited {{...}} public
\end{code}

\noindent Of course the natural numbers are inhabited.

\begin{code}
instance
  Inhabited-ℕ : Inhabited ℕ
  Inhabited-ℕ = record { elt = zero }
\end{code}

The constant formula $pˢ$ takes a (non-indexed) proposition $p$ and
turns it into an open step-indexed proposition, so $p$ must have type
$\mathsf{Set}$ and the result is well-typed at $\laters\, Γ$.

\begin{figure}
\raggedright
\fbox{$S : \mathsf{Set}ˢ \, Γ \, Δ$}
\begin{gather*}
\inference{a : A & x : Γ ∋ A}
          {a ∈ x  : \mathsf{Set}ˢ \,Γ \,(\varnow\,Γ\,x)} \quad
\inference{S : \mathsf{Set}ˢ\,Γ\, Δ}
          {▷ˢ S : \mathsf{Set}ˢ \,Γ\,(\laters\,Γ)} \quad
\inference{S : \mathsf{Set}ˢ\, Γ\, Δ}
          {↓ˢ \, k\, S : \mathsf{Set}ˢ\, Γ\, Δ} \\[2ex]
\inference{Sᵃ : A → \mathsf{Set}ˢ\, Γ\, Δ & T : \mathsf{Set}ˢ\, (Γ,A) (Δ, \mathsf{Later})}
          {\mathsf{let}ˢ\, Sᵃ\,T : \mathsf{Set}ˢ\, Γ\, Δ} \quad
\inference{S : \mathsf{Set}ˢ\,(Γ,A)\, (Δ,\mathsf{Later})}
          {μˢ S : \mathsf{Set}ˢ\,Γ\, Δ} \\[2ex]
\inference{S : \mathsf{Set}ˢ\, Γ \, Δ₁  & T : \mathsf{Set}ˢ\,Γ\, Δ₂}
          {S →ˢ T : \mathsf{Set}ˢ\,Γ\, (Δ₁ ∪ Δ₂)} \;\;
\inference{S : \mathsf{Set}ˢ\,Γ\, Δ₁ & T : \mathsf{Set}ˢ\,Γ\, Δ₂}
          {S ×ˢ T : \mathsf{Set}ˢ\,Γ\, (Δ₁ ∪ Δ₂)} \;\;
\inference{S : \mathsf{Set}ˢ\,Γ\, Δ₁ & T : \mathsf{Set}ˢ\,Γ\, Δ₂}
          {S ⊎ˢ T : \mathsf{Set}ˢ\,Γ\, (Δ₁ ∪ Δ₂)} \\[2ex]
\inference{∀ a ∈ A,\, f a : \mathsf{Set}ˢ\,Γ\, Δ}
          {∀ˢ f : \mathsf{Set}ˢ\,Γ\, Δ} \quad
\inference{∀ a ∈ A,\, f a : \mathsf{Set}ˢ\,Γ\, Δ}
          {∃ˢ f : \mathsf{Set}ˢ\,Γ\, Δ} \quad
\inference{}{p ˢ : \mathsf{Set}ˢ\,Γ\, (\laters\,Δ)}
\end{gather*}
\caption{Type System for Open Step-Indexed Logical Formulas}
\label{fig:SIL-type-system}
\end{figure}

The type system is implemented by the type signatures for the logical
operators, which we declare in Figure~\ref{fig:SIL-decl}.

\begin{figure}
\begin{code}
_∈_ : A → (x : Γ ∋ A) → Setˢ Γ (var-now Γ x)

▷ˢ : Setˢ Γ Δ → Setˢ Γ (laters Γ)

↓ˢ : ℕ → Setˢ Γ Δ → Setˢ Γ Δ

letˢ : (A → Setˢ Γ Δ) → Setˢ (A ∷ Γ) (Later ∷ Δ) → Setˢ Γ Δ   

μˢ : (A → Setˢ (A ∷ Γ) (Later ∷ Δ)) → (A → Setˢ Γ Δ)

infixr 6 _→ˢ_
_→ˢ_ : Setˢ Γ Δ₁ → Setˢ Γ Δ₂ → Setˢ Γ (Δ₁ ∪ Δ₂)

infixr 7 _×ˢ_
_×ˢ_ : Setˢ Γ Δ₁ → Setˢ Γ Δ₂ → Setˢ Γ (Δ₁ ∪ Δ₂)

infixr 7 _⊎ˢ_
_⊎ˢ_ : Setˢ Γ Δ₁ → Setˢ Γ Δ₂ → Setˢ Γ (Δ₁ ∪ Δ₂)

∀ˢ : (A → Setˢ Γ Δ) → Setˢ Γ Δ

∃ˢ : {{_ : Inhabited A}} → (A → Setˢ Γ Δ) → Setˢ Γ Δ

_ˢ : Set → Setˢ Γ (laters Γ)
\end{code}
\caption{Declarations of the Open Step-Indexed Formula}
\label{fig:SIL-decl}
\end{figure}

We have declared the type $\mathsf{Set}ˢ$ for open propositions but we
have not yet given its definition. Similar to $\mathsf{Set}ᵒ$ it will
be a record type. Its principal field is an environment functional
(of type $\mathsf{RecEnv}\app Γ → \mathsf{Set}ᵒ$) that represents the meaning
of the formula. The record will also include two properties, that the
functional is congruent and that it is contractive in a sense that is
somewhat involved.

We define the $↓ᵈ$ operator to apply $k$-approximation to one of the
predicates in an environment. The second parameter of $↓ᵈ$, a
variable, specifies which predicate to apply the $k$-approximation.

\begin{code}
↓ᵈ : ℕ → Γ ∋ A → RecEnv Γ → RecEnv Γ
↓ᵈ k zeroˢ (P , δ) = ↓ᵖ k P , δ
↓ᵈ k (sucˢ x) (P , δ) = P , ↓ᵈ k x δ
\end{code}

The semantic conditions that correspond to using the variable for a
recursive predicate now vs. later are the notion of nonexpansive and
contractive of \citet{Appel:2001aa}.  A direct adaptation of
nonexpansive to our setting yields the following, which says that
given any environment $δ$ and variable $x$, the $k$-approximation of
$P\app δ$ is equivalent to the $k$-approximation of $P$ applied to the
$k$ approximation of the $δ$ with respect to variable $x$.
\[
  ↓\, k\, (P\, δ) ≡ᵒ ↓\, k\, (P\, (↓ᵈ\, k\, x\, δ)
\]
Simlarly, the direct adaption of contractive to our setting says
that the $k \plus 1$ approximation of $P\app δ$ is equivalent to the
$k \plus 1$ approximation of $P$ applied to the $k$ approximation of
the $δ$ with respect to variable $x$.
\[
  ↓\, (k \plus 1) \, (P\, δ) ≡ᵒ ↓\, (k \plus 1) \, (P\, (↓ᵈ\, k\, x\, δ)
\]
However, these definitions of nonexpansive and contractive were not
general enough to handle more than one recursive predicate in scope.
(Recall that \citet{Appel:2001aa} neglected to prove that $μ$
preserves nonexpansive and contractive propositions.)  So instead of
taking the $k$-approximation of the input $δ$, we generalize $k$ to
any $j$ greater or equal to $k$, yielding the following notions of
\emph{strongly nonexpansive} and \emph{strongly contractive}
functionals.

\begin{code}
strongly-nonexpansive : (x : Γ ∋ A) → (RecEnv Γ → Setᵒ) → Set₁
strongly-nonexpansive x F = ∀ δ j k → k ≤ j → F δ ≡[ k ] F (↓ᵈ j x δ)

strongly-contractive : (x : Γ ∋ A) → (RecEnv Γ → Setᵒ) → Set₁
strongly-contractive x F = ∀ δ j k → k ≤ j → F δ ≡[ suc k ] F (↓ᵈ j x δ)
\end{code}

\begin{code}
SC⇒SNE : (x : Γ ∋ A) (F : RecEnv Γ → Setᵒ) → strongly-contractive x F → strongly-nonexpansive x F
SC⇒SNE x F SC δ j zero k≤j = ↓ᵒ-zero
SC⇒SNE x F SC δ j (suc k) k≤j = SC δ j k (≤-trans (n≤1+n k) k≤j)
\end{code}

We say that an environment functional $F$ is \emph{strong in variable $x$
at time $t$} if it is either strongly nonexpansive (when $t = \Now$) or
strongly contractive (when $t = \Later$).

\begin{code}
strong-var : (x : Γ ∋ A) → Time → (RecEnv Γ → Setᵒ) → Set₁
strong-var x Now F = strongly-nonexpansive x F
strong-var x Later F = strongly-contractive x F
\end{code}

\noindent Next we define the \textsf{timeof} function to lookup the
time for a variable $x$ in $Δ$.

\begin{code}
timeof : (x : Γ ∋ A) → Times Γ → Time
timeof {B ∷ Γ} zeroˢ (t ∷ Δ) = t
timeof {B ∷ Γ} (sucˢ x) (t ∷ Δ) = timeof x Δ
\end{code}

For convenience, we define the following two elimination principles
for functionals that are strong in a variable. If the variable's time
is \textsf{Now}, then the functional is strongly nonexpansive, and if
the time is \textsf{Later}, then the functional is strongly
contractive.

\begin{code}
strong-now : ∀{x : Γ ∋ A}{Δ : Times Γ}{F : RecEnv Γ → Setᵒ}
   → strong-var x (timeof x Δ) F → timeof x Δ ≡ Now → strongly-nonexpansive x F
strong-now gF eq rewrite eq = gF

strong-later : ∀{x : Γ ∋ A}{Δ : Times Γ}{F : RecEnv Γ → Setᵒ}
   → strong-var x (timeof x Δ) F → timeof x Δ ≡ Later → strongly-contractive x F
strong-later gF eq rewrite eq = gF
\end{code}


\noindent We say that an environment functional is \emph{strong} if it
is strong with respect to every variable that is in scope.

\begin{code}
strong-fun : Times Γ → (RecEnv Γ → Setᵒ) → Set₁
strong-fun {Γ} Δ F = ∀{A} (x : Γ ∋ A) → strong-var x (timeof x Δ) F
\end{code}

\noindent Two environments are equivalent if they are point-wise equivalent.

\begin{code}
_≡ᵈ_ : RecEnv Γ → RecEnv Γ → Set
_≡ᵈ_ {[]} δ δ′ = ⊤
_≡ᵈ_ {A ∷ Γ} (P , δ) (Q , δ′) = (∀ a → P a ≡ᵒ Q a) × δ ≡ᵈ δ′
\end{code}

\noindent Environment equivalence is reflexive.

\begin{code}
≡ᵈ-refl : ∀{Γ}{δ : RecEnv Γ} → δ ≡ᵈ δ
≡ᵈ-refl {[]} {δ} = tt
≡ᵈ-refl {A ∷ Γ} {(P , δ)} = (λ a → ≡ᵒ-refl refl) , ≡ᵈ-refl
\end{code}

\noindent A functional is congruent if applying it to equivalent
environments produces equivalent step-indexed propositions.

\begin{code}
congruent : (RecEnv Γ → Setᵒ) → Set₁
congruent f = ∀{δ δ′} → δ ≡ᵈ δ′ → (f δ) ≡ᵒ (f δ′)
\end{code}

We define $\mathsf{Set}ˢ$ as the following record type.  The meaning
of the open step-indexed logical formula is given by an environment
functional and we require proofs that the functional is strong and
congruent.

\begin{code}
record Setˢ Γ Δ where
  field
    ♯ : RecEnv Γ → Setᵒ 
    strong : strong-fun Δ ♯
    congr : congruent ♯
open Setˢ public
\end{code}


\subsection{Equivalence for Open Step-Indexed Formulas}

We define two open step-indexed formulas to be equivalent if their
applications to the same environment are equivalent.

\begin{code}
abstract
  infix 2 _≡ˢ_
  _≡ˢ_ : Setˢ Γ Δ → Setˢ Γ Δ → Set₁
  S ≡ˢ T = ∀ δ → ♯ S δ ≡ᵒ ♯ T δ

  ≡ˢ-intro : (∀ δ → ♯ S δ ≡ᵒ ♯ T δ) → S ≡ˢ T
  ≡ˢ-intro S=T eq δ = S=T eq δ

  ≡ˢ-elim : S ≡ˢ T → (∀ δ → ♯ S δ ≡ᵒ ♯ T δ)
  ≡ˢ-elim S=T δ = S=T δ

  ≡ˢ-refl : S ≡ T → S ≡ˢ T
  ≡ˢ-refl{S = S}{T} refl δ = ≡ᵒ-refl{♯ S δ}{♯ T δ} refl

  ≡ˢ-sym : S ≡ˢ T → T ≡ˢ S
  ≡ˢ-sym{S = S}{T} ST δ = ≡ᵒ-sym{♯ S δ}{♯ T δ} (ST δ)

  ≡ˢ-trans : S ≡ˢ T → T ≡ˢ U → S ≡ˢ U
  ≡ˢ-trans{S = S}{T}{U} ST TU δ = ≡ᵒ-trans{♯ S δ}{♯ T δ}{♯ U δ} (ST δ) (TU δ)
  
instance
  SIL-Eqˢ : EquivalenceRelation (Setˢ Γ Δ)
  SIL-Eqˢ = record { _⩦_ = _≡ˢ_ ; ⩦-refl = ≡ˢ-refl ; ⩦-sym = ≡ˢ-sym ; ⩦-trans = ≡ˢ-trans }
\end{code}

In the following subsections we define the logic operators that are
declared in Figure~\ref{fig:SIL-decl}. We start with the logical
operators for membership, later, approximation, and let. We then dive
into the most difficult case, of recursive predicates. After that we
define the logical opereators from first-order logic.

\subsection{Membership}

The following \textsf{lookup} function retrieves from the environment
the predicate associated with a particular variable.

\begin{code}
lookup : Γ ∋ A → RecEnv Γ → Predᵒ A
lookup zeroˢ (P , δ) = P
lookup (sucˢ x) (P , δ) = lookup x δ
\end{code}

The lemma $\mathsf{double}\mbox{-}↓$ that we proved in
Section~\ref{sec:fun-approx-iter} generalizes to the \textsf{lookup}
function as follows.

\begin{code}
↓-lookup : ∀{a}{k j}{δ : RecEnv Γ} (x : Γ ∋ A) (y : Γ ∋ B) → k ≤ j
   → lookup{Γ}{A} x δ a ≡[ k ] lookup{Γ}{A} x (↓ᵈ j y δ) a
↓-lookup {a = a}{δ = P , δ} zeroˢ zeroˢ k≤j = ≡ᵒ-sym (double-↓ᵒ (P a) k≤j)
↓-lookup zeroˢ (sucˢ y) k≤j = ≡ᵒ-refl refl
↓-lookup (sucˢ x) zeroˢ k≤j = ≡ᵒ-refl refl
↓-lookup (sucˢ x) (sucˢ y) k≤j = ↓-lookup x y k≤j
\end{code}

Approximating an environment δ with respect to variable $y$ does not
change the result of lookup for any other variable $x$. Because
$x$ and $y$ have different types, it is not convenient in Agda to
compare them directly, so we instead compare their times in Δ.

\begin{code}
lookup-diff : ∀{Γ}{Δ : Times Γ}{A}{B}{δ : RecEnv Γ}{j} (x : Γ ∋ A) (y : Γ ∋ B) → timeof x Δ ≢ timeof y Δ
   → lookup{Γ}{A} x (↓ᵈ j y δ) ≡ lookup{Γ}{A} x δ
lookup-diff {C ∷ Γ} {t ∷ Δ} zeroˢ zeroˢ neq = ⊥-elim (neq refl)
lookup-diff {C ∷ Γ} {t ∷ Δ} zeroˢ (sucˢ y) neq = refl
lookup-diff {C ∷ Γ} {t ∷ Δ} (sucˢ x) zeroˢ neq = refl
lookup-diff {C ∷ Γ} {t ∷ Δ} (sucˢ x) (sucˢ y) neq = lookup-diff x y neq
\end{code}

The time of a variable $x$ is \textsf{Now} in the list of times
produced by $\varnow\,Γ\,x$.

\begin{code}
timeof-var-now : ∀{Γ}{A} → (x : Γ ∋ A) → timeof x (var-now Γ x) ≡ Now
timeof-var-now {B ∷ Γ} zeroˢ = refl
timeof-var-now {B ∷ Γ} (sucˢ x) = timeof-var-now x
\end{code}

The time of a variable $x$ is \textsf{Later} in the list of times
produced by $\laters(Γ)$.

\begin{code}
timeof-later : ∀{Γ}{A} (x : Γ ∋ A) → (timeof x (laters Γ)) ≡ Later
timeof-later {B ∷ Γ} zeroˢ = refl
timeof-later {B ∷ Γ} (sucˢ x) = timeof-later x
\end{code}

The \textsf{lookup} function for a given variable $x$ is a strong
functional when the list of times Δ is the result of
$\varnow\,Γ\,x$. The time of $x$ in $\varnow\,Γ\,x$ is \textsf{Now},
so it suffices to prove that \textsf{lookup} is strongly nonexpansive
in $x$ and strongly contractive in the other variables, which we show
in Figure~\ref{fig:strong-lookup}.

\begin{figure}[tbp]
\small
\begin{code}
strong-lookup : ∀{Γ}{A}{a} → (x : Γ ∋ A) → strong-fun (var-now Γ x) (λ δ → lookup x δ a)
strong-lookup {.(A ∷ _)} {A} {a} zeroˢ zeroˢ = SNE where
  SNE : strongly-nonexpansive zeroˢ (λ {(P , δ) → P a})
  SNE (P , δ) j k k≤j = ≡ᵒ-sym (double-↓ᵒ (P a) k≤j)
strong-lookup {.(A ∷ _)} {A} {a} zeroˢ (sucˢ y) rewrite timeof-later y = SC where
  SC : strongly-contractive (sucˢ y) (λ {(P , δ) → P a})
  SC (P , δ) j k k≤j = ≡ᵒ-refl refl
strong-lookup {.(_ ∷ _)} {A} {a} (sucˢ x) zeroˢ = SC where
  SC : strongly-contractive zeroˢ (λ (P , δ) → lookup x δ a)
  SC (P , δ) j k k≤j = ≡ᵒ-refl refl
strong-lookup {B ∷ Γ} {A} {a} (sucˢ x) (sucˢ y)
    with timeof y (var-now Γ x) in eq-y
... | Now = SNE where
    SNE : strongly-nonexpansive (sucˢ y) (λ {(P , δ) → lookup x δ a})
    SNE (P , δ) j k k≤j = ↓-lookup x y k≤j 
... | Later = SC where
    timeof-diff : ∀{Γ}{Δ : Times Γ}{A}{B} (x : Γ ∋ A) (y : Γ ∋ B) → timeof x Δ ≡ Now → timeof y Δ ≡ Later
       → timeof x Δ ≢ timeof y Δ
    timeof-diff x y eq1 eq2 rewrite eq1 | eq2 = λ ()
    SC : strongly-contractive (sucˢ y) (λ {(P , δ) → lookup x δ a})
    SC (P , δ) j k k≤j =
      let eq = (lookup-diff{Γ}{δ = δ}{j} x y (timeof-diff x y (timeof-var-now x) eq-y)) in
      subst (λ X → (lookup x δ a) ≡[ suc k ] (X a)) (sym eq) (≡ᵒ-refl refl)
\end{code}
\caption{The variable \textsf{lookup} function is a strong environment functional.}
\label{fig:strong-lookup}
\end{figure}

The \textsf{lookup} function for a variable $x$ is congruent. That is,
given two equivalent environments, \textsf{lookup} produces equivalent
predicates.

\begin{code}
congruent-lookup : ∀ (x : Γ ∋ A) (a : A) → congruent (λ δ → lookup x δ a)
congruent-lookup x a d=d′ = aux x a d=d′
  where
  aux : ∀{Γ}{A}{δ δ′ : RecEnv Γ} (x : Γ ∋ A) (a : A) → δ ≡ᵈ δ′ → lookup x δ a ≡ᵒ lookup x δ′ a
  aux {B ∷ Γ} {.B}{P , δ}{P′ , δ′} zeroˢ a (P=P′ , d=d′) = P=P′ a
  aux {B ∷ Γ} {A}{P , δ}{P′ , δ′} (sucˢ x) a (P=P′ , d=d′) = aux x a d=d′
\end{code}

We conclude by constructing the \textsf{Set}ˢ record for the predicate
membership formula as follows.

\begin{code}
a ∈ x = record { ♯ = λ δ → (lookup x δ) a ; strong = strong-lookup x ; congr = congruent-lookup x a }
\end{code}

\subsection{Later}

Next we come to the later formula. We first define a closed variant of
the operator, written $▷ᵒ ϕ$, and then define the open formula $▷ˢ S$.
The following is the definition for $▷ᵒ ϕ$, with the meaning of the
formula given by the \texttt{\#} field. Of course, at zero, $▷ᵒ ϕ$ is
true. For any other index $\mathsf{suc}\app k$, $▷ᵒ ϕ$ means $ϕ$ is
true at $k$, that is, subtract one from the step index.  So we
construct the record for $▷ᵒ ϕ$ as follows, proving in-line that it is
downward closed and true-at-zero.

\begin{code}
▷ᵒ_ : Setᵒ → Setᵒ
▷ᵒ ϕ = record { # = λ { zero → ⊤ ; (suc k) → # ϕ k }
              ; down = λ { zero ▷ϕn .zero z≤n → tt
                         ; (suc n) ▷ϕn .zero z≤n → tt
                         ; (suc n) ▷ϕn (suc k) (s≤s k≤n) → down ϕ n ▷ϕn k k≤n}
              ; tz = tt }
\end{code}

To construct the record for the open formula $▷ˢ S$, we need to show
that $▷ˢ$ is strong and congruent. We begin by showing that $▷ᵒ$ is
congruent becuase it turns out that this fact is need to show that
$▷ˢ$ is strong.

\begin{code}
cong-▷ : ϕ ≡ᵒ ψ → ▷ᵒ ϕ ≡ᵒ ▷ᵒ ψ
cong-▷ {ϕ}{ψ} ϕ=ψ = ≡ᵒ-intro aux
  where aux : ∀ i → #(▷ᵒ ϕ) i ⇔ #(▷ᵒ ψ) i
        aux zero = (λ _ → tt) , (λ _ → tt)
        aux (suc i) = (λ ϕi → ⇔-to (≡ᵒ-elim ϕ=ψ) ϕi) , (λ ψi → ⇔-fro (≡ᵒ-elim ϕ=ψ) ψi)
\end{code}

The operator $▷ᵒ$ is also contractive.

\begin{code}
WF-▷ : ∀{k} (S : Setᵒ) → ▷ᵒ S ≡[ suc k ] ▷ᵒ (↓ᵒ k S)
WF-▷ {k} S = ≡ᵒ-intro aux
  where aux : ∀ i → #(↓ᵒ (suc k) (▷ᵒ S)) i ⇔ #(↓ᵒ (suc k) (▷ᵒ (↓ᵒ k S))) i
        aux zero = (λ _ → tt) , (λ _ → tt)
        aux 1 = (λ {(si<sk , Si) → si<sk , tt}) , λ {(1<sk , _) → 1<sk , tz S}
        aux (suc (suc i)) = (λ {(s≤s i≤1+k , ▷Si) → s≤s i≤1+k , i≤1+k , ▷Si})
                            , (λ {(i≤1+k , (_ , ▷Si)) → i≤1+k , ▷Si})
\end{code}

The operator $▷ᵒ$ is a strong environment functional, which we prove in
Figure~\ref{fig:strong-later}. In addition to using the above two lemmas,
the proof also relies on \textsf{lemma17}.

\begin{figure}[tbp]
\small
\begin{code}
strong-▷ : (S : Setˢ Γ Δ) → strong-fun (laters Γ) (λ δ → ▷ᵒ (♯ S δ))
strong-▷ {Γ}{Δ} S x
    with strong S x
... | strongS
    with timeof x Δ
... | Now rewrite timeof-later{Γ} x = λ δ j k k≤j →
      ▷ᵒ (♯ S δ)
    ⩦⟨ WF-▷ {k} (♯ S δ) ⟩ 
      ▷ᵒ (↓ᵒ k (♯ S δ))
    ⩦⟨ cong-↓ᵒ (suc k) (cong-▷ (strongS δ j k k≤j)) ⟩ 
      ▷ᵒ (↓ᵒ k (♯ S (↓ᵈ j x δ)))
    ⩦⟨ ≡ᵒ-sym (WF-▷ {k} (♯ S (↓ᵈ j x δ))) ⟩ 
      ▷ᵒ (♯ S (↓ᵈ j x δ))
    ∎
... | Later rewrite timeof-later{Γ} x = λ δ j k k≤j →
      ▷ᵒ (♯ S δ)
    ⩦⟨ ≡ᵒ-sym (lemma17ᵒ (suc k)) ⟩ 
      ↓ᵒ (2 + k) (▷ᵒ (♯ S δ))
    ⩦⟨ cong-↓ᵒ (suc k) (WF-▷ _) ⟩
      ↓ᵒ (2 + k) (▷ᵒ (↓ᵒ (suc k) (♯ S δ)))
    ⩦⟨ cong-↓ᵒ (suc k) (cong-↓ᵒ (suc (suc k)) (cong-▷ (strongS δ j k k≤j))) ⟩
      ↓ᵒ (2 + k) (▷ᵒ (↓ᵒ (suc k) (♯ S (↓ᵈ j x δ))))
    ⩦⟨ ≡ᵒ-sym (cong-↓ᵒ (suc k) (WF-▷ _)) ⟩
      ↓ᵒ (2 + k) (▷ᵒ (♯ S (↓ᵈ j x δ)))
    ⩦⟨ lemma17ᵒ (suc k) ⟩
      ▷ᵒ (♯ S (↓ᵈ j x δ))
    ∎
\end{code}
\caption{The later operator is a strong environment functional.}
\label{fig:strong-later}
\end{figure}

We conclude by defining the record for the $▷ˢ$ formula of SIL.

\begin{code}
▷ˢ S = record { ♯ = λ δ → ▷ᵒ (♯ S δ) ; strong = strong-▷ S ; congr = λ d=d′ → cong-▷ (congr S d=d′) }
\end{code}


\subsection{Approximation}

We have already defined a closed variant of $k$-approximation, written
$↓ᵒ$, and we have proved that it is congruent. So it remains to show
that $↓ᵒ$ is a strong environment functional. For that we need the
following lemma that permutes two uses of approximation.

\begin{code}
permute-↓ : ∀{S : Setᵒ}{j}{k} → ↓ᵒ k (↓ᵒ j S) ≡ᵒ ↓ᵒ j (↓ᵒ k S)
permute-↓ {S} {j} {k} = ≡ᵒ-intro aux
  where aux : ∀ i → #(↓ᵒ k (↓ᵒ j S)) i ⇔ #(↓ᵒ j (↓ᵒ k S)) i
        aux zero = (λ _ → tt) , (λ _ → tt)
        aux (suc i) = (λ {(x , (y , z)) → y , x , z}) , λ {(x , (y , z)) → y , x , z}
\end{code}

The fact that $↓ᵒ$ is strong follows from this permutation lemma and
from $↓ᵒ$ being congruent, as shown in Figure~\ref{fig:strong-approx}.

\begin{figure}[tbp]
\small
\begin{code}
strong-↓ : ∀{Γ}{Δ : Times Γ}{i} (S : Setˢ Γ Δ) → strong-fun Δ (λ δ → ↓ᵒ i (♯ S δ))
strong-↓ {Γ}{Δ}{i} S {A} x
    with timeof x Δ in time-x
... | Now = λ δ j k k≤j → 
    let strongS = strong-now (strong S x) time-x δ j k k≤j in
      ↓ᵒ k (↓ᵒ i (♯ S δ))
    ⩦⟨ permute-↓  ⟩ 
      ↓ᵒ i (↓ᵒ k (♯ S δ))
    ⩦⟨ cong-↓ᵒ i strongS ⟩ 
      ↓ᵒ i (↓ᵒ k (♯ S (↓ᵈ j x δ)))
    ⩦⟨ permute-↓ ⟩
      ↓ᵒ k (↓ᵒ i (♯ S (↓ᵈ j x δ)))
    ∎
... | Later = λ δ j k k≤j →
    let strongS = strong-later (strong S x) time-x δ j k k≤j in
      ↓ᵒ (suc k) (↓ᵒ i (♯ S δ))
    ⩦⟨ permute-↓  ⟩ 
      ↓ᵒ i (↓ᵒ (suc k) (♯ S δ))
    ⩦⟨ cong-↓ᵒ i strongS ⟩ 
      ↓ᵒ i (↓ᵒ (suc k) (♯ S (↓ᵈ j x δ)))
    ⩦⟨ permute-↓ ⟩
      ↓ᵒ (suc k) (↓ᵒ i (♯ S (↓ᵈ j x δ)))
    ∎
\end{code}
\caption{The $k$-approximation operator is a strong environment functional.}
\label{fig:strong-approx}
\end{figure}

To conclude, we construct $↓ˢ\,k\,S$ with the following record.

\begin{code}
↓ˢ k S = record { ♯ = λ δ → ↓ᵒ k (♯ S δ) ; strong = strong-↓ S
                ; congr = λ d=d′ → cong-↓ᵒ k (congr S d=d′)}
\end{code}


\subsection{Let}

The meaning of the $\mathsf{let}ˢ\,Sᵃ\,T$ formula is the meaning of its body $T$
where the zero variable is bound to the predicate $Sᵃ$. The proof that
$\mathsf{let}ˢ$ is a strong environment functional is somewhat involved,
and given in Figure~\ref{fig:strong-let}. The proof relies on \textsf{lemma17}.

\begin{figure}[tbp]
\small
\begin{code}
strong-let : ∀{Γ}{Δ : Times Γ}{A} (T : Setˢ (A ∷ Γ) (Later ∷ Δ)) (Sᵃ : A → Setˢ Γ Δ)
   → strong-fun Δ (λ δ → ♯ T ((λ a → ♯ (Sᵃ a) δ) , δ))
strong-let {Γ}{Δ}{A} T Sᵃ x
   with timeof x Δ in time-x
... | Now = λ δ j k k≤j →
    let strongTz = ((strong T) zeroˢ) ((λ a → ♯ (Sᵃ a) δ) , δ) j k k≤j in
    let strongTz2 = ((strong T) zeroˢ) ((λ a → ♯ (Sᵃ a) (↓ᵈ j x δ)) , (↓ᵈ j x δ))
                   j k k≤j in
    let strongTsx = strong-now{x = sucˢ x}{Δ = Now ∷ Δ} ((strong T) (sucˢ x)) time-x
                 ((λ a → ↓ᵒ j (♯ (Sᵃ a) δ)) , δ) j k k≤j in
    let EQ : ((λ a → ↓ᵒ j (♯ (Sᵃ a) δ)) , ↓ᵈ j x δ)
          ≡ᵈ ((λ a → ↓ᵒ j  (♯ (Sᵃ a) (↓ᵈ j x δ))) , ↓ᵈ j x δ)
        EQ = (λ a → strong-now (strong (Sᵃ a) x) time-x δ j j ≤-refl) , ≡ᵈ-refl in
      ♯ T ((λ a → ♯ (Sᵃ a) δ) , δ)
    ⩦⟨ ≡ᵒ-sym (lemma17ᵒ k) ⟩
      ↓ᵒ (suc k) (♯ T ((λ a → ♯ (Sᵃ a) δ) , δ))
    ⩦⟨ cong-↓ᵒ k strongTz ⟩
      ↓ᵒ (suc k) (♯ T ((λ a → ↓ᵒ j (♯ (Sᵃ a) δ)) , δ))
    ⩦⟨ lemma17ᵒ k ⟩
      ♯ T ((λ a → ↓ᵒ j (♯ (Sᵃ a) δ)) , δ)
    ⩦⟨ strongTsx ⟩
      ♯ T ((λ a → ↓ᵒ j (♯ (Sᵃ a) δ)) , ↓ᵈ j x δ)
    ⩦⟨ cong-↓ᵒ k (congr T EQ) ⟩
      ♯ T ((λ a → ↓ᵒ j (♯ (Sᵃ a) (↓ᵈ j x δ))) , ↓ᵈ j x δ)
    ⩦⟨ ≡ᵒ-sym (lemma17ᵒ k) ⟩
      ↓ᵒ (suc k) (♯ T ((λ a → ↓ᵒ j (♯ (Sᵃ a) (↓ᵈ j x δ))) , ↓ᵈ j x δ))
    ⩦⟨ cong-↓ᵒ k (≡ᵒ-sym strongTz2) ⟩
      ↓ᵒ (suc k) (♯ T ((λ a → ♯ (Sᵃ a) (↓ᵈ j x δ)) , ↓ᵈ j x δ))
    ⩦⟨ lemma17ᵒ k ⟩
      ♯ T ((λ a → ♯ (Sᵃ a) (↓ᵈ j x δ)) , ↓ᵈ j x δ)
    ∎
... | Later = λ δ j k k≤j →
    let strongTz = ((strong T) zeroˢ) ((λ a → ♯ (Sᵃ a) δ) , δ) (suc j) k (≤-trans k≤j (n≤1+n _)) in
    let strongTz2 = ((strong T) zeroˢ) (((λ a → ♯ (Sᵃ a) (↓ᵈ j x δ))) , δ) (suc j) k (≤-trans k≤j (n≤1+n _)) in
    let EQ : ((λ a → ↓ᵒ (suc j) (♯ (Sᵃ a) δ)) , δ) ≡ᵈ ((λ a → ↓ᵒ (suc j)  (♯ (Sᵃ a) (↓ᵈ j x δ))) , δ)
        EQ = (λ a → strong-later (strong (Sᵃ a) x) time-x δ j j ≤-refl) , ≡ᵈ-refl in
    let strongTsx = strong-later{x = sucˢ x}{Δ = Now ∷ Δ} ((strong T) (sucˢ x)) time-x
                 ((λ a → ♯ (Sᵃ a) (↓ᵈ j x δ)) , δ) j k k≤j in
      ♯ T ((λ a → ♯ (Sᵃ a) δ) , δ)
    ⩦⟨ strongTz ⟩
      ♯ T (↓ᵖ (suc j) (λ a → ♯ (Sᵃ a) δ) , δ)
    ⩦⟨ cong-↓ᵒ (suc k) (congr T EQ) ⟩
      ♯ T (↓ᵖ (suc j) (λ a → ♯ (Sᵃ a) (↓ᵈ j x δ)) , δ)
    ⩦⟨ ≡ᵒ-sym strongTz2 ⟩
      ♯ T ((λ a → ♯ (Sᵃ a) (↓ᵈ j x δ)) , δ)
    ⩦⟨ strongTsx ⟩
      ♯ T ((λ a → ♯ (Sᵃ a) (↓ᵈ j x δ)) , ↓ᵈ j x δ)
    ∎
\end{code}
\caption{The \textsf{let}ˢ operator is a strong environment functional.}
\label{fig:strong-let}
\end{figure}

We define $\mathsf{let}ˢ\,Sᵃ\,T$ by constructing the following record.

\begin{code}
letˢ Sᵃ T = record { ♯ = λ δ → (♯ T) ((λ a → ♯ (Sᵃ a) δ) , δ) ; strong = strong-let T Sᵃ
                   ; congr = λ d=d′ → congr T ((λ a → congr (Sᵃ a) d=d′) , d=d′) }
\end{code}

\subsection{Recursive Predicates and the Fixpoint Theorem}

As mentioned previously, we use iteration to define recursive
predicates. We begin this process by defining an auxilliary function
$μᵖ$ that takes a functional $f$ and produces a raw step-indexed
predicate (without the proofs). It iterates the function $k \plus 1$
times, starting at the always true predicate as follows.

\begin{code}
μᵖ : (Predᵒ A → Predᵒ A) → A → (ℕ → Set)
μᵖ f a k = #((f ^ (1 + k)) (λ a → ⊤ᵒ) a) k
\end{code}

Recall that the body $Sᵃ$ of a $μˢ Sᵃ$ has type
\[
    A → \mathsf{Set}ˢ (A ∷ Γ) (\mathsf{cons}\, \Later\, Δ))
    \text{ and not } \mathsf{Pred}ᵒ A → \mathsf{Pred}ᵒ A.
\]
So we define the following function to convert from the former to the later.

\begin{code}
⟅_⟆ : (A → Setˢ (A ∷ Γ) (Later ∷ Δ)) → RecEnv Γ → (Predᵒ A → Predᵒ A)
⟅ Sᵃ ⟆  δ μS = λ a → ♯ (Sᵃ a) (μS , δ)
\end{code}

\subsubsection{μᵖ is downward closed}

Our first goal is to prove that μᵖ is downward closed in the following sense.

\begin{code}
down-μᵖ : ∀{Sᵃ : A → Setˢ (A ∷ Γ) (Later ∷ Δ)} {a : A}{δ : RecEnv Γ}
  → downClosed (μᵖ (⟅ Sᵃ ⟆ δ) a)
\end{code}

\noindent The proof relies on \textsf{lemma15b}, but applies it to a
functional obtained by \textsf{env}-\textsf{fun}⇒\textsf{fun}.  So we
need to prove that such a functional is contractive and congruent.
The fact that $\eff{Sᵃ} δ$ is contractive is a direct consequence of
$Sᵃ\app a$ being strong.

\begin{code}
wf-env-fun : ∀ (δ : RecEnv Γ) (Sᵃ : A → Setˢ (A ∷ Γ) (Later ∷ Δ)) → contractiveᵖ (⟅ Sᵃ ⟆ δ)
wf-env-fun δ Sᵃ = λ a P k → strong (Sᵃ a) zeroˢ (P , δ) k k ≤-refl
\end{code}

\noindent Similarly, $\eff{Sᵃ}\,δ$ is congruent because $Sᵃ\app a$ is congruent.

\begin{code}
cong-env-fun : ∀ (δ : RecEnv Γ) (Sᵃ : A → Setˢ (A ∷ Γ) (Later ∷ Δ))
   → congruentᵖ (⟅ Sᵃ ⟆ δ)
cong-env-fun δ Sᵃ = λ P=Q a → congr (Sᵃ a) (P=Q , ≡ᵈ-refl{_}{δ})
\end{code}

\noindent So we have the following adaptation of \textsf{lemma15b}.

\begin{code}
lemma15b-env-fun : ∀(k j : ℕ) (Sᵃ : A → Setˢ (A ∷ Γ) (Later ∷ Δ)) (a : A) → j ≤ k
  → ((⟅ Sᵃ ⟆ δ) ^ j) P a ≡[ j ] ((⟅ Sᵃ ⟆ δ) ^ k) P a
lemma15b-env-fun{δ = δ} k j Sᵃ a j≤k =
  lemma15b k j (⟅ Sᵃ ⟆ δ) a j≤k (wf-env-fun δ Sᵃ) (cong-env-fun δ Sᵃ)
\end{code}

The one other fact we need to prove that $μᵖ$ is downward closed is
that \textsf{iter} is downward closed when applied to a functional.

\begin{code}
dc-iter : ∀(i : ℕ){A} (F : Predᵒ A → Predᵒ A) → ∀ a → downClosed (#((F ^ i) ⊤ᵖ a))
dc-iter zero F = λ a n _ k _ → tt
dc-iter (suc i) F = λ a → down (F ((F ^ i) ⊤ᵖ) a)
\end{code}

\noindent We now prove that the $μᵖ$ function is downward closed when
applied to the result of $\eff{Sᵃ}$.

\begin{code}
down-μᵖ {Sᵃ = Sᵃ}{a}{δ} k iterskSᵃk zero j≤k = tz (⟅ Sᵃ ⟆ δ (id ⊤ᵖ) a)
down-μᵖ {Sᵃ = Sᵃ}{a}{δ} (suc k′) μSᵃa (suc j′) (s≤s j′≤k′) =
  let dc-iter-ssk : downClosed (# ((((⟅ Sᵃ ⟆ δ) ^ (2 + k′)) ⊤ᵖ) a))
      dc-iter-ssk = dc-iter (2 + k′) (⟅ Sᵃ ⟆ δ) a in
  let ↓-iter-ssk : #(↓ᵒ (2 + j′) ((((⟅ Sᵃ ⟆ δ) ^ (2 + k′)) ⊤ᵖ) a))(suc j′)
      ↓-iter-ssk = ≤-refl , (dc-iter-ssk (suc k′) μSᵃa (suc j′) (s≤s j′≤k′)) in
  let eq : ((((⟅ Sᵃ ⟆ δ) ^ (2 + j′)) ⊤ᵖ) a)  ≡[ 2 + j′ ]  ((((⟅ Sᵃ ⟆ δ) ^ (2 + k′)) ⊤ᵖ) a)
      eq = lemma15b-env-fun {δ = δ} (2 + k′) (2 + j′) Sᵃ a (s≤s (s≤s j′≤k′)) in
  let ↓-iter-ssj : #(↓ᵒ (2 + j′) ((((⟅ Sᵃ ⟆ δ) ^ (2 + j′)) ⊤ᵖ) a)) (suc j′)
      ↓-iter-ssj = ⇔-to (≡ᵒ-elim (≡ᵒ-sym eq)) ↓-iter-ssk in
  proj₂ ↓-iter-ssj
\end{code}

With these proofs complete, we can use μᵖ to define another auxilliary
function, \textsf{mu}ᵒ, that builds a \textsf{Set}ᵒ record given a
predicate into \textsf{Set}ˢ, an environment, and an element of $A$.

\begin{code}
muᵒ : (A → Setˢ (A ∷ Γ) (Later ∷ Δ)) → RecEnv Γ → A → Setᵒ
muᵒ Sᵃ δ a = record { # = μᵖ (⟅ Sᵃ ⟆ δ) a ; down = down-μᵖ {Sᵃ = Sᵃ}
                    ; tz = tz (⟅ Sᵃ ⟆ δ ⊤ᵖ a) }
\end{code}

\subsubsection{\textsf{mu}ᵒ is a strong environment functional}

Next we need to prove that \textsf{mu}ᵒ is a strong environment
functional. The proof involves three technical lemmas that we adapt from
\citet{Appel:2001aa}.

The first, \textsf{lemma18a} (Figure~\ref{fig:lemma18a}), shows that
$\mathsf{mu}ᵒ\, Sᵃ\, δ\, a$ is equivalent to the $k$ iteration of
$\eff{Sᵃ}\, δ$ under $k$-approximation. 
%
The second, \textsf{lemma18b} (Figure~\ref{fig:lemma18b}), shows that one unrolling of the
recursion is equivalent to $k \plus 1$ iterations of $\eff{Sᵃ}\, δ$,
under $k\plus 1$-approximation.
%
The third, \textsf{lemma19a} (Figure~\ref{fig:lemma19a}), shows that
one unrolling of the recursive predicate is equivalent to the
recursive predicate under $k$-approximation.

\begin{figure}[tbp]
\small
\begin{code}
abstract
  lemma18a : ∀ (k : ℕ) (Sᵃ : A → Setˢ (A ∷ Γ) (Later ∷ Δ)) (a : A) (δ : RecEnv Γ)
     → muᵒ Sᵃ δ a ≡[ k ] ((⟅ Sᵃ ⟆ δ) ^ k) ⊤ᵖ a
  lemma18a zero Sᵃ a δ zero = (λ x → tt) , (λ {x → tt})
  lemma18a zero Sᵃ a δ (suc j) = (λ {()}) , λ {()}
  lemma18a (suc k) Sᵃ a δ zero = (λ {x → tt}) , λ {x → tt}
  lemma18a (suc k′) Sᵃ a δ (suc j′) =
      ↓ (suc k′) (λ j₁ → # ((⟅ Sᵃ ⟆ δ) (((⟅ Sᵃ ⟆ δ) ^ j₁)  ⊤ᵖ) a) j₁) (suc j′)
    ⩦⟨ ⩦-refl refl ⟩    
      (suc j′) < (suc k′)  ×  # (((⟅ Sᵃ ⟆ δ) ^ (suc (suc j′))) ⊤ᵖ a) (suc j′)
    ⩦⟨ (λ {(s≤s x , y) → s≤s x , ≤-refl , y}) , (λ {(s≤s x , (y , z)) → (s≤s x) , z}) ⟩
      (suc j′) < (suc k′)  ×  # (↓ᵒ (suc (suc j′)) (((⟅ Sᵃ ⟆ δ) ^ (suc (suc j′))) ⊤ᵖ a)) (suc j′)
    ⩦⟨ EQ  ⟩    
      (suc j′) < (suc k′)  ×  # (↓ᵒ (suc (suc j′)) (((⟅ Sᵃ ⟆ δ) ^ (suc k′)) ⊤ᵖ a)) (suc j′)
    ⩦⟨ (λ {(s≤s x , (s≤s y , z)) → (s≤s x) , z}) , (λ {(x , y) → x , (≤-refl , y)})  ⟩
      (suc j′) < (suc k′)  ×  # (((⟅ Sᵃ ⟆ δ) ^ (suc k′)) ⊤ᵖ a) (suc j′)
    ⩦⟨ ⩦-refl refl  ⟩    
      ↓ (suc k′) (# (((⟅ Sᵃ ⟆ δ) ^ (suc k′)) ⊤ᵖ a)) (suc j′)
    ∎
    where
    EQ : ((suc j′) < (suc k′)  ×  # (↓ᵒ (suc (suc j′)) (((⟅ Sᵃ ⟆ δ) ^ (suc (suc j′))) ⊤ᵖ a)) (suc j′))
         ⇔ ((suc j′) < (suc k′)  ×  # (↓ᵒ (suc (suc j′)) (((⟅ Sᵃ ⟆ δ) ^ (suc k′)) ⊤ᵖ a)) (suc j′))
    EQ = (λ {(s≤s x , y) →
           let xx = proj₁ ((lemma15b-env-fun (suc k′) (suc (suc j′)) Sᵃ a (s≤s x)) (suc j′)) y in
           (s≤s x) , (≤-refl , proj₂ xx)})
       , (λ {(s≤s x , (s≤s y , z)) →
           let xx = proj₂ ((lemma15b-env-fun(suc k′)(suc (suc j′)) Sᵃ a (s≤s x)) (suc j′)) (≤-refl , z) in
           s≤s x , (≤-refl , (proj₂ xx))})
\end{code}
\caption{$\mathsf{mu}ᵒ\, Sᵃ\, δ\, a$ is equivalent to the $k$ iteration of
 $\eff{Sᵃ}\, δ$ under $k$-approximation.}
\label{fig:lemma18a}
\end{figure}


\begin{figure}[tbp]
\small 
\begin{code}
lemma18b : ∀ (k : ℕ) (Sᵃ : A → Setˢ (A ∷ Γ) (Later ∷ Δ)) (a : A) (δ : RecEnv Γ)
     → ♯ (Sᵃ a) (muᵒ Sᵃ δ , δ) ≡[ 1 + k ] ((⟅ Sᵃ ⟆ δ) ^ (1 + k)) ⊤ᵖ a
lemma18b {A}{Γ}{Δ} k Sᵃ a δ =
       ♯ (Sᵃ a) (muᵒ Sᵃ δ , δ)
   ⩦⟨ strong (Sᵃ a) zeroˢ (muᵒ Sᵃ δ , δ) k k ≤-refl ⟩
       ♯ (Sᵃ a) (↓ᵖ k (muᵒ Sᵃ δ) , δ)
   ⩦⟨ cong-↓ (λ a → congr (Sᵃ a) ((λ a → lemma18a k Sᵃ a δ) , ≡ᵈ-refl)) a ⟩
       ♯ (Sᵃ a) (↓ᵖ k (((⟅ Sᵃ ⟆ δ) ^ k) ⊤ᵖ) , δ)
   ⩦⟨ ≡ᵖ-sym{A} (strong (Sᵃ a) zeroˢ ((((⟅ Sᵃ ⟆ δ) ^ k) ⊤ᵖ) , δ) k k ≤-refl) {a} ⟩
       ♯ (Sᵃ a) (((⟅ Sᵃ ⟆ δ) ^ k) ⊤ᵖ , δ)
   ⩦⟨ ≡ᵒ-refl refl ⟩
       ((⟅ Sᵃ ⟆ δ) ^ (suc k)) ⊤ᵖ a
   ∎
\end{code}
\caption{One unrolling of $muᵒ\, Sᵃ\, δ$ is equivalent to $k \plus 1$ iterations of
$\eff{Sᵃ}\, δ$, under $k\plus 1$-approximation.}
\label{fig:lemma18b}
\end{figure}


\begin{figure}[tbp]
\small
\begin{code}
lemma19a : ∀ (Sᵃ : A → Setˢ (A ∷ Γ) (Later ∷ Δ)) (a : A) (k : ℕ) (δ : RecEnv Γ)
   → muᵒ Sᵃ δ a ≡[ k ] ♯ (Sᵃ a) (muᵒ Sᵃ δ , δ)
lemma19a {A}{Γ}{Δ} Sᵃ a k δ =
    let f = (⟅ Sᵃ ⟆ δ) in
      muᵒ Sᵃ δ a
  ⩦⟨ lemma18a k Sᵃ a δ  ⟩
      (f ^ k) ⊤ᵖ a
  ⩦⟨ lemma15b-env-fun (suc k) k Sᵃ a (n≤1+n k) ⟩
      (f ^ (suc k)) ⊤ᵖ a
  ⩦⟨ ≡ᵖ-sym (lemma17ᵒ{((f ^ (suc k)) ⊤ᵖ) a} k) {a} ⟩
      ↓ᵒ (suc k) ((f ^ (suc k)) ⊤ᵖ a)
   ⩦⟨ cong-↓ (λ a → ≡ᵒ-sym (lemma18b k Sᵃ a δ))  a  ⟩
      ↓ᵒ (suc k) (♯ (Sᵃ a) (muᵒ Sᵃ δ , δ))
   ⩦⟨ lemma17ᵒ{(♯ (Sᵃ a) (muᵒ Sᵃ δ , δ))} k ⟩
      ♯ (Sᵃ a) (muᵒ Sᵃ δ , δ)
   ∎
\end{code}
\caption{$muᵒ\, Sᵃ\, δ$ is equivalent to one unrolling of itself under $k$-approximation.}
\label{fig:lemma19a}
\end{figure}

The proof that \textsf{mu}ᵒ is a strong environment functional
proceeds by cases on whether the variable in question is assigned to
\textsf{Now} in Δ, in which case we need to show that \textsf{mu}ᵒ is
strongly nonexpansive with respect to that variable, or the variable
is assigned to \textsf{Later} in Δ, in which case we need to show that
\textsf{mu}ᵒ is strongly contractive.

The proof that \textsf{mu}ᵒ is strongly nonexpansive
(Figure~\ref{fig:mu-nonexpansive}) demonstrates why we need to
generalize from nonexpansive to strongly nonexpansive. Suppose we were
trying to prove that \textsf{mu}ᵒ is merely nonexpansive in $x$.
\[
   ↓ᵒ\, k\, (muᵒ\, Sᵃ\, δ\, a) ≡ᵒ ↓ᵒ\, k\, (muᵒ\, Sᵃ\, (↓ᵈ\, k\, x\, δ)\, a)
\]
We proceed by induction on $k$ and consider the case for $k = 1 \plus k′$.
The equational reasoning takes the same first three steps
as in Figure~\ref{fig:mu-nonexpansive}, except with $k$ replacing $j$.
The fourth step requires the induction hypothesis, but we need
to prove that
\[
   ↓ᵒ\, k′\, (muᵒ\, Sᵃ\, δ\, a) ≡ᵒ ↓ᵒ\, k′\, (muᵒ\, Sᵃ\, (↓ᵈ\, (1 \plus k′)\, x\, δ)\, a)
\]
The $1 \plus k′$ on the right-hand side does not match the induction
hypothesis, it would need to be $k′$. Our insight is that taking a
larger-than necessary approximation on the input is harmless,
so we can replace nonexpansive with strongly nonexpansive.
Thus we instead must prove that
\[
   ↓ᵒ\, k\, (muᵒ\, Sᵃ\, δ\, a) ≡ᵒ ↓ᵒ\, k\, (muᵒ\, Sᵃ\, (↓ᵈ\, j\, x\, δ)\, a)
\]
for any $j$ greater or equal to $k$. Then in the fourth step of the
proof, we need to prove
\[
   ↓ᵒ\, k′\, (muᵒ\, Sᵃ\, δ\, a) ≡ᵒ ↓ᵒ\, k′\, (muᵒ\, Sᵃ\, (↓ᵈ\, j\, x\, δ)\, a)
\]
so we are required to show $k′ ≤ j$, but that follows immediately from $1 \plus k′ = k ≤ j$.


\begin{figure}[tbp]
\small
\begin{code}
mu-nonexpansive : ∀{Γ}{Δ : Times Γ}{A}{B} (Sᵃ : A → Setˢ (A ∷ Γ) (Later ∷ Δ)) (a : A) (x : Γ ∋ B)
   → timeof x Δ ≡ Now → (δ : RecEnv Γ) (k j : ℕ) → (k ≤ j)
   → muᵒ Sᵃ δ a ≡[ k ] muᵒ Sᵃ (↓ᵈ j x δ) a
mu-nonexpansive {Γ} {Δ} {A} Sᵃ a x time-x δ zero j k≤j = ↓ᵒ-zero
mu-nonexpansive {Γ} {Δ} {A}{B} Sᵃ a x time-x δ (suc k′) j k≤j =
      muᵒ Sᵃ δ a
  ⩦⟨ lemma19a Sᵃ a (suc k′) δ ⟩
      ♯ (Sᵃ a) (muᵒ Sᵃ δ , δ)
  ⩦⟨ nonexp-Sᵃ-sx ⟩
      ♯ (Sᵃ a) (muᵒ Sᵃ δ , ↓ᵈ j x δ)
  ⩦⟨ wf-Sᵃ-z1 ⟩
      ♯ (Sᵃ a) (↓ᵖ k′ (muᵒ Sᵃ δ) , ↓ᵈ j x δ)
  ⩦⟨ cong-↓ (λ a → congr (Sᵃ a) (IH , ≡ᵈ-refl)) a ⟩
      ♯ (Sᵃ a) (↓ᵖ k′ (muᵒ Sᵃ (↓ᵈ j x δ)) , ↓ᵈ j x δ)
  ⩦⟨ ≡ᵒ-sym wf-Sᵃ-z2 ⟩
      ♯ (Sᵃ a) (muᵒ Sᵃ (↓ᵈ j x δ) , ↓ᵈ j x δ)
  ⩦⟨ ≡ᵒ-sym (lemma19a Sᵃ a (suc k′) (↓ᵈ j x δ)) ⟩
      muᵒ Sᵃ (↓ᵈ j x δ) a
  ∎
  where
  IH : ∀ a → ↓ᵒ k′ (muᵒ Sᵃ δ a) ≡ᵒ ↓ᵒ k′ (muᵒ Sᵃ (↓ᵈ j x δ) a)
  IH a = mu-nonexpansive Sᵃ a x time-x δ k′ j (≤-trans (n≤1+n _) k≤j)
  nonexp-Sᵃ-sx = strong-now{x = sucˢ x}{Δ = Later ∷ Δ}
                    (strong (Sᵃ a) (sucˢ x)) time-x (muᵒ Sᵃ δ , δ) j (suc k′) k≤j
  wf-Sᵃ-z1 = strong (Sᵃ a) zeroˢ (muᵒ Sᵃ δ , ↓ᵈ j x δ) k′ k′ ≤-refl
  wf-Sᵃ-z2 = strong (Sᵃ a) zeroˢ (muᵒ Sᵃ (↓ᵈ j x δ) , ↓ᵈ j x δ) k′ k′ ≤-refl
\end{code}
\caption{\textsf{mu}ᵒ is strongly nonexpansive.}
\label{fig:mu-nonexpansive}
\end{figure}

Figure~\ref{fig:mu-contractive} gives the proof for the second case,
that \textsf{mu}ᵒ is strongly contractive. The proof is similar to the
previous one.

\begin{figure}[tbp]
\small
\begin{code}
mu-contractive : (Sᵃ : A → Setˢ (A ∷ Γ) (Later ∷ Δ)) (a : A) (x : Γ ∋ B)
   → timeof x Δ ≡ Later → (δ : RecEnv Γ) (k j : ℕ) → (k ≤ j)
   → muᵒ Sᵃ δ a ≡[ 1 + k ] muᵒ Sᵃ (↓ᵈ j x δ) a
mu-contractive {A} {Γ} {Δ} {B} Sᵃ a x time-x δ zero j k≤j = ↓ᵒ-one
mu-contractive {A} {Γ} {Δ} {B} Sᵃ a x time-x δ (suc k′) j k≤j =
      muᵒ Sᵃ δ a
  ⩦⟨ lemma19a Sᵃ a (1 + (1 + k′)) δ ⟩
      ♯ (Sᵃ a) (muᵒ Sᵃ δ , δ)
  ⩦⟨ wf-Sᵃ-sx ⟩
      ♯ (Sᵃ a) (muᵒ Sᵃ δ , ↓ᵈ j x δ)
  ⩦⟨ wf-Sᵃ-z1 ⟩
      ♯ (Sᵃ a) (↓ᵖ (1 + k′) (muᵒ Sᵃ δ) , ↓ᵈ j x δ)
  ⩦⟨ cong-↓ (λ a → congr (Sᵃ a) (IH , ≡ᵈ-refl)) a ⟩
      ♯ (Sᵃ a) (↓ᵖ (1 + k′) (muᵒ Sᵃ (↓ᵈ j x δ)) , ↓ᵈ j x δ)
  ⩦⟨ ≡ᵒ-sym wf-Sᵃ-z2 ⟩
      ♯ (Sᵃ a) (muᵒ Sᵃ (↓ᵈ j x δ) , (↓ᵈ j x δ))
  ⩦⟨ ≡ᵒ-sym (lemma19a Sᵃ a (1 + (1 + k′)) _) ⟩
      muᵒ Sᵃ (↓ᵈ j x δ) a
  ∎
  where
  IH : ∀ a → ↓ᵒ (1 + k′) (muᵒ Sᵃ δ a) ≡ᵒ ↓ᵒ (1 + k′) (muᵒ Sᵃ (↓ᵈ j x δ) a)
  IH a = mu-contractive Sᵃ a x time-x δ k′ j (≤-trans (n≤1+n _) k≤j)
  wf-Sᵃ-sx = strong-later{A = B}{sucˢ x}{Δ = Later ∷ Δ}
              (strong (Sᵃ a) (sucˢ x)) time-x (muᵒ Sᵃ δ , δ) j (1 + k′) k≤j 
  wf-Sᵃ-z1 = strong (Sᵃ a) zeroˢ (muᵒ Sᵃ δ , ↓ᵈ j x δ) (1 + k′) (1 + k′) ≤-refl 
  wf-Sᵃ-z2 = strong (Sᵃ a) zeroˢ (muᵒ Sᵃ (↓ᵈ j x δ) , ↓ᵈ j x δ) (1 + k′) (1 + k′) ≤-refl 
\end{code}
\caption{\textsf{mu}ᵒ is strongly contractive.}
\label{fig:mu-contractive}
\end{figure}

Finally, we put the two cases together to show that \textsf{mu}ᵒ is a strong
environment functional (Figure~\ref{fig:mu-strong-env-fun}).

\begin{figure}[tbp]
\small
\begin{code}
strong-fun-mu : ∀{Γ}{Δ : Times Γ}{A} (Sᵃ : A → Setˢ (A ∷ Γ) (Later ∷ Δ)) (a : A)
   → strong-fun Δ (λ δ → muᵒ Sᵃ δ a)
strong-fun-mu {Γ} {Δ} {A} Sᵃ a x
    with timeof x Δ in time-x
... | Now = λ δ j k k≤j → mu-nonexpansive Sᵃ a x time-x δ k j k≤j
... | Later = λ δ j k k≤j → mu-contractive Sᵃ a x time-x δ k j k≤j
\end{code}
\caption{\textsf{mu}ᵒ is a strong environment functional.}
\label{fig:mu-strong-env-fun}
\end{figure}

\clearpage

\subsubsection{\textsf{mu}ᵒ is congruent}

To prove that \textsf{mu}ᵒ is congruent we need just one lemma, that
the \textsf{iter} function produces equivalent predicates given
congruent functions $f$ and $g$.

\begin{code}
cong-iter : ∀{A}{a : A} (i : ℕ) (f g : Predᵒ A → Predᵒ A)
  → (∀ P Q a → (∀ b → P b ≡ᵒ Q b) → f P a ≡ᵒ g Q a) → (I : Predᵒ A)
  → (f ^ i) I a ≡ᵒ (g ^ i) I a
cong-iter zero f g f=g I = ≡ᵒ-refl refl
cong-iter{A}{a} (suc i) f g f=g I =
  let IH = λ b → cong-iter{A}{b} i f g f=g I in
  f=g ((f ^ i) I) ((g ^ i) I) a IH
\end{code}

\noindent The result \textsf{mu}ᵒ is congruent follows immediately from the lemma.

\begin{code}
congruent-mu : ∀{Γ}{Δ : Times Γ}{A} (Sᵃ : A → Setˢ (A ∷ Γ) (Later ∷ Δ)) (a : A)
   → congruent (λ δ → muᵒ Sᵃ δ a)
congruent-mu{Γ}{Δ}{A} Sᵃ a {δ}{δ′} δ=δ′ = ≡ᵒ-intro Goal
  where
  Goal : (k : ℕ) → μᵖ (⟅ Sᵃ ⟆ δ) a k ⇔ μᵖ (⟅ Sᵃ ⟆ δ′) a k
  Goal k = ≡ᵒ-elim (cong-iter{A}{a} (suc k) (⟅ Sᵃ ⟆ δ) (⟅ Sᵃ ⟆ δ′)
                       (λ P Q a P=Q → congr (Sᵃ a) (P=Q , δ=δ′)) ⊤ᵖ)
\end{code}

\subsubsection{Definition of μˢ}

We construct the record for the predicate $μˢ \,Sᵃ$ as follows.

\begin{code}
μˢ Sᵃ a = record { ♯ = λ δ → muᵒ Sᵃ δ a ; strong = strong-fun-mu Sᵃ a
                 ; congr = congruent-mu Sᵃ a }
\end{code}

\subsubsection{Fixpoint Theorem}

Most of the work to prove the fixpoint theorem is already finished,
with the series of lemmas that concluded with \textsf{lemma19a}, which
showed that one unrolling of the recursive predicate is equivalent to
the recursive predicate under $k$-approximation. It remains to show
that if two formula are equivalent under $k$-approximation, then they
are equivalent. This is straightforward to prove by induction on the
step index, as shown below.

\begin{code}
equiv-downᵒ : (∀ k → ϕ ≡[ k ] ψ) → ϕ ≡ᵒ ψ
equiv-downᵒ {ϕ}{ψ} ↓ϕ=↓ψ = ≡ᵒ-intro aux
  where aux : ∀ i → # ϕ i ⇔ # ψ i
        aux zero = (λ _ → tz ψ) , (λ _ → tz ϕ)
        aux (suc i) = let ↓ϕ⇔↓ψ = (≡ᵒ-elim{k = suc i} (↓ϕ=↓ψ (suc (suc i)))) in
                      (λ ϕsi → proj₂ (⇔-to ↓ϕ⇔↓ψ  (≤-refl , ϕsi)))
                      , (λ ψsi → proj₂ (⇔-fro ↓ϕ⇔↓ψ (≤-refl , ψsi)))
\end{code}

\noindent We lift this lemma from $\mathsf{Set}ᵒ$ to $\mathsf{Set}ˢ$
with the following corollary.

\begin{code}
abstract
  equiv-downˢ : (∀ k → ↓ˢ k S ≡ˢ ↓ˢ k T) → S ≡ˢ T
  equiv-downˢ {S = S}{T} ↓S=↓T δ = equiv-downᵒ{♯ S δ}{♯ T δ} λ k → (↓S=↓T k) δ
\end{code}

\noindent We prove the fixpoint theorem by applying \textsf{lemma19a}
and then \textsf{equiv-down}ˢ.

\begin{code}
fixpointˢ : ∀ (F : A → Setˢ (A ∷ Γ) (Later ∷ Δ)) (a : A)
   → μˢ F a ≡ˢ letˢ (μˢ F) (F a)
fixpointˢ F a = equiv-downˢ λ k → ≡ˢ-intro (lemma19a F a k)
\end{code}

A recursive predicate will often appear at the top of a logical
formula, in which case it does not need to be an open formula. To
streamline this situation, we define the following μᵒ connective,
which specializes μˢ to the situation where $Γ = []$.

\begin{code}
μᵒ : (A → Setˢ (A ∷ []) (Later ∷ [])) → (A → Setᵒ)
μᵒ P = muᵒ P ttᵖ
\end{code}

\noindent Also for convenience, we provide the following
specialization of the fixpoint theorem for μᵒ.

TODO: Move letᵒ to an appropriate place
\begin{code}
letᵒ : Predᵒ A → Setˢ (A ∷ []) (Later ∷ []) → Setᵒ
letᵒ P T = (♯ T) (P , ttᵖ)
\end{code}

\begin{code}
fixpointᵒ : ∀{A} (P : A → Setˢ (A ∷ []) (Later ∷ [])) (a : A)
   → μᵒ P a ≡ᵒ letᵒ (μᵒ P) (P a)
fixpointᵒ P a = ≡ˢ-elim (fixpointˢ P a) ttᵖ
\end{code}

\noindent That concludes our treatment of the recursive predicate in
SIL. We now move onto to the simpler connectives, including the
logical connectives from first-order logical.

\subsection{Pure}

A step-indexed logic such as LSLR is typically specialized to include
atomic formulas to express properties of programs in a particular
language. Here we instead allow arbitrary Agda propositions to be
included in a step-indexed proposition by way of the following
pure operator. Given a proposition $p$, the formula $p\,ᵒ$ is true
at zero and everywhere else it is equivalent to $p$.

\begin{code}
_ᵒ : Set → Setᵒ
p ᵒ = record { # = λ { zero → ⊤ ; (suc k) → p }
             ; down = λ { k pk zero j≤k → tt
                        ; (suc k) pk (suc j) j≤k → pk}
             ; tz = tt }
\end{code}

\noindent The pure operator is a strong environment functiuonal.

\begin{code}
strong-pure : ∀ (p : Set) (x : Γ ∋ A) → strong-var x (timeof x Δ) (λ δ → p ᵒ)
strong-pure {Γ}{A}{Δ} p x
    with timeof x Δ
... | Now = λ δ j k k≤j → ≡ᵒ-refl refl
... | Later = λ δ j k k≤j → ≡ᵒ-refl refl
\end{code}

\noindent So we define the constant SIL formula $pˢ$ as the following record.

\begin{code}
p ˢ = record { ♯ = λ δ → p ᵒ ; strong = λ x → strong-pure p x ; congr = λ d=d′ → ≡ᵒ-refl refl }
\end{code}

\subsection{True and False}

We already defined ⊤ᵒ, but it remains to construct the open variant of
the true formula, written ⊤ˢ.

\begin{code}
⊤ˢ : Setˢ Γ (laters Γ)
⊤ˢ = record { ♯ = λ δ → ⊤ᵒ ; strong = strong-⊤ ; congr = λ _ → ≡ᵒ-refl refl }
  where
  strong-⊤ : strong-fun (laters Γ) (λ δ → ⊤ᵒ)
  strong-⊤ x rewrite timeof-later x = λ δ j k k≤j → ≡ᵒ-refl refl
\end{code}

We do so by lifting Agda's true into SIL using the constant operator.
We similarly lift the false formula of Agda into SIL.

\begin{code}
⊥ᵒ : Setᵒ
⊥ᵒ = ⊥ ᵒ

⊥ˢ : Setˢ Γ (laters Γ)
⊥ˢ = ⊥ ˢ
\end{code}

\subsection{For all}

The forall quantifier maps a step-indexed predicate $P$ to $\mathsf{Set}ᵒ$.
That is, $∀ᵒ P$ is true at $k$ if, for any $a ∈ A$, $P\,a$ is true at $k$.

\begin{code}
∀ᵒ : Predᵒ A → Setᵒ
∀ᵒ P = record { # = λ k → ∀ a → # (P a) k
              ; down = λ n ∀Pn k k≤n a → down (P a) n (∀Pn a) k k≤n
              ; tz = λ a → tz (P a) }
\end{code}

\noindent As an example, the following formla says that adding zero to any
natural number is equal to itself.

\begin{code}
_ = ∀ᵒ (λ x → (x + 0 ≡ x)ᵒ)
\end{code}

\noindent We make the syntax of the forall quantifier more natural with the
following syntax definition.

\begin{code}
∀ᵒ-syntax = ∀ᵒ
infix 2 ∀ᵒ-syntax
syntax ∀ᵒ-syntax (λ x → P) = ∀ᵒ[ x ] P
\end{code}

\noindent So the above example can be rewritten as follows.

\begin{code}
_ = ∀ᵒ[ x ] (x + 0 ≡ x)ᵒ
\end{code}

\noindent In some situations, Agda has trouble infering the type of
the quantifier. So we also provide the following version of ∀ᵒ that
includes an explicit type annotation.

\begin{code}
∀ᵒ-annot : ∀ A → Predᵒ A → Setᵒ
∀ᵒ-annot A = ∀ᵒ{A = A}
\end{code}

\begin{code}
∀ᵒ-annot-syntax = ∀ᵒ-annot
infix 2 ∀ᵒ-annot-syntax
syntax ∀ᵒ-annot-syntax A (λ x → P) = ∀ᵒ[ x ⦂ A ] P
\end{code}

\noindent The forall quantifier is congruent in the following sense.

\begin{code}
abstract
  cong-∀ : (∀ a → P a ≡ᵒ Q a) → (∀ᵒ P) ≡ᵒ (∀ᵒ Q)
  cong-∀ {P = P}{k} P=Q zero = (λ z a → proj₁ (P=Q a zero) (z a)) , (λ _ a → tz (P a))
  cong-∀ {k} P=Q (suc i) = (λ z a → proj₁ (P=Q a (suc i)) (z a))
                           , (λ z a → proj₂ (P=Q a (suc i)) (z a))
\end{code}

\noindent The forall quantifier is also nonexpansive.

\begin{code}
abstract
  nonexpansive-∀ : ∀{k} → (∀ᵒ[ a ] P a)  ≡[ k ]  (∀ᵒ[ a ] ↓ᵒ k (P a))
  nonexpansive-∀ zero = (λ x → tt) , (λ x → tt)
  nonexpansive-∀ (suc i) = (λ {(a , b) → a , (λ c → a , b c)}) , λ {(a , b) → a , (λ a → proj₂ (b a))}
\end{code}

\noindent In Figure~\ref{fig:strong-all} we show that the forall
quantifier is a strong environment functional.

\begin{figure}[tbp]
\small
\begin{code}
strong-all : (P : A → Setˢ Γ Δ) → strong-fun Δ (λ δ → ∀ᵒ[ a ] ♯ (P a) δ)
strong-all {A}{Γ}{Δ} P x
    with timeof x Δ in time-x
... | Now = λ δ j k k≤j →
        ∀ᵒ[ a ] ♯ (P a) δ
      ⩦⟨ nonexpansive-∀ ⟩
        ∀ᵒ[ a ] ↓ᵒ k (♯ (P a) δ)
      ⩦⟨ cong-↓ᵒ k (cong-∀(λ a → strong-now(strong(P a) x) time-x δ j k k≤j)) ⟩
        ∀ᵒ[ a ] ↓ᵒ k (♯ (P a) (↓ᵈ j x δ))
      ⩦⟨ ≡ᵒ-sym nonexpansive-∀ ⟩
        ∀ᵒ[ a ] ♯ (P a) (↓ᵈ j x δ)
      ∎
... | Later = λ δ j k k≤j → 
        ∀ᵒ[ a ] ♯ (P a) δ
      ⩦⟨ nonexpansive-∀ ⟩
        ∀ᵒ[ a ] ↓ᵒ (suc k) (♯ (P a) δ)
      ⩦⟨ cong-↓ᵒ (suc k) (cong-∀ (λ a → strong-later (strong (P a) x) time-x δ j k k≤j)) ⟩
        ∀ᵒ[ a ] ↓ᵒ (suc k) (♯ (P a) (↓ᵈ j x δ))
      ⩦⟨ ≡ᵒ-sym nonexpansive-∀ ⟩
        ∀ᵒ[ a ] ♯ (P a) (↓ᵈ j x δ)
      ∎
\end{code}
\caption{The forall quantifier is a strong environment functional.}
\label{fig:strong-all}
\end{figure}

Finally, we define the open version of the forall quantifier, ∀ˢ, by
constructing the following record from the above ingredients.

\begin{code}
∀ˢ P = record { ♯ = λ δ → ∀ᵒ[ a ] ♯ (P a) δ ; strong = strong-all P
              ; congr = λ d=d′ → cong-∀ λ a → congr (P a) d=d′ }
∀ˢ-syntax = ∀ˢ
infix 1 ∀ˢ-syntax
syntax ∀ˢ-syntax (λ x → P) = ∀ˢ[ x ] P
\end{code}

\subsection{Exists}

We define the formula $∃ᵒ P$ at $k$ to mean that there exists a value
$a ∈ A$ such that $P \app a$ is true at $k$.  For the true-at-zero
property, we use the \textsf{elt} field of \textsf{Inhabited} to
obtain a witness.

\begin{code}
∃ᵒ : ∀{{_ : Inhabited A}} → Predᵒ A → Setᵒ
∃ᵒ P = record { # = λ k → ∃[ a ] # (P a) k
              ; down = λ n (a , Pa) k k≤n → a , (down (P a) n Pa k k≤n)
              ; tz = elt , tz (P elt) }

∃ᵒ-syntax = ∃ᵒ
infix 2 ∃ᵒ-syntax
syntax ∃ᵒ-syntax (λ x → P) = ∃ᵒ[ x ] P
\end{code}

\noindent The existential quantifier is congruent.

\begin{code}
abstract
  cong-∃ : ∀{P Q : Predᵒ A}{{_ : Inhabited A}} → (∀ a → P a ≡ᵒ Q a) → (∃ᵒ P) ≡ᵒ (∃ᵒ Q)
  cong-∃ {A} {P} {Q} P=Q i = (λ {(a , b) → a , proj₁ (P=Q a i) b}) , λ {(a , b) → a , (proj₂ (P=Q a i) b)}
\end{code}

\noindent The existential quantifier is also nonexpansive.

\begin{code}
abstract
  nonexpansive-∃ : ∀{A}{P : Predᵒ A}{k}{{_ : Inhabited A}}
    → (∃ᵒ[ a ] P a) ≡[ k ] (∃ᵒ[ a ] ↓ᵒ k (P a))
  nonexpansive-∃ {A} {P} {k} zero = (λ x → tt) , (λ x → tt)
  nonexpansive-∃ {A} {P} {k} (suc i) = (λ {(a , (b , c)) → a , (b , (a , c))}) , λ { (a , b , c) → a , b , proj₂ c}
\end{code}

\noindent Figure~\ref{fig:strong-exists} shows that the existential
quantifier is a strong environment functional.

\begin{figure}[tbp]
\begin{code}
strong-exists : {{_ : Inhabited A}} (P : A → Setˢ Γ Δ)
  → strong-fun Δ (λ δ → ∃ᵒ[ a ] ♯ (P a) δ)
strong-exists {A}{Γ}{Δ} P x
    with timeof x Δ in time-x
... | Now = λ δ j k k≤j →
        ∃ᵒ[ a ] ♯ (P a) δ
      ⩦⟨ nonexpansive-∃ ⟩
        ∃ᵒ[ a ] ↓ᵒ k (♯ (P a) δ)
      ⩦⟨ cong-↓ᵒ k (cong-∃(λ a → strong-now(strong(P a) x) time-x δ j k k≤j)) ⟩
        ∃ᵒ[ a ] ↓ᵒ k (♯ (P a) (↓ᵈ j x δ))
      ⩦⟨ ≡ᵒ-sym nonexpansive-∃ ⟩
        ∃ᵒ[ a ] ♯ (P a) (↓ᵈ j x δ)
      ∎
... | Later = λ δ j k k≤j →
        ∃ᵒ[ a ] ♯ (P a) δ
      ⩦⟨ nonexpansive-∃ ⟩
        ∃ᵒ[ a ] ↓ᵒ (suc k) (♯ (P a) δ)
      ⩦⟨ cong-↓ᵒ (suc k) (cong-∃ (λ a → strong-later (strong (P a) x) time-x δ j k k≤j)) ⟩
        ∃ᵒ[ a ] ↓ᵒ (suc k) (♯ (P a) (↓ᵈ j x δ))
      ⩦⟨ ≡ᵒ-sym nonexpansive-∃ ⟩
        ∃ᵒ[ a ] ♯ (P a) (↓ᵈ j x δ)
      ∎
\end{code}
\caption{The existential quantifier is a strong environment functional.}
\label{fig:strong-exists}
\end{figure}

Finally, we define the open version of the existential quantifier, ∃ˢ,
by constructing the following record from the above ingredients.

\begin{code}
∃ˢ P = record { ♯ = λ δ → ∃ᵒ[ a ] ♯ (P a) δ ; strong = strong-exists P
              ; congr = λ d=d′ → cong-∃ λ a → congr (P a) d=d′ }

∃ˢ-syntax = ∃ˢ
infix 1 ∃ˢ-syntax
syntax ∃ˢ-syntax (λ x → P) = ∃ˢ[ x ] P
\end{code}


\subsection{Conjunction}

Next we define conjunction in SIL. Given step-indexed propositions
$ϕ$ and $ψ$, their conjunction is the function that takes the
conjunction of applying them to the step index. The proofs of
downward-closedness and true-at-zero are straightforward, using
the proofs of these properties for $ϕ$ and $ψ$.

\begin{code}
infixr 7 _×ᵒ_
_×ᵒ_ : Setᵒ → Setᵒ → Setᵒ
ϕ ×ᵒ ψ = record { # = λ k → # ϕ k × # ψ k
                ; down = λ k (ϕk , ψk) j j≤k → (down ϕ k ϕk j j≤k) , (down ψ k ψk j j≤k)
                ; tz = (tz ϕ) , (tz ψ) }
\end{code}

\noindent The conjunction connective is congruent.

\begin{code}
cong-×ᵒ : ϕ ≡ᵒ ϕ′ → ψ ≡ᵒ ψ′ → ϕ ×ᵒ ψ ≡ᵒ ϕ′ ×ᵒ ψ′
cong-×ᵒ {ϕ}{ϕ′}{ψ}{ψ′} ϕ=ϕ′ ψ=ψ′ = ≡ᵒ-intro (λ k → ⇔-intro to fro)
  where
  to : ∀{k} → # (ϕ ×ᵒ ψ) k → # (ϕ′ ×ᵒ ψ′) k
  to {k} (ϕk , ψk) = (⇔-to (≡ᵒ-elim ϕ=ϕ′) ϕk) , (⇔-to (≡ᵒ-elim ψ=ψ′) ψk)
  fro  : ∀{k} → #(ϕ′ ×ᵒ ψ′) k → #(ϕ ×ᵒ ψ) k
  fro {k} (ϕ′k , ψ′k) = (⇔-fro (≡ᵒ-elim ϕ=ϕ′) ϕ′k) , (⇔-fro (≡ᵒ-elim ψ=ψ′) ψ′k)
\end{code}

\noindent The conjunction connective is also nonexpansive.

\begin{code}
nonexpansive-× : ∀{k} → ϕ ×ᵒ ψ ≡[ k ] (↓ᵒ k ϕ) ×ᵒ (↓ᵒ k ψ)
nonexpansive-× {ϕ}{ψ} = ≡ᵒ-intro (λ i → aux i)
  where
  aux : ∀{k} i → #(↓ᵒ k (ϕ ×ᵒ ψ)) i ⇔ #(↓ᵒ k ((↓ᵒ k ϕ) ×ᵒ (↓ᵒ k ψ))) i
  aux zero = ⇔-intro (λ x → tt) (λ x → tt)
  aux (suc i) = ⇔-intro (λ { (si<k , ϕsi , Δi) → si<k , ((si<k , ϕsi) , (si<k , Δi))})
                         (λ { (si<k , (_ , ϕsi) , _ , Δi) → si<k , ϕsi , Δi})
\end{code}

\noindent The time of a variable in a list of combined times is equal
to choosing between the times in each list.

\begin{code}
timeof-combine : ∀{Γ}{Δ₁ Δ₂ : Times Γ}{A}{x : Γ ∋ A}
   → timeof x (Δ₁ ∪ Δ₂) ≡ choose (timeof x Δ₁) (timeof x Δ₂)
timeof-combine {B ∷ Γ} {s ∷ Δ₁} {t ∷ Δ₂} {.B} {zeroˢ} = refl
timeof-combine {B ∷ Γ} {s ∷ Δ₁} {t ∷ Δ₂} {A} {sucˢ x} =
  timeof-combine {Γ} {Δ₁} {Δ₂} {A} {x}
\end{code}

Figure~\ref{fig:strong-pair} shows the proof that conjunction is a strong
environment functional. There are four cases to consider, the cross product
of whether the time of $x$ in $Δ₁$ and $Δ₂$ are \textsf{Now} or \textsf{Later}.

\begin{figure}[tbp]
\footnotesize
\begin{code}
strong-pair : (S : Setˢ Γ Δ₁) (T : Setˢ Γ Δ₂) → strong-fun (Δ₁ ∪ Δ₂) (λ δ → ♯ S δ ×ᵒ ♯ T δ)
strong-pair {Γ}{Δ₁}{Δ₂} S T {A} x
    rewrite timeof-combine {Γ}{Δ₁}{Δ₂}{A}{x}
    with timeof x Δ₁ in time-x1 | timeof x Δ₂ in time-x2
... | Now | Now = λ δ j k k≤j →
    let strongS = strong-now (strong S x) time-x1 δ j k k≤j in
    let strongT = strong-now (strong T x) time-x2 δ j k k≤j in
      ♯ S δ ×ᵒ ♯ T δ
    ⩦⟨ nonexpansive-× ⟩ 
      ↓ᵒ k (♯ S δ) ×ᵒ ↓ᵒ k (♯ T δ)
    ⩦⟨ cong-↓ᵒ k (cong-×ᵒ strongS (≡ᵒ-refl refl)) ⟩ 
      ↓ᵒ k (♯ S (↓ᵈ j x δ)) ×ᵒ ↓ᵒ k (♯ T δ)
    ⩦⟨ cong-↓ᵒ k (cong-×ᵒ (≡ᵒ-refl refl) strongT) ⟩ 
      ↓ᵒ k (♯ S (↓ᵈ j x δ)) ×ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ))
    ⩦⟨ ≡ᵒ-sym nonexpansive-× ⟩
      ♯ S (↓ᵈ j x δ) ×ᵒ ♯ T (↓ᵈ j x δ)
    ∎
... | Now | Later = λ δ j k k≤j →
    let strongS = strong-now (strong S x) time-x1 δ j k k≤j in
    let strongT = strong-later (strong T x) time-x2 δ j k k≤j in
      ♯ S δ ×ᵒ ♯ T δ
    ⩦⟨ ≡ᵒ-sym (lemma17ᵒ k) ⟩ 
      ↓ᵒ (1 + k) (♯ S δ ×ᵒ ♯ T δ)
    ⩦⟨ cong-↓ᵒ k nonexpansive-× ⟩ 
      ↓ᵒ (1 + k) (↓ᵒ (1 + k) (♯ S δ) ×ᵒ ↓ᵒ (1 + k) (♯ T δ))
    ⩦⟨ cong-↓ᵒ k (cong-↓ᵒ (1 + k) (cong-×ᵒ (≡ᵒ-refl refl) strongT)) ⟩ 
      ↓ᵒ (1 + k) (↓ᵒ (1 + k) (♯ S δ) ×ᵒ ↓ᵒ (1 + k) (♯ T (↓ᵈ j x δ)))
    ⩦⟨ ≡ᵒ-sym (cong-↓ᵒ k nonexpansive-×) ⟩ 
      ↓ᵒ (1 + k) (♯ S δ ×ᵒ ♯ T (↓ᵈ j x δ))
    ⩦⟨ lemma17ᵒ k ⟩ 
      ♯ S δ ×ᵒ ♯ T (↓ᵈ j x δ)
    ⩦⟨ nonexpansive-× ⟩ 
      ↓ᵒ k (♯ S δ) ×ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ))
    ⩦⟨ cong-↓ᵒ k (cong-×ᵒ strongS (≡ᵒ-refl refl)) ⟩ 
      ↓ᵒ k (♯ S (↓ᵈ j x δ)) ×ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ))
    ⩦⟨ ≡ᵒ-sym nonexpansive-× ⟩ 
      ♯ S (↓ᵈ j x δ) ×ᵒ ♯ T (↓ᵈ j x δ)
    ∎
... | Later | Now = λ δ j k k≤j →
    let strongS = strong-later (strong S x) time-x1 δ j k k≤j in
    let strongT = strong-now (strong T x) time-x2 δ j k k≤j in
      ♯ S δ ×ᵒ ♯ T δ
    ⩦⟨ ≡ᵒ-sym (lemma17ᵒ k) ⟩ 
      ↓ᵒ (1 + k) (♯ S δ ×ᵒ ♯ T δ)
    ⩦⟨ cong-↓ᵒ k nonexpansive-× ⟩ 
      ↓ᵒ (1 + k) (↓ᵒ (1 + k) (♯ S δ) ×ᵒ ↓ᵒ (1 + k) (♯ T δ))
    ⩦⟨ cong-↓ᵒ k (cong-↓ᵒ (1 + k) (cong-×ᵒ strongS (≡ᵒ-refl refl))) ⟩ 
      ↓ᵒ (1 + k) (↓ᵒ (1 + k) (♯ S (↓ᵈ j x δ)) ×ᵒ ↓ᵒ (1 + k) (♯ T δ))
    ⩦⟨ ≡ᵒ-sym (cong-↓ᵒ k nonexpansive-×) ⟩ 
      ↓ᵒ (1 + k) (♯ S (↓ᵈ j x δ) ×ᵒ ♯ T δ)
    ⩦⟨ lemma17ᵒ k ⟩ 
      ♯ S (↓ᵈ j x δ) ×ᵒ ♯ T δ
    ⩦⟨ nonexpansive-× ⟩ 
      ↓ᵒ k (♯ S (↓ᵈ j x δ)) ×ᵒ ↓ᵒ k (♯ T δ)
    ⩦⟨ cong-↓ᵒ k (cong-×ᵒ (≡ᵒ-refl refl) strongT) ⟩ 
      ↓ᵒ k (♯ S (↓ᵈ j x δ)) ×ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ))
    ⩦⟨ ≡ᵒ-sym nonexpansive-× ⟩ 
      ♯ S (↓ᵈ j x δ) ×ᵒ ♯ T (↓ᵈ j x δ)
    ∎
... | Later | Later = λ δ j k k≤j →
    let strongS = strong-later (strong S x) time-x1 δ j k k≤j in
    let strongT = strong-later (strong T x) time-x2 δ j k k≤j in
      ♯ S δ ×ᵒ ♯ T δ
    ⩦⟨ nonexpansive-× ⟩ 
      ↓ᵒ (1 + k) (♯ S δ) ×ᵒ ↓ᵒ (1 + k) (♯ T δ)
    ⩦⟨ cong-↓ᵒ (1 + k) (cong-×ᵒ strongS strongT) ⟩ 
      ↓ᵒ (1 + k) (♯ S (↓ᵈ j x δ)) ×ᵒ ↓ᵒ (1 + k) (♯ T (↓ᵈ j x δ))
    ⩦⟨ ≡ᵒ-sym nonexpansive-× ⟩ 
      ♯ S (↓ᵈ j x δ) ×ᵒ ♯ T (↓ᵈ j x δ)
    ∎
\end{code}
\caption{Conjunction is a strong environment functional.}
\label{fig:strong-pair}
\end{figure}

We define the open version of conjunction by constructing the
following record from the above ingredients.

\begin{code}
S ×ˢ T = record { ♯ = λ δ → ♯ S δ ×ᵒ ♯ T δ ; strong = strong-pair S T
                ; congr = λ d=d′ → cong-×ᵒ (congr S d=d′) (congr T d=d′) }
\end{code}

\clearpage

\subsection{Disjunction}

Given two step-indexed propositions $ϕ$ and $ψ$, their disjunction is
the function that takes the disjunction of applying them to the step
index. The proofs of downward-closedness and true-at-zero are
straightforward, relying on the proofs of these properties for $ϕ$ and
$ψ$.

\begin{code}
infixr 7 _⊎ᵒ_
_⊎ᵒ_ : Setᵒ → Setᵒ → Setᵒ
ϕ ⊎ᵒ ψ = record { # = λ k → # ϕ k ⊎ # ψ k
                ; down = λ { k (inj₁ ϕk) j j≤k → inj₁ (down ϕ k ϕk j j≤k)
                           ; k (inj₂ ψk) j j≤k → inj₂ (down ψ k ψk j j≤k)}
                ; tz = inj₁ (tz ϕ) }
\end{code}

\noindent The disjunction connective is congruent.

\begin{code}
cong-⊎ᵒ : ϕ ≡ᵒ ϕ′ → ψ ≡ᵒ ψ′ → ϕ ⊎ᵒ ψ ≡ᵒ ϕ′ ⊎ᵒ ψ′
cong-⊎ᵒ {ϕ}{ϕ′}{ψ}{ψ′} ϕ=ϕ′ ψ=ψ′ = ≡ᵒ-intro (λ k → ⇔-intro to fro)
  where
  to : ∀{k} → # (ϕ ⊎ᵒ ψ) k → # (ϕ′ ⊎ᵒ ψ′) k
  to (inj₁ x) = inj₁ (proj₁ (≡ᵒ-elim ϕ=ϕ′) x)
  to (inj₂ y) = inj₂ (proj₁ (≡ᵒ-elim ψ=ψ′) y)
  fro  : ∀{k} → #(ϕ′ ⊎ᵒ ψ′) k → #(ϕ ⊎ᵒ ψ) k
  fro (inj₁ x) = inj₁ (proj₂ (≡ᵒ-elim ϕ=ϕ′) x)
  fro (inj₂ y) = inj₂ (proj₂ (≡ᵒ-elim ψ=ψ′) y)
\end{code}

\noindent The disjunction connective is also nonexpansive.

\begin{code}
nonexpansive-⊎ : ∀{k} → (ϕ ⊎ᵒ ψ) ≡[ k ] ((↓ᵒ k ϕ) ⊎ᵒ (↓ᵒ k ψ))
nonexpansive-⊎ {ϕ}{ψ}{k} = ≡ᵒ-intro (λ i → aux i)
  where
  aux : ∀ i → #(↓ᵒ k (ϕ ⊎ᵒ ψ)) i ⇔ #(↓ᵒ k ((↓ᵒ k ϕ) ⊎ᵒ (↓ᵒ k ψ))) i
  aux zero = ⇔-intro (λ x → tt) (λ x → tt)
  aux (suc i) = (λ { (x , inj₁ x₁) → x , inj₁ (x , x₁)
                   ; (x , inj₂ y) → x , inj₂ (x , y)})
               , λ { (x , inj₁ x₁) → x , inj₁ (proj₂ x₁)
                   ; (x , inj₂ y) → x , inj₂ (proj₂ y)}
\end{code}

Figure~\ref{fig:strong-sum} proves that disjunction is a strong
environment functional. Similar to the proof for conjunction,
there are four cases to consider, depending on whether $x$
has time \textsf{Now} or \textsf{Later} in Δ₁ and Δ₂.

\begin{figure}[tbp]
\footnotesize
\begin{code}
strong-sum : (S : Setˢ Γ Δ₁) (T : Setˢ Γ Δ₂)
   → strong-fun (Δ₁ ∪ Δ₂) (λ δ → ♯ S δ ⊎ᵒ ♯ T δ)
strong-sum {Γ}{Δ₁}{Δ₂} S T {A} x
    rewrite timeof-combine {Γ}{Δ₁}{Δ₂}{A}{x}
    with timeof x Δ₁ in time-x1 | timeof x Δ₂ in time-x2
... | Now | Now = λ δ j k k≤j →
    let strongS = strong-now (strong S x) time-x1 δ j k k≤j in
    let strongT = strong-now (strong T x) time-x2 δ j k k≤j in
      ♯ S δ ⊎ᵒ ♯ T δ
    ⩦⟨ nonexpansive-⊎ ⟩ 
      ↓ᵒ k (♯ S δ) ⊎ᵒ ↓ᵒ k (♯ T δ)
    ⩦⟨ cong-↓ᵒ k (cong-⊎ᵒ strongS (≡ᵒ-refl refl)) ⟩ 
      ↓ᵒ k (♯ S (↓ᵈ j x δ)) ⊎ᵒ ↓ᵒ k (♯ T δ)
    ⩦⟨ cong-↓ᵒ k (cong-⊎ᵒ (≡ᵒ-refl refl) strongT) ⟩ 
      ↓ᵒ k (♯ S (↓ᵈ j x δ)) ⊎ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ))
    ⩦⟨ ≡ᵒ-sym nonexpansive-⊎ ⟩
      ♯ S (↓ᵈ j x δ) ⊎ᵒ ♯ T (↓ᵈ j x δ)
    ∎
... | Now | Later = λ δ j k k≤j →
    let strongS = strong-now (strong S x) time-x1 δ j k k≤j in
    let strongT = strong-later (strong T x) time-x2 δ j k k≤j in
      ♯ S δ ⊎ᵒ ♯ T δ
    ⩦⟨ ≡ᵒ-sym (lemma17ᵒ k) ⟩ 
      ↓ᵒ (1 + k) (♯ S δ ⊎ᵒ ♯ T δ)
    ⩦⟨ cong-↓ᵒ k nonexpansive-⊎ ⟩ 
      ↓ᵒ (1 + k) (↓ᵒ (1 + k) (♯ S δ) ⊎ᵒ ↓ᵒ (1 + k) (♯ T δ))
    ⩦⟨ cong-↓ᵒ k (cong-↓ᵒ (1 + k) (cong-⊎ᵒ (≡ᵒ-refl refl) strongT)) ⟩ 
      ↓ᵒ (1 + k) (↓ᵒ (1 + k) (♯ S δ) ⊎ᵒ ↓ᵒ (1 + k) (♯ T (↓ᵈ j x δ)))
    ⩦⟨ ≡ᵒ-sym (cong-↓ᵒ k nonexpansive-⊎) ⟩ 
      ↓ᵒ (1 + k) (♯ S δ ⊎ᵒ ♯ T (↓ᵈ j x δ))
    ⩦⟨ lemma17ᵒ k ⟩ 
      ♯ S δ ⊎ᵒ ♯ T (↓ᵈ j x δ)
    ⩦⟨ nonexpansive-⊎ ⟩ 
      ↓ᵒ k (♯ S δ) ⊎ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ))
    ⩦⟨ cong-↓ᵒ k (cong-⊎ᵒ strongS (≡ᵒ-refl refl)) ⟩ 
      ↓ᵒ k (♯ S (↓ᵈ j x δ)) ⊎ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ))
    ⩦⟨ ≡ᵒ-sym nonexpansive-⊎ ⟩ 
      ♯ S (↓ᵈ j x δ) ⊎ᵒ ♯ T (↓ᵈ j x δ)
    ∎
... | Later | Now = λ δ j k k≤j →
    let strongS = strong-later (strong S x) time-x1 δ j k k≤j in
    let strongT = strong-now (strong T x) time-x2 δ j k k≤j in
      ♯ S δ ⊎ᵒ ♯ T δ
    ⩦⟨ ≡ᵒ-sym (lemma17ᵒ k) ⟩ 
      ↓ᵒ (1 + k) (♯ S δ ⊎ᵒ ♯ T δ)
    ⩦⟨ cong-↓ᵒ k nonexpansive-⊎ ⟩ 
      ↓ᵒ (1 + k) (↓ᵒ (1 + k) (♯ S δ) ⊎ᵒ ↓ᵒ (1 + k) (♯ T δ))
    ⩦⟨ cong-↓ᵒ k (cong-↓ᵒ (1 + k) (cong-⊎ᵒ strongS (≡ᵒ-refl refl))) ⟩ 
      ↓ᵒ (1 + k) (↓ᵒ (1 + k) (♯ S (↓ᵈ j x δ)) ⊎ᵒ ↓ᵒ (1 + k) (♯ T δ))
    ⩦⟨ ≡ᵒ-sym (cong-↓ᵒ k nonexpansive-⊎) ⟩ 
      ↓ᵒ (1 + k) (♯ S (↓ᵈ j x δ) ⊎ᵒ ♯ T δ)
    ⩦⟨ lemma17ᵒ k ⟩ 
      ♯ S (↓ᵈ j x δ) ⊎ᵒ ♯ T δ
    ⩦⟨ nonexpansive-⊎ ⟩ 
      ↓ᵒ k (♯ S (↓ᵈ j x δ)) ⊎ᵒ ↓ᵒ k (♯ T δ)
    ⩦⟨ cong-↓ᵒ k (cong-⊎ᵒ (≡ᵒ-refl refl) strongT) ⟩ 
      ↓ᵒ k (♯ S (↓ᵈ j x δ)) ⊎ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ))
    ⩦⟨ ≡ᵒ-sym nonexpansive-⊎ ⟩ 
      ♯ S (↓ᵈ j x δ) ⊎ᵒ ♯ T (↓ᵈ j x δ)
    ∎
... | Later | Later = λ δ j k k≤j →
    let strongS = strong-later (strong S x) time-x1 δ j k k≤j in
    let strongT = strong-later (strong T x) time-x2 δ j k k≤j in
      ♯ S δ ⊎ᵒ ♯ T δ
    ⩦⟨ nonexpansive-⊎ ⟩ 
      ↓ᵒ (1 + k) (♯ S δ) ⊎ᵒ ↓ᵒ (1 + k) (♯ T δ)
    ⩦⟨ cong-↓ᵒ (1 + k) (cong-⊎ᵒ strongS strongT) ⟩ 
      ↓ᵒ (1 + k) (♯ S (↓ᵈ j x δ))  ⊎ᵒ ↓ᵒ (1 + k) (♯ T (↓ᵈ j x δ))
    ⩦⟨ ≡ᵒ-sym nonexpansive-⊎ ⟩ 
      ♯ S (↓ᵈ j x δ) ⊎ᵒ ♯ T (↓ᵈ j x δ)
    ∎
\end{code}
\caption{Disjunction is a strong environment functional.}
\label{fig:strong-sum}
\end{figure}

\begin{code}
S ⊎ˢ T = record { ♯ = λ δ → ♯ S δ ⊎ᵒ ♯ T δ ; strong = strong-sum S T
                ; congr = λ d=d′ → cong-⊎ᵒ (congr S d=d′) (congr T d=d′) }
\end{code}

\clearpage

\subsection{Implication}

The definition of impliciation is interesting.  The following is a
naive first attempt, in which we following the same pattern as for
conjuction and disjunction, by saying that the meaning of $ϕ$ implies
$ψ$ at index $k$ is that $ϕ$ at $k$ implies $ψ$ at $k$. We run intro
trouble proving that this is downward closed. We are given that $ϕ$ at
$j$ for some $j \leq k$, but we have no way to prove that $ψ$ at $j$.

\begin{code}
_→n_ : Setᵒ → Setᵒ → Setᵒ
ϕ →n ψ = record { # = λ k → # ϕ k → # ψ k
                ; down = λ k ϕk→ψk j j≤k ϕj → impossible
                ; tz = λ ϕz → tz ψ }
\end{code}

\noindent The standard workaround is to force implication to be
downward closed by definition. We define $ϕ$ implies $ψ$ at $k$ to
mean that for all $j \leq k$, $ϕ$ at $j$ implies $ψ$ at $j$.

\begin{code}
infixr 6 _→ᵒ_
_→ᵒ_ : Setᵒ → Setᵒ → Setᵒ
ϕ →ᵒ ψ = record { # = λ k → ∀ j → j ≤ k → # ϕ j → # ψ j
                ; down = λ k ∀j≤k→ϕj→ψj j j≤k i i≤j ϕi → ∀j≤k→ϕj→ψj i (≤-trans i≤j j≤k) ϕi
                ; tz = λ { .zero z≤n _ → tz ψ} }
\end{code}

\noindent The implication connective is congruent.

\begin{code}
cong-→ : ϕ ≡ᵒ ϕ′ → ψ ≡ᵒ ψ′ → ϕ →ᵒ ψ ≡ᵒ ϕ′ →ᵒ ψ′
cong-→ {ϕ}{ϕ′}{ψ}{ψ′} ϕ=ϕ′ ψ=ψ′ = ≡ᵒ-intro (λ k →
  (λ x j x₁ x₂ → ⇔-to (≡ᵒ-elim ψ=ψ′) (x j x₁ (⇔-fro (≡ᵒ-elim ϕ=ϕ′) x₂)))
  , (λ z j z₁ z₂ → ⇔-fro (≡ᵒ-elim ψ=ψ′) (z j z₁ (⇔-to (≡ᵒ-elim ϕ=ϕ′) z₂))))
\end{code}

\noindent The implication connective is also nonexpansive.

\begin{code}
nonexpansive-→ : ∀{k} → (ϕ →ᵒ ψ) ≡[ k ] ((↓ᵒ k ϕ) →ᵒ (↓ᵒ k ψ))
nonexpansive-→ {ϕ}{ψ}{k} = ≡ᵒ-intro (λ i → aux i)
  where
  aux : ∀ i → #(↓ᵒ k (ϕ →ᵒ ψ)) i ⇔ #(↓ᵒ k ((↓ᵒ k ϕ) →ᵒ (↓ᵒ k ψ))) i
  aux zero = (λ x → tt) , (λ x → tt)
  aux (suc i) = (λ {(x , y) → x , (λ { zero x₁ x₂ → tt
                                     ; (suc j) x₁ (x₂ , x₃) → x₂ , y (suc j) x₁ x₃})})
               , λ {(x , y) → x , (λ { zero x₁ x₂ → tz ψ
                                     ; (suc j) x₁ x₂ → proj₂ (y (suc j) x₁ ((≤-trans (s≤s x₁) x) , x₂))})}
\end{code}

Figure~\ref{fig:strong-imp} shows the proof that implication is a
strong environment functional.

\begin{figure}[tbp]
\footnotesize
\begin{code}
strong-imp : ∀{Γ}{Δ₁ Δ₂ : Times Γ} (S : Setˢ Γ Δ₁) (T : Setˢ Γ Δ₂)
   → strong-fun (Δ₁ ∪ Δ₂) (λ δ → ♯ S δ →ᵒ ♯ T δ)
strong-imp {Γ}{Δ₁}{Δ₂} S T {A} x
    rewrite timeof-combine {Γ}{Δ₁}{Δ₂}{A}{x}
    with timeof x Δ₁ in time-x1 | timeof x Δ₂ in time-x2
... | Now | Now = λ δ j k k≤j →
    let strongS = strong-now (strong S x) time-x1 δ j k k≤j in
    let strongT = strong-now (strong T x) time-x2 δ j k k≤j in
      ♯ S δ →ᵒ ♯ T δ
    ⩦⟨ nonexpansive-→{♯ S δ}{♯ T δ} ⟩ 
      ↓ᵒ k (♯ S δ) →ᵒ ↓ᵒ k (♯ T δ)
    ⩦⟨ cong-↓ᵒ k (cong-→ strongS (≡ᵒ-refl refl)) ⟩ 
      ↓ᵒ k (♯ S (↓ᵈ j x δ)) →ᵒ ↓ᵒ k (♯ T δ)
    ⩦⟨ cong-↓ᵒ k (cong-→{↓ᵒ k (♯ S (↓ᵈ j x δ))}{↓ᵒ k (♯ S (↓ᵈ j x δ))}
                        {↓ᵒ k (♯ T δ)}{↓ᵒ k (♯ T (↓ᵈ j x δ))} (≡ᵒ-refl refl) strongT) ⟩ 
      ↓ᵒ k (♯ S (↓ᵈ j x δ)) →ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ))
    ⩦⟨ ≡ᵒ-sym (nonexpansive-→{♯ S (↓ᵈ j x δ)}{♯ T (↓ᵈ j x δ)}) ⟩
      ♯ S (↓ᵈ j x δ) →ᵒ ♯ T (↓ᵈ j x δ)
    ∎
... | Now | Later = λ δ j k k≤j →
    let strongS = strong-now (strong S x) time-x1 δ j k k≤j in
    let strongT = strong-later (strong T x) time-x2 δ j k k≤j in
      ♯ S δ →ᵒ ♯ T δ
    ⩦⟨ ≡ᵒ-sym (lemma17ᵒ k) ⟩ 
      ↓ᵒ (1 + k) (♯ S δ →ᵒ ♯ T δ)
    ⩦⟨ cong-↓ᵒ k (nonexpansive-→{♯ S δ}{♯ T δ}) ⟩ 
      ↓ᵒ (1 + k) (↓ᵒ (1 + k) (♯ S δ) →ᵒ ↓ᵒ (1 + k) (♯ T δ))
    ⩦⟨ cong-↓ᵒ k (cong-↓ᵒ (1 + k) (cong-→{↓ᵒ (1 + k) (♯ S δ)}{↓ᵒ (1 + k) (♯ S δ)} (≡ᵒ-refl refl) strongT)) ⟩ 
      ↓ᵒ (1 + k) (↓ᵒ (1 + k) (♯ S δ) →ᵒ ↓ᵒ (1 + k) (♯ T (↓ᵈ j x δ)))
    ⩦⟨ ≡ᵒ-sym (cong-↓ᵒ k (nonexpansive-→{♯ S δ}{♯ T (↓ᵈ j x δ)})) ⟩ 
      ↓ᵒ (1 + k) (♯ S δ →ᵒ ♯ T (↓ᵈ j x δ))
    ⩦⟨ lemma17ᵒ k ⟩ 
      ♯ S δ →ᵒ ♯ T (↓ᵈ j x δ)
    ⩦⟨ nonexpansive-→{♯ S δ}{♯ T (↓ᵈ j x δ)} ⟩ 
      ↓ᵒ k (♯ S δ) →ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ))
    ⩦⟨ cong-↓ᵒ k (cong-→ strongS (≡ᵒ-refl refl)) ⟩ 
      ↓ᵒ k (♯ S (↓ᵈ j x δ)) →ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ))
    ⩦⟨ ≡ᵒ-sym (nonexpansive-→{♯ S (↓ᵈ j x δ)}{♯ T (↓ᵈ j x δ)}) ⟩ 
      ♯ S (↓ᵈ j x δ) →ᵒ ♯ T (↓ᵈ j x δ)
    ∎
... | Later | Now = λ δ j k k≤j →
    let strongS = strong-later (strong S x) time-x1 δ j k k≤j in
    let strongT = strong-now (strong T x) time-x2 δ j k k≤j in
      ♯ S δ →ᵒ ♯ T δ
    ⩦⟨ ≡ᵒ-sym (lemma17ᵒ k) ⟩ 
      ↓ᵒ (1 + k) (♯ S δ →ᵒ ♯ T δ)
    ⩦⟨ cong-↓ᵒ k (nonexpansive-→{♯ S δ}{♯ T δ}) ⟩ 
      ↓ᵒ (1 + k) (↓ᵒ (1 + k) (♯ S δ) →ᵒ ↓ᵒ (1 + k) (♯ T δ))
    ⩦⟨ cong-↓ᵒ k (cong-↓ᵒ (1 + k) (cong-→ strongS (≡ᵒ-refl refl))) ⟩ 
      ↓ᵒ (1 + k) (↓ᵒ (1 + k) (♯ S (↓ᵈ j x δ)) →ᵒ ↓ᵒ (1 + k) (♯ T δ))
    ⩦⟨ ≡ᵒ-sym (cong-↓ᵒ k (nonexpansive-→{♯ S (↓ᵈ j x δ)}{♯ T δ})) ⟩ 
      ↓ᵒ (1 + k) (♯ S (↓ᵈ j x δ) →ᵒ ♯ T δ)
    ⩦⟨ lemma17ᵒ k ⟩ 
      ♯ S (↓ᵈ j x δ) →ᵒ ♯ T δ
    ⩦⟨ nonexpansive-→{♯ S (↓ᵈ j x δ)}{♯ T δ} ⟩ 
      ↓ᵒ k (♯ S (↓ᵈ j x δ)) →ᵒ ↓ᵒ k (♯ T δ)
    ⩦⟨ cong-↓ᵒ k (cong-→{↓ᵒ k (♯ S (↓ᵈ j x δ))}
                     {↓ᵒ k (♯ S (↓ᵈ j x δ))}{↓ᵒ k (♯ T δ)}{↓ᵒ k (♯ T (↓ᵈ j x δ))} (≡ᵒ-refl refl) strongT) ⟩ 
      ↓ᵒ k (♯ S (↓ᵈ j x δ)) →ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ))
    ⩦⟨ ≡ᵒ-sym (nonexpansive-→{♯ S _}{♯ T _}) ⟩ 
      ♯ S (↓ᵈ j x δ) →ᵒ ♯ T (↓ᵈ j x δ)
    ∎
... | Later | Later = λ δ j k k≤j →
    let strongS = strong-later (strong S x) time-x1 δ j k k≤j in
    let strongT = strong-later (strong T x) time-x2 δ j k k≤j in
      ♯ S δ →ᵒ ♯ T δ
    ⩦⟨ nonexpansive-→{♯ S δ}{♯ T δ} ⟩ 
      ↓ᵒ (1 + k) (♯ S δ) →ᵒ ↓ᵒ (1 + k) (♯ T δ)
    ⩦⟨ cong-↓ᵒ (1 + k) (cong-→ strongS strongT) ⟩ 
      ↓ᵒ (1 + k) (♯ S (↓ᵈ j x δ)) →ᵒ ↓ᵒ (1 + k) (♯ T (↓ᵈ j x δ))
    ⩦⟨ ≡ᵒ-sym (nonexpansive-→{♯ S _}{♯ T _}) ⟩ 
      ♯ S (↓ᵈ j x δ) →ᵒ ♯ T (↓ᵈ j x δ)
    ∎
\end{code}
\caption{Implication is a strong environment functional.}
\label{fig:strong-imp}
\end{figure}

We define the open variant of implication in SIL by constructing the
following record, using the proofs from this subsection.

\begin{code}
S →ˢ T = record { ♯ = λ δ → ♯ S δ →ᵒ ♯ T δ ; strong = strong-imp S T
                ; congr = λ d=d′ → cong-→ (congr S d=d′) (congr T d=d′) }
\end{code}

\noindent This completes the definition of the open logicla connectives of SIL.
Next we turn to the proof theory of SIL.


\clearpage


\section{Proof Theory for Step-Indexed Logic}
\label{sec:proofs}

The entailment relation of SIL $𝒫 ⊢ᵒ ϕ$ says that if the list of
propositions $𝒫$ are true at time $k$, then $ϕ$ must also be true at
$k$. We define the following function to interpret a list of
propositions as the conjunction of its elements.

\begin{code}
Πᵒ : List Setᵒ → Setᵒ
Πᵒ [] = ⊤ᵒ
Πᵒ (ϕ ∷ 𝒫) = ϕ ×ᵒ Πᵒ 𝒫 
\end{code}

\noindent Let 𝒫 range over lists of set-indexed propositions.

\begin{code}
variable 𝒫 : List Setᵒ
\end{code}

\noindent The meaning of a list of step-indexed propositions is
downward closed because each proposition is downward closed.

\begin{code}
downClosed-Πᵒ : (𝒫 : List Setᵒ) → downClosed (# (Πᵒ 𝒫))
downClosed-Πᵒ [] = λ n _ k _ → tt
downClosed-Πᵒ (ϕ ∷ 𝒫) n (ϕn , ⊨𝒫n) k k≤n = (down ϕ n ϕn k k≤n) , (downClosed-Πᵒ 𝒫 n ⊨𝒫n k k≤n)
\end{code}

\noindent We can now define entailment relation as described above.
We choose to make the relation \textsf{abstract} because that improves
Agda's inference of implicit parameters in the proof rules.

\begin{code}
abstract 
  infix 1 _⊢ᵒ_
  _⊢ᵒ_ : List Setᵒ → Setᵒ → Set
  𝒫 ⊢ᵒ ϕ = ∀ n → # (Πᵒ 𝒫) n → # ϕ n
\end{code}

\noindent We define the following introduction and elimination rules
for the entailment relation to provide an explicit way to fold and
unfold its definition.

\begin{code}
abstract
  ⊢ᵒI : (∀ n → # (Πᵒ 𝒫) n → # ϕ n) → 𝒫 ⊢ᵒ ϕ
  ⊢ᵒI 𝒫→ϕ = 𝒫→ϕ

  ⊢ᵒE : 𝒫 ⊢ᵒ ϕ → (∀ n → # (Πᵒ 𝒫) n → # ϕ n)
  ⊢ᵒE 𝒫⊢ϕ = 𝒫⊢ϕ
\end{code}

Now we proceed to define the proof rules of SIL. The first, \textsf{mono}ᵒ
says that if ϕ is true now, it is also true later.

\begin{code}
abstract
  monoᵒ : 𝒫 ⊢ᵒ ϕ  →  𝒫 ⊢ᵒ  ▷ᵒ ϕ
  monoᵒ {𝒫}{ϕ} ⊢ϕ zero ⊨𝒫n = tt
  monoᵒ {𝒫}{ϕ} ⊢ϕ (suc n) ⊨𝒫n = ⊢ϕ n (downClosed-Πᵒ 𝒫 (suc n) ⊨𝒫n n (n≤1+n n))
\end{code}

The analog of mathematical induction in SIL is called \textsf{lob}ᵒ
induction.  It says that in a proof of ϕ, it is permissible to assume
$▷ᵒ\,ϕ$.  The definition of \textsf{lob}ᵒ induction is by recursion on
the step index. In the base case, we use the fact that ϕ is true at zero.
For the induction step, we feed the induction hypothesis into the
premise named \textsf{step}.

\begin{code}
abstract
  lobᵒ : (▷ᵒ ϕ) ∷ 𝒫 ⊢ᵒ ϕ  →  𝒫 ⊢ᵒ ϕ
  lobᵒ {ϕ}{𝒫} step zero ⊨𝒫n = tz ϕ
  lobᵒ {ϕ}{𝒫} step (suc n) ⊨𝒫sn =
    let ⊨𝒫n = downClosed-Πᵒ 𝒫 (suc n) ⊨𝒫sn n (n≤1+n n) in
    let ϕn = lobᵒ {ϕ}{𝒫} step n ⊨𝒫n in
    step (suc n) (ϕn , ⊨𝒫sn)
\end{code}

The next few proof rules say that the later operator distributes through
the other logical connectives. The following says that ▷ᵒ distributes
through ×ᵒ.

\begin{code}
abstract
  ▷× : 𝒫 ⊢ᵒ (▷ᵒ (ϕ ×ᵒ ψ))  →  𝒫 ⊢ᵒ (▷ᵒ ϕ) ×ᵒ (▷ᵒ ψ)
  ▷× ▷ϕ×ψ zero = λ _ → tt , tt
  ▷× ▷ϕ×ψ (suc n) = ▷ϕ×ψ (suc n)
\end{code}

\noindent Next, we have that ▷ᵒ distributes through ⊎ᵒ.

\begin{code}
abstract
  ▷⊎ : 𝒫 ⊢ᵒ (▷ᵒ (ϕ ⊎ᵒ ψ))  →  𝒫 ⊢ᵒ (▷ᵒ ϕ) ⊎ᵒ (▷ᵒ ψ)
  ▷⊎ ▷ϕ⊎ψ zero = λ _ → inj₁ tt
  ▷⊎ ▷ϕ⊎ψ (suc n) = ▷ϕ⊎ψ (suc n) 
\end{code}

\noindent Also, ▷ᵒ distributes through implication.

\begin{code}
abstract
  ▷→ : 𝒫 ⊢ᵒ (▷ᵒ (ϕ →ᵒ ψ))  →  𝒫 ⊢ᵒ (▷ᵒ ϕ) →ᵒ (▷ᵒ ψ)
  ▷→ ▷ϕ→ψ zero ⊨𝒫n .zero z≤n tt = tt
  ▷→ ▷ϕ→ψ (suc n) ⊨𝒫n .zero z≤n ▷ϕj = tt
  ▷→ ▷ϕ→ψ (suc n) ⊨𝒫n (suc j) (s≤s j≤n) ϕj = ▷ϕ→ψ (suc n) ⊨𝒫n j j≤n ϕj
\end{code}

\noindent Finally, ▷ᵒ distributes through the forall quantifier.

\begin{code}
abstract
  ▷∀ : ∀{ϕᵃ : A → Setᵒ} → 𝒫 ⊢ᵒ ▷ᵒ (∀ᵒ[ a ] ϕᵃ a)  →  𝒫 ⊢ᵒ (∀ᵒ[ a ] ▷ᵒ (ϕᵃ a))
  ▷∀ 𝒫⊢▷∀ϕᵃ zero ⊨𝒫n a = tt
  ▷∀ 𝒫⊢▷∀ϕᵃ (suc n) ⊨𝒫sn a = 𝒫⊢▷∀ϕᵃ (suc n) ⊨𝒫sn a
\end{code}

The \textsf{subst}ᵒ rule is the analog of Agda's \textsf{subst}, which
says that if ϕ and ψ are equivalent, then proving ϕ suffices to prove
ψ.  In general, for the SIL proof rules that have an analogous rule in
Agda, we use the same name with a postfix of ᵒ.

\begin{code}
abstract
  substᵒ : ϕ ≡ᵒ ψ  →  𝒫 ⊢ᵒ ϕ  →  𝒫 ⊢ᵒ ψ
  substᵒ ϕ=ψ 𝒫⊢ϕ n ⊨𝒫n = ⇔-to (ϕ=ψ n) (𝒫⊢ϕ n ⊨𝒫n)
\end{code}

The true formula is trivially provable.

\begin{code}
abstract
  ttᵒ : 𝒫 ⊢ᵒ ⊤ᵒ
  ttᵒ n _ = tt  
\end{code}

The elimination rule for false is the usual one.
Anything is provable from false.

\begin{code}
abstract
  ⊥-elimᵒ : 𝒫 ⊢ᵒ ⊥ᵒ → (ϕ : Setᵒ) → 𝒫 ⊢ᵒ ϕ
  ⊥-elimᵒ ⊢⊥ ϕ zero ⊨𝒫n = tz ϕ
  ⊥-elimᵒ ⊢⊥ ϕ (suc n) ⊨𝒫sn = ⊥-elim (⊢⊥ (suc n) ⊨𝒫sn)
\end{code}

TODO: explain
\begin{code}
⊥⇒⊥ᵒ : ⊥ → 𝒫 ⊢ᵒ ⊥ᵒ
⊥⇒⊥ᵒ ()

⊥ᵒ⇒⊥ : [] ⊢ᵒ ⊥ᵒ → ⊥
⊥ᵒ⇒⊥ ⊢⊥ = ⊢ᵒE ⊢⊥ 1 tt
\end{code}

The introduction and elimination rules for conjunction are the
standard ones.

\begin{code}
abstract
  _,ᵒ_ : 𝒫 ⊢ᵒ ϕ  →  𝒫 ⊢ᵒ ψ  →  𝒫 ⊢ᵒ ϕ ×ᵒ ψ
  (𝒫⊢ϕ ,ᵒ 𝒫⊢ψ) n ⊨𝒫n = 𝒫⊢ϕ n ⊨𝒫n , 𝒫⊢ψ n ⊨𝒫n

  proj₁ᵒ : 𝒫 ⊢ᵒ ϕ ×ᵒ ψ  →  𝒫 ⊢ᵒ ϕ
  proj₁ᵒ 𝒫⊢ϕ×ψ n ⊨𝒫n = proj₁ (𝒫⊢ϕ×ψ n ⊨𝒫n)

  proj₂ᵒ : 𝒫 ⊢ᵒ ϕ ×ᵒ ψ  →  𝒫 ⊢ᵒ ψ
  proj₂ᵒ 𝒫⊢ϕ×ψ n ⊨𝒫n = proj₂ (𝒫⊢ϕ×ψ n ⊨𝒫n)
\end{code}

For disjunction, we have the usual injection rules and the case
analysis rule.

\begin{code}
abstract
  inj₁ᵒ : 𝒫 ⊢ᵒ ϕ → 𝒫 ⊢ᵒ ϕ ⊎ᵒ ψ
  inj₁ᵒ 𝒫⊢ϕ n ⊨𝒫n = inj₁ (𝒫⊢ϕ n ⊨𝒫n)

  inj₂ᵒ : 𝒫 ⊢ᵒ ψ → 𝒫 ⊢ᵒ ϕ ⊎ᵒ ψ
  inj₂ᵒ 𝒫⊢ψ n ⊨𝒫n = inj₂ (𝒫⊢ψ n ⊨𝒫n)

  caseᵒ : 𝒫 ⊢ᵒ ϕ ⊎ᵒ ψ  →  ϕ ∷ 𝒫 ⊢ᵒ þ  →  ψ ∷ 𝒫 ⊢ᵒ þ  →  𝒫 ⊢ᵒ þ
  caseᵒ 𝒫⊢ϕ⊎ψ ϕ∷𝒫⊢þ ψ∷𝒫⊢þ n ⊨𝒫n
      with 𝒫⊢ϕ⊎ψ n ⊨𝒫n
  ... | inj₁ ϕn = ϕ∷𝒫⊢þ n (ϕn , ⊨𝒫n)
  ... | inj₂ ψn = ψ∷𝒫⊢þ n (ψn , ⊨𝒫n)
\end{code}

Regarding implication, we also define the standard introduction and
elimination rules.

\begin{code}
abstract
  →ᵒI : ϕ ∷ 𝒫 ⊢ᵒ ψ  →  𝒫 ⊢ᵒ ϕ →ᵒ ψ
  →ᵒI {𝒫 = 𝒫} ϕ∷𝒫⊢ψ n ⊨𝒫n j j≤n ϕj = ϕ∷𝒫⊢ψ j (ϕj , downClosed-Πᵒ 𝒫 n ⊨𝒫n j j≤n)

  →ᵒE : 𝒫 ⊢ᵒ ϕ →ᵒ ψ  →  𝒫 ⊢ᵒ ϕ  →  𝒫 ⊢ᵒ ψ
  →ᵒE {𝒫} 𝒫⊢ϕ→ψ 𝒫⊢ϕ n ⊨𝒫n = let ϕn = 𝒫⊢ϕ n ⊨𝒫n in 𝒫⊢ϕ→ψ n ⊨𝒫n n ≤-refl ϕn
\end{code}

Next we define a derived rule that caters to a common reasoning
pattern in which we know that ϕ implies ψ, but you have ▷ᵒ ϕ and need
to prove ▷ᵒ ψ.

\begin{code}
abstract
  ▷→▷ : 𝒫 ⊢ᵒ ▷ᵒ ϕ  →  ϕ ∷ 𝒫 ⊢ᵒ ψ  →  𝒫 ⊢ᵒ ▷ᵒ ψ
  ▷→▷ {𝒫}{ϕ}{ψ} ▷ϕ ϕ⊢ψ n ⊨𝒫n =
    let ▷ψ = →ᵒE{𝒫}{▷ᵒ ϕ}{▷ᵒ ψ} (▷→{𝒫}{ϕ}{ψ} (monoᵒ{𝒫}{ϕ →ᵒ ψ} (→ᵒI{ϕ}{𝒫}{ψ} ϕ⊢ψ))) ▷ϕ in
    ▷ψ n ⊨𝒫n
\end{code}

The introduction rule for the forall quantifier uses an Agda function
for the quantification, a function from an element of type \textsf{A}
to a proof of $ϕᵃ \, a$. We introduce the syntax $Λᵒ[ a ] ϕ$ for
this introduction rule. The elimination rule, \textsf{inst}ᵒ,
instantiates the universal statement to a particular choice
of $a$ in $A$.

\begin{code}
abstract
  Λᵒ : {ϕᵃ : A → Setᵒ} → (∀ a → 𝒫 ⊢ᵒ ϕᵃ a)  →  𝒫 ⊢ᵒ ∀ᵒ ϕᵃ
  Λᵒ ∀ϕᵃa n ⊨𝒫n a = ∀ϕᵃa a n ⊨𝒫n

Λᵒ-syntax = Λᵒ
infix 1 Λᵒ-syntax
syntax Λᵒ-syntax (λ a → ⊢ϕᵃa) = Λᵒ[ a ] ⊢ϕᵃa

abstract
  ∀ᵒE : ∀{ϕᵃ : A → Setᵒ} → 𝒫 ⊢ᵒ ∀ᵒ ϕᵃ  →  (a : A)  →  𝒫 ⊢ᵒ ϕᵃ a
  ∀ᵒE ⊢∀ϕᵃ a n ⊨𝒫n = ⊢∀ϕᵃ n ⊨𝒫n a
\end{code}

\begin{comment}
\noindent In some situations Agda has difficulty infering the ϕᵃ
parameter, so we also provide the following version of ∀ᵒE with an
explicit annotation.

\begin{code}
∀ᵒE-annot : ∀(ϕᵃ : A → Setᵒ) → 𝒫 ⊢ᵒ ∀ᵒ ϕᵃ  →  (a : A)  →  𝒫 ⊢ᵒ ϕᵃ a
∀ᵒE-annot ϕᵃ = ∀ᵒE{ϕᵃ = ϕᵃ}

∀ᵒE-annot-syntax = ∀ᵒE-annot
infix 1 ∀ᵒE-annot-syntax
syntax ∀ᵒE-annot-syntax (λ a → ϕᵃ) ∀ϕ b = instᵒ ∀ϕ ⦂∀[ a ] ϕᵃ at b
\end{code}
\end{comment}

The introduction rule for the existential quantifier requires witness $a ∈ A$ and
a proof of $ϕᵃ \, a$ to show that $∃ᵒ ϕᵃ$. The elimination rule says that
if you have a proof of $∃ᵒ ϕᵃ$, then to prove some proposition $þ$ it
suffies to prove that $ϕᵃ \, a$ entails $þ$ for an arbitrary $a ∈ A$.

\begin{code}
abstract
  ∃ᵒI : ∀{ϕᵃ : A → Setᵒ}{{_ : Inhabited A}} → (a : A)  →  𝒫 ⊢ᵒ ϕᵃ a  →  𝒫 ⊢ᵒ ∃ᵒ ϕᵃ
  ∃ᵒI a ⊢ϕᵃa n ⊨𝒫n = a , (⊢ϕᵃa n ⊨𝒫n)

  ∃ᵒE : ∀{ϕᵃ : A → Setᵒ}{þ : Setᵒ}{{_ : Inhabited A}}
     → 𝒫 ⊢ᵒ ∃ᵒ ϕᵃ  →  (∀ a → ϕᵃ a ∷ 𝒫 ⊢ᵒ þ)  →  𝒫 ⊢ᵒ þ
  ∃ᵒE {þ = þ} ⊢∃ϕᵃ cont zero ⊨𝒫n = tz þ
  ∃ᵒE ⊢∃ϕᵃ cont (suc n) ⊨𝒫n
      with ⊢∃ϕᵃ (suc n) ⊨𝒫n
  ... | (a , ϕᵃasn) = cont a (suc n) (ϕᵃasn , ⊨𝒫n)
\end{code}

The introduction rule for the constant formula says that a proof of
$p$ is required to prove $p ᵒ$. The elimination rule says that
if you have $p ᵒ$, then to prove an arbitrary proposition þ,
one can provide an Agda function that quantifies over $p$.

\begin{code}
abstract
  pureᵒI : ∀{p : Set} → p → 𝒫 ⊢ᵒ p ᵒ
  pureᵒI s zero ⊨𝒫n = tt
  pureᵒI s (suc n) ⊨𝒫n = s

  pureᵒE : 𝒫 ⊢ᵒ p ᵒ  →  (p → 𝒫 ⊢ᵒ þ)  →  𝒫 ⊢ᵒ þ
  pureᵒE {𝒫} {p} {R} ⊢p p→⊢R zero 𝒫n = tz R
  pureᵒE {𝒫} {p} {R} ⊢p p→⊢R (suc n) 𝒫n = p→⊢R (⊢p (suc n) 𝒫n) (suc n) 𝒫n

pureᵒE-syntax = pureᵒE
infix 1 pureᵒE-syntax
syntax pureᵒE-syntax pᵒ (λ p → ⊢þ) = let-pureᵒ[ p ] pᵒ within ⊢þ
\end{code}

The next two rules provide ways to make use of premises to the left of
the turnstile.  The first rule references the premise at position
zero.

\begin{code}
abstract
  Zᵒ : ϕ ∷ 𝒫 ⊢ᵒ ϕ
  Zᵒ n (ϕn , ⊨𝒫n) = ϕn
\end{code}

\noindent The second rule removes the premise at position zero, so it
is a ``weakening'' rule.

\begin{code}
abstract
  Sᵒ : 𝒫 ⊢ᵒ ψ  →  ϕ ∷ 𝒫 ⊢ᵒ ψ
  Sᵒ 𝒫⊢ψ n (ϕn , ⊨𝒫n) = 𝒫⊢ψ n ⊨𝒫n
\end{code}

TODO: explain this
\begin{code}
λᵒ : ∀ ϕ → (ϕ ∷ 𝒫 ⊢ᵒ ϕ → ϕ ∷ 𝒫 ⊢ᵒ ψ) → 𝒫 ⊢ᵒ ϕ →ᵒ ψ
λᵒ ϕ f = →ᵒI{ϕ = ϕ} (f Zᵒ)

λᵒ-syntax = λᵒ
infix 1 λᵒ-syntax
syntax λᵒ-syntax ϕ (λ ⊢ϕ → ⊢ψ) = λᵒ[ ⊢ϕ ⦂ ϕ ] ⊢ψ
\end{code}

Finally, we provide a rule that lets one export a proof of $ϕ$
from SIL into Agda. That is, given a proof of ϕ in SIL, to prove
some other arbitrary proposition ψ, it suffices to provide
a function that is parameterized over $ϕ$ at a non-zero index
and that produces a proof of ψ.

\begin{code}
let-sucᵒ : 𝒫 ⊢ᵒ ϕ  →  (∀{n} → # ϕ (suc n) → 𝒫 ⊢ᵒ ψ)  →  𝒫 ⊢ᵒ ψ
let-sucᵒ {𝒫}{ϕ}{ψ} ⊢ϕ ϕsn⊢ψ =
    ⊢ᵒI λ { zero x → tz ψ
               ; (suc n) 𝒫sn → let ⊢ψ = ϕsn⊢ψ (⊢ᵒE ⊢ϕ (suc n) 𝒫sn) in ⊢ᵒE ⊢ψ (suc n) 𝒫sn }

let-sucᵒ-syntax = let-sucᵒ
infix 1 let-sucᵒ-syntax
syntax let-sucᵒ-syntax ϕ (λ ϕsuc → ⊢ψ) = let-sucᵒ[ ϕsuc ] ϕ within ⊢ψ
\end{code}


TODO: move the following to an appropriate location -Jeremy

\begin{code}
foldᵒ : ∀{𝒫} (P : A → Setˢ (A ∷ []) (Later ∷ [])) (a : A) →  𝒫 ⊢ᵒ letᵒ (μᵒ P) (P a)  →  𝒫 ⊢ᵒ μᵒ P a
foldᵒ P a P[μP] = substᵒ (≡ᵒ-sym (fixpointᵒ P a)) P[μP]
\end{code}

\begin{code}
unfoldᵒ : ∀{𝒫} (P : A → Setˢ (A ∷ []) (Later ∷ [])) (a : A) →  𝒫 ⊢ᵒ μᵒ P a  →  𝒫 ⊢ᵒ letᵒ (μᵒ P) (P a)
unfoldᵒ P a μP = substᵒ (fixpointᵒ P a) μP
\end{code}



