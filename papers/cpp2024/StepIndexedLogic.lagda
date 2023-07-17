\begin{comment}
\begin{code}
module cpp2024.StepIndexedLogic where

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
variable ϕ ψ þ : Setᵒ
\end{code}
Let $p, q, r$ range over (regular) propositions.
\begin{code}
variable p q r : Set
\end{code}

The ``true'' formula for SIL is embedded in Agda by defining an instance
of the $\mathsf{Set}ᵒ$ record type, with the representation function
mapping every natural number to true. The proofs of
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

The equivalence of predicates applied to the same argument forms and
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
on three concepts that we introduce in this section: functionals,
$k$-approximation, and iteration.  In the section we introduce these
concepts and prove several important lemmas concerning them. We adapt
these definitions and lemmas from \citet{Appel:2001aa}, who apply them
to the semantics of recursive types.

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

The $k$-approximation of a step-indexed predicate, $↓\, k\, ϕ$, is true at
$i$ if $ϕ$ at $i$ is true and $i < k$, except when $k = 0$, in which
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

The $k$-approximations of any two step-indexed propositions are
equivalent when $k=0$ and $k=1$.

\begin{code}
↓ᵒ-zero : ↓ᵒ zero ϕ ≡ᵒ ↓ᵒ zero ψ
↓ᵒ-zero = ≡ᵒ-intro λ {zero → (λ _ → tt) , λ _ → tt
                     ; (suc i) → (λ {()}) , (λ {()})}

↓ᵒ-one : ↓ᵒ 1 ϕ ≡ᵒ ↓ᵒ 1 ψ
↓ᵒ-one = ≡ᵒ-intro λ {zero → (λ _ → tt) , λ _ → tt
                     ; (suc i) → (λ { (s≤s () , _)}) , (λ { (s≤s () , _)})}
\end{code}

Given two equivalent propositions $ϕ$ and $ψ$, their $k$-approximations are also
eqivalent.

\begin{code}
cong-↓ᵒ : ∀ k → ϕ ≡ᵒ ψ → ↓ᵒ k ϕ ≡ᵒ ↓ᵒ k ψ
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

A functional is \emph{wellfounded} if applying $k$-approximation to
its input does not change the $k{\plus}1$-approximation of its output.
Intuitively, this corresponds to functions that only use their input
at one step later in time.

\begin{code}
wellfoundedᵖ : ∀ (f : Predᵒ A → Predᵒ A) → Set₁
wellfoundedᵖ f = ∀ a P k → ↓ᵒ (suc k) (f P a) ≡ᵒ ↓ᵒ (suc k) (f (↓ᵖ k P) a)
\end{code}

The nth iteration of a function, $f^n$, is implemented by the
following $\mathsf{iter}$ function.

\begin{code}
iter : ∀ {ℓ} {A : Set ℓ} → ℕ → (A → A) → (A → A)
iter zero    f  =  id
iter (suc n) f  =  f ∘ iter n f
\end{code}

\noindent Iterating $k$ times is equivalent to iterating $j$ times
followed by $k ∸ j$ times, assuming that $j \leq k$.

\begin{code}
iter-subtract : ∀{ℓ}{A : Set ℓ}{a : A} (F : A → A) (j k : ℕ) → j ≤ k
  → iter j F (iter (k ∸ j) F a) ≡ iter k F a
iter-subtract {A = A} {a} F .zero k z≤n = refl
iter-subtract {A = A} {a} F (suc j) (suc k) (s≤s j≤k)
  rewrite iter-subtract{A = A}{a} F j k j≤k = refl
\end{code}

Suppose a functional is wellfounded and congruent.  If you iterate the
functional $j$ times and then take the $j$-approximation, the
initial predicate doesn't matter. This corresponds to Lemma 15 (part 1)
of \citet{Appel:2001aa}.

\begin{code}
lemma15a : ∀ j (f : Predᵒ A → Predᵒ A) (a : A) → wellfoundedᵖ f → congruentᵖ f
  → ↓ᵒ j (iter j f P a) ≡ᵒ ↓ᵒ j (iter j f Q a)
lemma15a zero f a wf-f cong-f = ↓ᵒ-zero
lemma15a {A}{P}{Q} (suc j) f a wf-f cong-f =
  ↓ᵒ (suc j) (f (iter j f P) a)           ⩦⟨ wf-f a (iter j f P) j ⟩ 
  ↓ᵒ (suc j) (f (↓ᵖ j (iter j f P)) a)    ⩦⟨ cong-↓ (cong-f λ a → lemma15a j f a wf-f cong-f) a ⟩
  ↓ᵒ (suc j) (f (↓ᵖ j (iter j f Q)) a)    ⩦⟨ ≡ᵒ-sym (wf-f a (iter j f Q) j) ⟩
  ↓ᵒ (suc j) (f (iter j f Q) a)           ∎
\end{code}

Again assuming that the functional is wellfounded and congruent, if
you take the $j$ approximation of the output, iterating the
functional more then $j$ times does not change the result.  This
corresponds to Lemma 15 (part 2) of \citet{Appel:2001aa}.

\begin{code}
lemma15b : (k j : ℕ) (f : Predᵒ A → Predᵒ A) (a : A) → j ≤ k → wellfoundedᵖ f → congruentᵖ f
   → ↓ᵒ j (iter j f P a) ≡ᵒ ↓ᵒ j (iter k f P a)
lemma15b {A}{P} k j f a j≤k wf-f cong-f =
  ↓ᵒ j (iter j f P a)                     ⩦⟨ lemma15a j f a wf-f cong-f ⟩
  ↓ᵒ j (iter j f (iter (k ∸ j) f P) a)    ⩦⟨ cong-↓{A}{j}{iter j f (iter (k ∸ j) f P)}{iter k f P}
                                             (λ a → ≡ᵖ-refl (iter-subtract f j k j≤k)) a ⟩
  ↓ᵒ j (iter k f P a)   ∎
\end{code}

Appoximations are idempotent in the sense that applying the $k$ and
$j$ approximations in sequence, when $j \leq k$, is equivalent to
just applying the $j$ approximation.

\begin{code}
double-↓ᵒ : ∀{j k} (S : Setᵒ) → j ≤ k → ↓ᵒ j (↓ᵒ k S) ≡ᵒ ↓ᵒ j S
double-↓ᵒ {j}{k} S j≤k = ≡ᵒ-intro aux
  where aux : ∀ i → ↓ j (↓ k (# S)) i ⇔ ↓ j (# S) i
        aux zero = (λ _ → tt) , (λ _ → tt)
        aux (suc i) = (λ {(a , b , c) → a , c}) , λ {(a , b) → a , ≤-trans a j≤k , b}
\end{code}

This is a generalization of Lemma 17 of \citet{Appel:2001aa}, in which $j = k - 1$.

\begin{code}
lemma17ᵒ : ∀ k → ↓ᵒ k (↓ᵒ (suc k) ϕ) ≡ᵒ ↓ᵒ k ϕ
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
  ∅ : Times []
  cons : Time → Times Γ → Times (A ∷ Γ)
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
laters [] = ∅
laters (A ∷ Γ) = cons Later (laters Γ)

var-now : ∀ (Γ : Context) → ∀{A} → (x : Γ ∋ A) → Times Γ
var-now (B ∷ Γ) zeroˢ = cons Now (laters Γ)
var-now (B ∷ Γ) (sucˢ x) = cons Later (var-now Γ x)
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
_∪_ {[]} Δ₁ Δ₂ = ∅
_∪_ {A ∷ Γ} (cons x Δ₁) (cons y Δ₂) = cons (choose x y) (Δ₁ ∪ Δ₂)
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

letˢ : (A → Setˢ Γ Δ) → Setˢ (A ∷ Γ) (cons Later Δ) → Setˢ Γ Δ   

μˢ : (A → Setˢ (A ∷ Γ) (cons Later Δ)) → (A → Setˢ Γ Δ)

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
functional is congruent and that it is wellfounded in a sense that is
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
wellfounded of \citet{Appel:2001aa}.  A direct adaptation of
nonexpansive to our setting yields the following, which says that
given any environment $δ$ and variable $x$, the $k$-approximation of
$P\app δ$ is equivalent to the $k$-approximation of $P$ applied to the
$k$ approximation of the $δ$ with respect to variable $x$.
\[
  ↓\, k\, (P\, δ) ≡ᵒ ↓\, k\, (P\, (↓ᵈ\, k\, x\, δ)
\]
Simlarly, the direct adaption of wellfounded to our setting says
that the $k \plus 1$ approximation of $P\app δ$ is equivalent to the
$k \plus 1$ approximation of $P$ applied to the $k$ approximation of
the $δ$ with respect to variable $x$.
\[
  ↓\, (k \plus 1) \, (P\, δ) ≡ᵒ ↓\, (k \plus 1) \, (P\, (↓ᵈ\, k\, x\, δ)
\]
However, these definitions of nonexpansive and wellfounded were not
general enough to handle more than one recursive predicate in scope.
(Recall that \citet{Appel:2001aa} neglected to prove that $μ$
preserves nonexpansive and wellfounded propositions.)  So instead of
taking the $k$-approximation of the input $δ$, we generalize $k$ to
any $j$ greater or equal to $k$, yielding the following notions of
\emph{strongly nonexpansive} and \emph{strongly wellfounded}
functionals.

\begin{code}
strongly-nonexpansive : (x : Γ ∋ A) → (RecEnv Γ → Setᵒ) → Set₁
strongly-nonexpansive x F = ∀ δ j k → k ≤ j → ↓ᵒ k (F δ) ≡ᵒ ↓ᵒ k (F (↓ᵈ j x δ))

strongly-wellfounded : (x : Γ ∋ A) → (RecEnv Γ → Setᵒ) → Set₁
strongly-wellfounded x F = ∀ δ j k → k ≤ j → ↓ᵒ (suc k) (F δ) ≡ᵒ ↓ᵒ (suc k) (F (↓ᵈ j x δ))
\end{code}

We say that an environment functional $F$ is \emph{strong in variable $x$
at time $t$} if it is either strongly nonexpansive (when $t = \Now$) or
strongly wellfounded (when $t = \Later$).

\begin{code}
strong-var : (x : Γ ∋ A) → Time → (RecEnv Γ → Setᵒ) → Set₁
strong-var x Now F = strongly-nonexpansive x F
strong-var x Later F = strongly-wellfounded x F
\end{code}

\noindent Next we define the \textsf{timeof} function to lookup the
time for a variable $x$ in $Δ$.

\begin{code}
timeof : (x : Γ ∋ A) → Times Γ → Time
timeof {B ∷ Γ} zeroˢ (cons t Δ) = t
timeof {B ∷ Γ} (sucˢ x) (cons t Δ) = timeof x Δ
\end{code}

For convenience, we define the following two elimination principles
for functionals that are strong in a variable. If the variable's time
is \textsf{Now}, then the functional is strongly nonexpansive, and if
the time is \textsf{Later}, then the functional is strongly
wellfounded.

\begin{code}
strong-now : ∀{x : Γ ∋ A}{Δ : Times Γ}{F : RecEnv Γ → Setᵒ}
   → strong-var x (timeof x Δ) F → timeof x Δ ≡ Now → strongly-nonexpansive x F
strong-now gF eq rewrite eq = gF

strong-later : ∀{x : Γ ∋ A}{Δ : Times Γ}{F : RecEnv Γ → Setᵒ}
   → strong-var x (timeof x Δ) F → timeof x Δ ≡ Later → strongly-wellfounded x F
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
   → ↓ᵒ k (lookup{Γ}{A} x δ a) ≡ᵒ ↓ᵒ k (lookup{Γ}{A} x (↓ᵈ j y δ) a)
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
lookup-diff {C ∷ Γ} {cons t Δ} zeroˢ zeroˢ neq = ⊥-elim (neq refl)
lookup-diff {C ∷ Γ} {cons t Δ} zeroˢ (sucˢ y) neq = refl
lookup-diff {C ∷ Γ} {cons t Δ} (sucˢ x) zeroˢ neq = refl
lookup-diff {C ∷ Γ} {cons t Δ} (sucˢ x) (sucˢ y) neq = lookup-diff x y neq
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
in $x$ and strongly wellfounded in the other variables, which we show
in Figure~\ref{fig:strong-lookup}.

\begin{figure}[tbp]
\small
\begin{code}
strong-lookup : ∀{Γ}{A}{a} → (x : Γ ∋ A) → strong-fun (var-now Γ x) (λ δ → lookup x δ a)
strong-lookup {.(A ∷ _)} {A} {a} zeroˢ zeroˢ = SNE where
  SNE : strongly-nonexpansive zeroˢ (λ {(P , δ) → P a})
  SNE (P , δ) j k k≤j = ≡ᵒ-sym (double-↓ᵒ (P a) k≤j)
strong-lookup {.(A ∷ _)} {A} {a} zeroˢ (sucˢ y) rewrite timeof-later y = SWF where
  SWF : strongly-wellfounded (sucˢ y) (λ {(P , δ) → P a})
  SWF (P , δ) j k k≤j = ≡ᵒ-refl refl
strong-lookup {.(_ ∷ _)} {A} {a} (sucˢ x) zeroˢ = SWF where
  SWF : strongly-wellfounded zeroˢ (λ (P , δ) → lookup x δ a)
  SWF (P , δ) j k k≤j = ≡ᵒ-refl refl
strong-lookup {B ∷ Γ} {A} {a} (sucˢ x) (sucˢ y)
    with timeof y (var-now Γ x) in eq-y
... | Now = SNE where
    SNE : strongly-nonexpansive (sucˢ y) (λ {(P , δ) → lookup x δ a})
    SNE (P , δ) j k k≤j = ↓-lookup x y k≤j 
... | Later = SWF where
    timeof-diff : ∀{Γ}{Δ : Times Γ}{A}{B} (x : Γ ∋ A) (y : Γ ∋ B) → timeof x Δ ≡ Now → timeof y Δ ≡ Later
       → timeof x Δ ≢ timeof y Δ
    timeof-diff x y eq1 eq2 rewrite eq1 | eq2 = λ ()
    SWF : strongly-wellfounded (sucˢ y) (λ {(P , δ) → lookup x δ a})
    SWF (P , δ) j k k≤j =
      let eq = (lookup-diff{Γ}{δ = δ}{j} x y (timeof-diff x y (timeof-var-now x) eq-y)) in
      subst (λ X → ↓ᵒ (suc k) (lookup x δ a) ≡ᵒ ↓ᵒ (suc k) (X a)) (sym eq) (≡ᵒ-refl refl)
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

The operator $▷ᵒ$ is also wellfounded.

\begin{code}
WF-▷ : ∀{k} (S : Setᵒ) → ↓ᵒ (suc k) (▷ᵒ S) ≡ᵒ ↓ᵒ (suc k) (▷ᵒ (↓ᵒ k S))
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
  ↓ᵒ (suc k) (▷ᵒ (♯ S δ))                      ⩦⟨ WF-▷ {k} (♯ S δ) ⟩ 
  ↓ᵒ (suc k) (▷ᵒ (↓ᵒ k (♯ S δ)))               ⩦⟨ cong-↓ᵒ (suc k) (cong-▷ (strongS δ j k k≤j)) ⟩ 
  ↓ᵒ (suc k) (▷ᵒ (↓ᵒ k (♯ S (↓ᵈ j x δ))))      ⩦⟨ ≡ᵒ-sym (WF-▷ {k} (♯ S (↓ᵈ j x δ))) ⟩ 
  ↓ᵒ (suc k) (▷ᵒ (♯ S (↓ᵈ j x δ)))             ∎
... | Later rewrite timeof-later{Γ} x = λ δ j k k≤j →
  ↓ᵒ (suc k) (▷ᵒ (♯ S δ))                         ⩦⟨ ≡ᵒ-sym (lemma17ᵒ (suc k)) ⟩ 
  ↓ᵒ (suc k) (↓ᵒ (2 + k) (▷ᵒ (♯ S δ)))            ⩦⟨ cong-↓ᵒ (suc k) (WF-▷ _) ⟩
  ↓ᵒ (suc k) (↓ᵒ (2 + k) (▷ᵒ (↓ᵒ (suc k) (♯ S δ))))
                            ⩦⟨ cong-↓ᵒ (suc k) (cong-↓ᵒ (suc (suc k)) (cong-▷ (strongS δ j k k≤j))) ⟩
  ↓ᵒ (suc k) (↓ᵒ (2 + k) (▷ᵒ (↓ᵒ (suc k) (♯ S (↓ᵈ j x δ)))))  ⩦⟨ ≡ᵒ-sym (cong-↓ᵒ (suc k) (WF-▷ _)) ⟩
  ↓ᵒ (suc k) (↓ᵒ (2 + k) (▷ᵒ (♯ S (↓ᵈ j x δ))))               ⩦⟨ lemma17ᵒ (suc k) ⟩
  ↓ᵒ (suc k) (▷ᵒ (♯ S (↓ᵈ j x δ)))                            ∎
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
    ↓ᵒ k (↓ᵒ i (♯ S δ))                 ⩦⟨ permute-↓  ⟩ 
    ↓ᵒ i (↓ᵒ k (♯ S δ))                 ⩦⟨ cong-↓ᵒ i strongS ⟩ 
    ↓ᵒ i (↓ᵒ k (♯ S (↓ᵈ j x δ)))        ⩦⟨ permute-↓ ⟩
    ↓ᵒ k (↓ᵒ i (♯ S (↓ᵈ j x δ)))        ∎
... | Later = λ δ j k k≤j →
    let strongS = strong-later (strong S x) time-x δ j k k≤j in
    ↓ᵒ (suc k) (↓ᵒ i (♯ S δ))                 ⩦⟨ permute-↓  ⟩ 
    ↓ᵒ i (↓ᵒ (suc k) (♯ S δ))                 ⩦⟨ cong-↓ᵒ i strongS ⟩ 
    ↓ᵒ i (↓ᵒ (suc k) (♯ S (↓ᵈ j x δ)))        ⩦⟨ permute-↓ ⟩
    ↓ᵒ (suc k) (↓ᵒ i (♯ S (↓ᵈ j x δ)))        ∎
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
strong-let : ∀{Γ}{Δ : Times Γ}{A} (T : Setˢ (A ∷ Γ) (cons Later Δ)) (Sᵃ : A → Setˢ Γ Δ)
   → strong-fun Δ (λ δ → ♯ T ((λ a → ♯ (Sᵃ a) δ) , δ))
strong-let {Γ}{Δ}{A} T Sᵃ x
   with timeof x Δ in time-x
... | Now = λ δ j k k≤j →
    let strongTz = ((strong T) zeroˢ) ((λ a → ♯ (Sᵃ a) δ) , δ) j k k≤j in
    let strongTz2 = ((strong T) zeroˢ) ((λ a → ♯ (Sᵃ a) (↓ᵈ j x δ)) , (↓ᵈ j x δ))
                   j k k≤j in
    let strongTsx = strong-now{x = sucˢ x}{Δ = cons Now Δ} ((strong T) (sucˢ x)) time-x
                 ((λ a → ↓ᵒ j (♯ (Sᵃ a) δ)) , δ) j k k≤j in
    let EQ : ((λ a → ↓ᵒ j (♯ (Sᵃ a) δ)) , ↓ᵈ j x δ)
          ≡ᵈ ((λ a → ↓ᵒ j  (♯ (Sᵃ a) (↓ᵈ j x δ))) , ↓ᵈ j x δ)
        EQ = (λ a → strong-now (strong (Sᵃ a) x) time-x δ j j ≤-refl) , ≡ᵈ-refl in
    ↓ᵒ k (♯ T ((λ a → ♯ (Sᵃ a) δ) , δ))                      ⩦⟨ ≡ᵒ-sym (lemma17ᵒ k) ⟩
    ↓ᵒ k (↓ᵒ (suc k) (♯ T ((λ a → ♯ (Sᵃ a) δ) , δ)))         ⩦⟨ cong-↓ᵒ k strongTz ⟩
    ↓ᵒ k (↓ᵒ (suc k) (♯ T ((λ a → ↓ᵒ j (♯ (Sᵃ a) δ)) , δ)))  ⩦⟨ lemma17ᵒ k ⟩
    ↓ᵒ k (♯ T ((λ a → ↓ᵒ j (♯ (Sᵃ a) δ)) , δ))               ⩦⟨ strongTsx ⟩
    ↓ᵒ k (♯ T ((λ a → ↓ᵒ j (♯ (Sᵃ a) δ)) , ↓ᵈ j x δ))        ⩦⟨ cong-↓ᵒ k (congr T EQ) ⟩
    ↓ᵒ k (♯ T ((λ a → ↓ᵒ j (♯ (Sᵃ a) (↓ᵈ j x δ))) , ↓ᵈ j x δ))               ⩦⟨ ≡ᵒ-sym (lemma17ᵒ k) ⟩
    ↓ᵒ k (↓ᵒ (suc k) (♯ T ((λ a → ↓ᵒ j (♯ (Sᵃ a) (↓ᵈ j x δ))) , ↓ᵈ j x δ)))  ⩦⟨ cong-↓ᵒ k (≡ᵒ-sym strongTz2) ⟩
    ↓ᵒ k (↓ᵒ (suc k) (♯ T ((λ a → ♯ (Sᵃ a) (↓ᵈ j x δ)) , ↓ᵈ j x δ)))         ⩦⟨ lemma17ᵒ k ⟩
    ↓ᵒ k (♯ T ((λ a → ♯ (Sᵃ a) (↓ᵈ j x δ)) , ↓ᵈ j x δ))                      ∎
... | Later = λ δ j k k≤j →
    let strongTz = ((strong T) zeroˢ) ((λ a → ♯ (Sᵃ a) δ) , δ) (suc j) k (≤-trans k≤j (n≤1+n _)) in
    let strongTz2 = ((strong T) zeroˢ) (((λ a → ♯ (Sᵃ a) (↓ᵈ j x δ))) , δ) (suc j) k (≤-trans k≤j (n≤1+n _)) in
    let EQ : ((λ a → ↓ᵒ (suc j) (♯ (Sᵃ a) δ)) , δ) ≡ᵈ ((λ a → ↓ᵒ (suc j)  (♯ (Sᵃ a) (↓ᵈ j x δ))) , δ)
        EQ = (λ a → strong-later (strong (Sᵃ a) x) time-x δ j j ≤-refl) , ≡ᵈ-refl in
    let strongTsx = strong-later{x = sucˢ x}{Δ = cons Now Δ} ((strong T) (sucˢ x)) time-x
                 ((λ a → ♯ (Sᵃ a) (↓ᵈ j x δ)) , δ) j k k≤j in
    ↓ᵒ (suc k) (♯ T ((λ a → ♯ (Sᵃ a) δ) , δ))                       ⩦⟨ strongTz ⟩
    ↓ᵒ (suc k) (♯ T (↓ᵖ (suc j) (λ a → ♯ (Sᵃ a) δ) , δ))            ⩦⟨ cong-↓ᵒ (suc k) (congr T EQ) ⟩
    ↓ᵒ (suc k) (♯ T (↓ᵖ (suc j) (λ a → ♯ (Sᵃ a) (↓ᵈ j x δ)) , δ))   ⩦⟨ ≡ᵒ-sym strongTz2 ⟩
    ↓ᵒ (suc k) (♯ T ((λ a → ♯ (Sᵃ a) (↓ᵈ j x δ)) , δ))              ⩦⟨ strongTsx ⟩
    ↓ᵒ (suc k) (♯ T ((λ a → ♯ (Sᵃ a) (↓ᵈ j x δ)) , ↓ᵈ j x δ))       ∎
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
μᵖ f a k = #(iter (1 + k) f (λ a → ⊤ᵒ) a) k
\end{code}

Recall that the body $Sᵃ$ of a $μˢ Sᵃ$ has type
\[
    A → \mathsf{Set}ˢ (A ∷ Γ) (\mathsf{cons}\, \Later\, Δ))
    \text{ and not } \mathsf{Pred}ᵒ A → \mathsf{Pred}ᵒ A.
\]
So we define the following function to convert from the former to the later.

\begin{code}
⟅_⟆ : (A → Setˢ (A ∷ Γ) (cons Later Δ)) → RecEnv Γ → (Predᵒ A → Predᵒ A)
⟅ Sᵃ ⟆  δ μS = λ a → ♯ (Sᵃ a) (μS , δ)
\end{code}

\subsubsection{μᵖ is downward closed}

Our first goal is to prove that μᵖ is downward closed in the following sense.

\begin{code}
down-μᵖ : ∀{Sᵃ : A → Setˢ (A ∷ Γ) (cons Later Δ)} {a : A}{δ : RecEnv Γ}
  → downClosed (μᵖ (⟅ Sᵃ ⟆ δ) a)
\end{code}

\noindent The proof relies on \textsf{lemma15b}, but applies it to a
functional obtained by \textsf{env}-\textsf{fun}⇒\textsf{fun}.  So we
need to prove that such a functional is wellfounded and congruent.
The fact that $\eff{Sᵃ} δ$ is wellfounded is a direct consequence of
$Sᵃ\app a$ being strong.

\begin{code}
wf-env-fun : ∀ (δ : RecEnv Γ) (Sᵃ : A → Setˢ (A ∷ Γ) (cons Later Δ)) → wellfoundedᵖ (⟅ Sᵃ ⟆ δ)
wf-env-fun δ Sᵃ = λ a P k → strong (Sᵃ a) zeroˢ (P , δ) k k ≤-refl
\end{code}

\noindent Similarly, $\eff{Sᵃ}\,δ$ is congruent because $Sᵃ\app a$ is congruent.

\begin{code}
cong-env-fun : ∀ (δ : RecEnv Γ) (Sᵃ : A → Setˢ (A ∷ Γ) (cons Later Δ))
   → congruentᵖ (⟅ Sᵃ ⟆ δ)
cong-env-fun δ Sᵃ = λ P=Q a → congr (Sᵃ a) (P=Q , ≡ᵈ-refl{_}{δ})
\end{code}

\noindent So we have the following adaptation of \textsf{lemma15b}.

\begin{code}
lemma15b-env-fun : ∀(k j : ℕ) (Sᵃ : A → Setˢ (A ∷ Γ) (cons Later Δ)) (a : A) → j ≤ k
  → ↓ᵒ j (iter j (⟅ Sᵃ ⟆ δ) P a) ≡ᵒ ↓ᵒ j (iter k (⟅ Sᵃ ⟆ δ) P a)
lemma15b-env-fun{δ = δ} k j Sᵃ a j≤k =
  lemma15b k j (⟅ Sᵃ ⟆ δ) a j≤k (wf-env-fun δ Sᵃ) (cong-env-fun δ Sᵃ)
\end{code}

The one other fact we need to prove that $μᵖ$ is downward closed is
that \textsf{iter} is downward closed when applied to a functional.

\begin{code}
dc-iter : ∀(i : ℕ){A} (F : Predᵒ A → Predᵒ A) → ∀ a → downClosed (#(iter i F ⊤ᵖ a))
dc-iter zero F = λ a n _ k _ → tt
dc-iter (suc i) F = λ a → down (F (iter i F ⊤ᵖ) a)
\end{code}

\noindent We now prove that the $μᵖ$ function is downward closed when
applied to the result of $\eff{Sᵃ}$.

\begin{code}
down-μᵖ {Sᵃ = Sᵃ}{a}{δ} k iterskSᵃk zero j≤k = tz (⟅ Sᵃ ⟆ δ (id ⊤ᵖ) a)
down-μᵖ {Sᵃ = Sᵃ}{a}{δ} (suc k′) μSᵃa (suc j′) (s≤s j′≤k′) =
  let dc-iter-ssk : downClosed (# ((iter (2 + k′) (⟅ Sᵃ ⟆ δ) ⊤ᵖ) a))
      dc-iter-ssk = dc-iter (2 + k′) (⟅ Sᵃ ⟆ δ) a in
  let ↓-iter-ssk : #(↓ᵒ (2 + j′) ((iter (2 + k′) (⟅ Sᵃ ⟆ δ) ⊤ᵖ) a))(suc j′)
      ↓-iter-ssk = ≤-refl , (dc-iter-ssk (suc k′) μSᵃa (suc j′) (s≤s j′≤k′)) in
  let eq : ↓ᵒ (2 + j′) ((iter (2 + j′) (⟅ Sᵃ ⟆ δ) ⊤ᵖ) a)
        ≡ᵒ ↓ᵒ (2 + j′) ((iter (2 + k′) (⟅ Sᵃ ⟆ δ) ⊤ᵖ) a)
      eq = lemma15b-env-fun {δ = δ} (2 + k′) (2 + j′) Sᵃ a (s≤s (s≤s j′≤k′)) in
  let ↓-iter-ssj : #(↓ᵒ (2 + j′) ((iter (2 + j′) (⟅ Sᵃ ⟆ δ) ⊤ᵖ) a)) (suc j′)
      ↓-iter-ssj = ⇔-to (≡ᵒ-elim (≡ᵒ-sym eq)) ↓-iter-ssk in
  proj₂ ↓-iter-ssj
\end{code}

With these proofs complete, we can use μᵖ to define another auxilliary
function, \textsf{mu}ᵒ, that builds a \textsf{Set}ᵒ record given a
predicate into \textsf{Set}ˢ, an environment, and an element of $A$.

\begin{code}
muᵒ : (A → Setˢ (A ∷ Γ) (cons Later Δ)) → RecEnv Γ → A → Setᵒ
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
  lemma18a : ∀ (k : ℕ) (Sᵃ : A → Setˢ (A ∷ Γ) (cons Later Δ)) (a : A) (δ : RecEnv Γ)
     → ↓ᵒ k (muᵒ Sᵃ δ a) ≡ᵒ ↓ᵒ k (iter k (⟅ Sᵃ ⟆ δ) ⊤ᵖ a)
  lemma18a zero Sᵃ a δ zero = (λ x → tt) , (λ {x → tt})
  lemma18a zero Sᵃ a δ (suc j) = (λ {()}) , λ {()}
  lemma18a (suc k) Sᵃ a δ zero = (λ {x → tt}) , λ {x → tt}
  lemma18a (suc k′) Sᵃ a δ (suc j′) =
    ↓ k (λ j₁ → # ((⟅ Sᵃ ⟆ δ) (iter j₁ (⟅ Sᵃ ⟆ δ) ⊤ᵖ) a) j₁) j                          ⩦⟨ ⩦-refl refl ⟩    
    j < k  ×  # (iter (suc j) (⟅ Sᵃ ⟆ δ) ⊤ᵖ a) j
         ⩦⟨ (λ {(s≤s x , y) → s≤s x , ≤-refl , y}) , (λ {(s≤s x , (y , z)) → (s≤s x) , z}) ⟩
    j < k  ×  # (↓ᵒ (suc j) (iter (suc j) (⟅ Sᵃ ⟆ δ) ⊤ᵖ a)) j                          ⩦⟨ EQ  ⟩    
    j < k  ×  # (↓ᵒ (suc j) (iter k (⟅ Sᵃ ⟆ δ) ⊤ᵖ a)) j
         ⩦⟨ (λ {(s≤s x , (s≤s y , z)) → (s≤s x) , z}) , (λ {(x , y) → x , (≤-refl , y)})  ⟩
    j < k  ×  # (iter k (⟅ Sᵃ ⟆ δ) ⊤ᵖ a) j                                            ⩦⟨ ⩦-refl refl  ⟩    
    ↓ k (# (iter k (⟅ Sᵃ ⟆ δ) ⊤ᵖ a)) j                                                ∎
    where
    k : ℕ
    k = suc k′
    j : ℕ
    j = suc j′
    EQ : (j < k  ×  # (↓ᵒ (suc j) (iter (suc j) (⟅ Sᵃ ⟆ δ) ⊤ᵖ a)) j)
         ⇔ (j < k  ×  # (↓ᵒ (suc j) (iter k (⟅ Sᵃ ⟆ δ) ⊤ᵖ a)) j)
    EQ = (λ {(s≤s x , y) →
           let xx = proj₁ ((lemma15b-env-fun (suc k′) (suc j) Sᵃ a (s≤s x)) j) y in
           (s≤s x) , (≤-refl , proj₂ xx)})
       , (λ {(s≤s x , (s≤s y , z)) →
           let xx = proj₂ ((lemma15b-env-fun(suc k′)(suc j) Sᵃ a (s≤s x)) j) (≤-refl , z) in
           s≤s x , (≤-refl , (proj₂ xx))})
\end{code}
\caption{$\mathsf{mu}ᵒ\, Sᵃ\, δ\, a$ is equivalent to the $k$ iteration of
 $\eff{Sᵃ}\, δ$ under $k$-approximation.}
\label{fig:lemma18a}
\end{figure}


\begin{figure}[tbp]
\small 
\begin{code}
lemma18b : ∀ (k : ℕ) (Sᵃ : A → Setˢ (A ∷ Γ) (cons Later Δ)) (a : A) (δ : RecEnv Γ)
     → ↓ᵒ (1 + k) (♯ (Sᵃ a) (muᵒ Sᵃ δ , δ)) ≡ᵒ ↓ᵒ (1 + k) (iter (1 + k) (⟅ Sᵃ ⟆ δ) ⊤ᵖ a)
lemma18b {A}{Γ}{Δ} k Sᵃ a δ =
   ↓ᵒ (suc k) (♯ (Sᵃ a) (muᵒ Sᵃ δ , δ))           ⩦⟨ strong (Sᵃ a) zeroˢ (muᵒ Sᵃ δ , δ) k k ≤-refl ⟩
   ↓ᵒ (suc k) (♯ (Sᵃ a) (↓ᵖ k (muᵒ Sᵃ δ) , δ))
        ⩦⟨ cong-↓ (λ a → congr (Sᵃ a) ((λ a → lemma18a k Sᵃ a δ) , ≡ᵈ-refl)) a ⟩
   ↓ᵒ (suc k) (♯ (Sᵃ a) (↓ᵖ k (iter k (⟅ Sᵃ ⟆ δ) ⊤ᵖ) , δ))
        ⩦⟨ ≡ᵖ-sym{A} (strong (Sᵃ a) zeroˢ ((iter k (⟅ Sᵃ ⟆ δ) ⊤ᵖ) , δ) k k ≤-refl) {a} ⟩
   ↓ᵒ (suc k) (♯ (Sᵃ a) (iter k (⟅ Sᵃ ⟆ δ) ⊤ᵖ , δ))        ⩦⟨ ≡ᵒ-refl refl ⟩
   ↓ᵒ (suc k) (iter (suc k) (⟅ Sᵃ ⟆ δ) ⊤ᵖ a)            ∎
\end{code}
\caption{One unrolling of $muᵒ\, Sᵃ\, δ$ is equivalent to $k \plus 1$ iterations of
$\eff{Sᵃ}\, δ$, under $k\plus 1$-approximation.}
\label{fig:lemma18b}
\end{figure}


\begin{figure}[tbp]
\small
\begin{code}
lemma19a : ∀ (Sᵃ : A → Setˢ (A ∷ Γ) (cons Later Δ)) (a : A) (k : ℕ) (δ : RecEnv Γ)
   → ↓ᵒ k (muᵒ Sᵃ δ a) ≡ᵒ ↓ᵒ k (♯ (Sᵃ a) (muᵒ Sᵃ δ , δ))
lemma19a {A}{Γ}{Δ} Sᵃ a k δ =
    let f = (⟅ Sᵃ ⟆ δ) in
    ↓ᵒ k (muᵒ Sᵃ δ a)                        ⩦⟨ lemma18a k Sᵃ a δ  ⟩
    ↓ᵒ k (iter k f ⊤ᵖ a)                     ⩦⟨ lemma15b-env-fun (suc k) k Sᵃ a (n≤1+n k) ⟩
    ↓ᵒ k (iter (suc k) f ⊤ᵖ a)               ⩦⟨ ≡ᵖ-sym (lemma17ᵒ{(iter (suc k) f ⊤ᵖ) a} k) {a} ⟩
    ↓ᵒ k (↓ᵒ (suc k) (iter (suc k) f ⊤ᵖ a))  ⩦⟨ cong-↓ (λ a → ≡ᵒ-sym (lemma18b k Sᵃ a δ))  a  ⟩
    ↓ᵒ k (↓ᵒ (suc k) (♯ (Sᵃ a) (muᵒ Sᵃ δ , δ)))    ⩦⟨ lemma17ᵒ{(♯ (Sᵃ a) (muᵒ Sᵃ δ , δ))} k ⟩
    ↓ᵒ k (♯ (Sᵃ a) (muᵒ Sᵃ δ , δ))                 ∎
\end{code}
\caption{$muᵒ\, Sᵃ\, δ$ is equivalent to one unrolling of itself under $k$-approximation.}
\label{fig:lemma19a}
\end{figure}

The proof that \textsf{mu}ᵒ is a strong environment functional
proceeds by cases on whether the variable in question is assigned to
\textsf{Now} in Δ, in which case we need to show that \textsf{mu}ᵒ is
strongly nonexpansive with respect to that variable, or the variable
is assigned to \textsf{Later} in Δ, in which case we need to show that
\textsf{mu}ᵒ is strongly wellfounded.

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
mu-nonexpansive : ∀{Γ}{Δ : Times Γ}{A}{B} (Sᵃ : A → Setˢ (A ∷ Γ) (cons Later Δ)) (a : A) (x : Γ ∋ B)
   → timeof x Δ ≡ Now → (δ : RecEnv Γ) (k j : ℕ) → (k ≤ j)
   → ↓ᵒ k (muᵒ Sᵃ δ a) ≡ᵒ ↓ᵒ k (muᵒ Sᵃ (↓ᵈ j x δ) a)
mu-nonexpansive {Γ} {Δ} {A} Sᵃ a x time-x δ zero j k≤j = ↓ᵒ-zero
mu-nonexpansive {Γ} {Δ} {A}{B} Sᵃ a x time-x δ (suc k′) j k≤j =
  ↓ᵒ k (muᵒ Sᵃ δ a)                                          ⩦⟨ lemma19a Sᵃ a k δ ⟩
  ↓ᵒ k (♯ (Sᵃ a) (muᵒ Sᵃ δ , δ))                             ⩦⟨ nonexp-Sᵃ-sx ⟩
  ↓ᵒ k (♯ (Sᵃ a) (muᵒ Sᵃ δ , ↓ᵈ j x δ))                      ⩦⟨ wf-Sᵃ-z1 ⟩
  ↓ᵒ k (♯ (Sᵃ a) (↓ᵖ k′ (muᵒ Sᵃ δ) , ↓ᵈ j x δ))              ⩦⟨ cong-↓ (λ a → congr (Sᵃ a) (IH , ≡ᵈ-refl)) a ⟩
  ↓ᵒ k (♯ (Sᵃ a) (↓ᵖ k′ (muᵒ Sᵃ (↓ᵈ j x δ)) , ↓ᵈ j x δ))     ⩦⟨ ≡ᵒ-sym wf-Sᵃ-z2 ⟩
  ↓ᵒ k (♯ (Sᵃ a) (muᵒ Sᵃ (↓ᵈ j x δ) , ↓ᵈ j x δ))             ⩦⟨ ≡ᵒ-sym (lemma19a Sᵃ a k (↓ᵈ j x δ)) ⟩
  ↓ᵒ k (muᵒ Sᵃ (↓ᵈ j x δ) a)                                                        ∎
  where
  IH : ∀ a → ↓ᵒ k′ (muᵒ Sᵃ δ a) ≡ᵒ ↓ᵒ k′ (muᵒ Sᵃ (↓ᵈ j x δ) a)
  IH a = mu-nonexpansive Sᵃ a x time-x δ k′ j (≤-trans (n≤1+n _) k≤j)
  k : ℕ
  k = 1 + k′
  nonexp-Sᵃ-sx = strong-now{x = sucˢ x}{Δ = cons Later Δ}
                    (strong (Sᵃ a) (sucˢ x)) time-x (muᵒ Sᵃ δ , δ) j k k≤j
  wf-Sᵃ-z1 = strong (Sᵃ a) zeroˢ (muᵒ Sᵃ δ , ↓ᵈ j x δ) k′ k′ ≤-refl
  wf-Sᵃ-z2 = strong (Sᵃ a) zeroˢ (muᵒ Sᵃ (↓ᵈ j x δ) , ↓ᵈ j x δ) k′ k′ ≤-refl
\end{code}
\caption{\textsf{mu}ᵒ is strongly nonexpansive.}
\label{fig:mu-nonexpansive}
\end{figure}

Figure~\ref{fig:mu-wellfounded} gives the proof for the second case,
that \textsf{mu}ᵒ is strongly wellfounded. The proof is similar to the
previous one.

\begin{figure}[tbp]
\small
\begin{code}
mu-wellfounded : (Sᵃ : A → Setˢ (A ∷ Γ) (cons Later Δ)) (a : A) (x : Γ ∋ B)
   → timeof x Δ ≡ Later → (δ : RecEnv Γ) (k j : ℕ) → (k ≤ j)
   → ↓ᵒ (1 + k) (muᵒ Sᵃ δ a) ≡ᵒ ↓ᵒ (1 + k) (muᵒ Sᵃ (↓ᵈ j x δ) a)
mu-wellfounded {A} {Γ} {Δ} {B} Sᵃ a x time-x δ zero j k≤j = ↓ᵒ-one
mu-wellfounded {A} {Γ} {Δ} {B} Sᵃ a x time-x δ (suc k′) j k≤j =
  ↓ᵒ (1 + k) (muᵒ Sᵃ δ a)                                       ⩦⟨ lemma19a Sᵃ a (1 + k) δ ⟩
  ↓ᵒ (1 + k) (♯ (Sᵃ a) (muᵒ Sᵃ δ , δ))                          ⩦⟨ wf-Sᵃ-sx ⟩
  ↓ᵒ (1 + k) (♯ (Sᵃ a) (muᵒ Sᵃ δ , ↓ᵈ j x δ))                   ⩦⟨ wf-Sᵃ-z1 ⟩
  ↓ᵒ (1 + k) (♯ (Sᵃ a) (↓ᵖ k (muᵒ Sᵃ δ) , ↓ᵈ j x δ))            ⩦⟨ cong-↓ (λ a → congr (Sᵃ a) (IH , ≡ᵈ-refl)) a ⟩
  ↓ᵒ (1 + k) (♯ (Sᵃ a) (↓ᵖ k (muᵒ Sᵃ (↓ᵈ j x δ)) , ↓ᵈ j x δ))   ⩦⟨ ≡ᵒ-sym wf-Sᵃ-z2 ⟩
  ↓ᵒ (1 + k) (♯ (Sᵃ a) (muᵒ Sᵃ (↓ᵈ j x δ) , (↓ᵈ j x δ)))        ⩦⟨ ≡ᵒ-sym (lemma19a Sᵃ a (1 + k) _) ⟩
  ↓ᵒ (1 + k) (muᵒ Sᵃ (↓ᵈ j x δ) a)                                              ∎
  where
  IH : ∀ a → ↓ᵒ (1 + k′) (muᵒ Sᵃ δ a) ≡ᵒ ↓ᵒ (1 + k′) (muᵒ Sᵃ (↓ᵈ j x δ) a)
  IH a = mu-wellfounded Sᵃ a x time-x δ k′ j (≤-trans (n≤1+n _) k≤j)
  k : ℕ
  k = 1 + k′
  wf-Sᵃ-sx = strong-later{A = B}{sucˢ x}{Δ = cons Later Δ}
              (strong (Sᵃ a) (sucˢ x)) time-x (muᵒ Sᵃ δ , δ) j k k≤j 
  wf-Sᵃ-z1 = strong (Sᵃ a) zeroˢ (muᵒ Sᵃ δ , ↓ᵈ j x δ) k k ≤-refl 
  wf-Sᵃ-z2 = strong (Sᵃ a) zeroˢ (muᵒ Sᵃ (↓ᵈ j x δ) , ↓ᵈ j x δ) k k ≤-refl 
\end{code}
\caption{\textsf{mu}ᵒ is strongly wellfounded.}
\label{fig:mu-wellfounded}
\end{figure}

Finally, we put the two cases together to show that \textsf{mu}ᵒ is a strong
environment functional (Figure~\ref{fig:mu-strong-env-fun}).

\begin{figure}[tbp]
\small
\begin{code}
strong-fun-mu : ∀{Γ}{Δ : Times Γ}{A} (Sᵃ : A → Setˢ (A ∷ Γ) (cons Later Δ)) (a : A)
   → strong-fun Δ (λ δ → muᵒ Sᵃ δ a)
strong-fun-mu {Γ} {Δ} {A} Sᵃ a x
    with timeof x Δ in time-x
... | Now = λ δ j k k≤j → mu-nonexpansive Sᵃ a x time-x δ k j k≤j
... | Later = λ δ j k k≤j → mu-wellfounded Sᵃ a x time-x δ k j k≤j
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
  → iter i f I a ≡ᵒ iter i g I a
cong-iter zero f g f=g I = ≡ᵒ-refl refl
cong-iter{A}{a} (suc i) f g f=g I =
  let IH = λ b → cong-iter{A}{b} i f g f=g I in
  f=g (iter i f I) (iter i g I) a IH
\end{code}

\noindent The result \textsf{mu}ᵒ is congruent follows immediately from the lemma.

\begin{code}
congruent-mu : ∀{Γ}{Δ : Times Γ}{A} (Sᵃ : A → Setˢ (A ∷ Γ) (cons Later Δ)) (a : A)
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
equiv-downᵒ : (∀ k → ↓ᵒ k ϕ ≡ᵒ ↓ᵒ k ψ) → ϕ ≡ᵒ ψ
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
fixpointˢ : ∀ (F : A → Setˢ (A ∷ Γ) (cons Later Δ)) (a : A)
   → μˢ F a ≡ˢ letˢ (μˢ F) (F a)
fixpointˢ F a = equiv-downˢ λ k → ≡ˢ-intro (lemma19a F a k)
\end{code}

A recursive predicate will often appear at the top of a logical
formula, in which case it does not need to be an open formula. To
streamline this situation, we define the following μᵒ connective,
which specializes μˢ to the situation where $Γ = []$.

\begin{code}
μᵒ : (A → Setˢ (A ∷ []) (cons Later ∅)) → (A → Setᵒ)
μᵒ P = muᵒ P ttᵖ
\end{code}

\noindent Also for convenience, we provide the following
specialization of the fixpoint theorem for μᵒ.

\begin{code}
fixpointᵒ : ∀{A} (P : A → Setˢ (A ∷ []) (cons Later ∅)) (a : A)
   → μᵒ P a ≡ᵒ ♯ (P a) (μᵒ P , ttᵖ)
fixpointᵒ P a = ≡ˢ-elim (fixpointˢ P a) ttᵖ
\end{code}

\noindent That concludes our treatment of the recursive predicate in
SIL. We now move onto to the simpler connectives, including the
logical connectives from first-order logical.

\subsection{Constant}

A step-indexed logic such as LSLR is typically specialized to include
atomic formulas to express properties of programs in a particular
language. Here we instead allow arbitrary Agda propositions to be
included in a step-indexed proposition by way of the following
constant operator. Given a proposition $p$, the formula $p\,ᵒ$ is true
at zero and everywhere else it is equivalent to $p$.

\begin{code}
_ᵒ : Set → Setᵒ
p ᵒ = record { # = λ { zero → ⊤ ; (suc k) → p }
             ; down = λ { k pk zero j≤k → tt
                        ; (suc k) pk (suc j) j≤k → pk}
             ; tz = tt }
\end{code}

\noindent The constant operator is a strong environment functiuonal.

\begin{code}
const-strong : ∀ (p : Set) (x : Γ ∋ A) → strong-var x (timeof x Δ) (λ δ → p ᵒ)
const-strong {Γ}{A}{Δ} p x
    with timeof x Δ
... | Now = λ δ j k k≤j → ≡ᵒ-refl refl
... | Later = λ δ j k k≤j → ≡ᵒ-refl refl
\end{code}

\noindent So we define the constant SIL formula $pˢ$ as the following record.

\begin{code}
p ˢ = record { ♯ = λ δ → p ᵒ ; strong = λ x → const-strong p x ; congr = λ d=d′ → ≡ᵒ-refl refl }
\end{code}

\subsection{False}

The false formula of Agda is lifted into SIL by using the constant
operators.

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
  nonexpansive-∀ : ∀{k} → ↓ᵒ k (∀ᵒ[ a ] P a) ≡ᵒ ↓ᵒ k (∀ᵒ[ a ] ↓ᵒ k (P a))
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
      ↓ᵒ k (∀ᵒ[ a ] ♯ (P a) δ)                                      ⩦⟨ nonexpansive-∀ ⟩
      ↓ᵒ k (∀ᵒ[ a ] ↓ᵒ k (♯ (P a) δ))
          ⩦⟨ cong-↓ᵒ k (cong-∀(λ a → strong-now(strong(P a) x) time-x δ j k k≤j)) ⟩
      ↓ᵒ k (∀ᵒ[ a ] ↓ᵒ k (♯ (P a) (↓ᵈ j x δ)))                  ⩦⟨ ≡ᵒ-sym nonexpansive-∀ ⟩
      ↓ᵒ k (∀ᵒ[ a ] ♯ (P a) (↓ᵈ j x δ))                            ∎
... | Later = λ δ j k k≤j → 
      ↓ᵒ (suc k) (∀ᵒ[ a ] ♯ (P a) δ)                                ⩦⟨ nonexpansive-∀ ⟩
      ↓ᵒ (suc k) (∀ᵒ[ a ] ↓ᵒ (suc k) (♯ (P a) δ))
                      ⩦⟨ cong-↓ᵒ (suc k) (cong-∀ (λ a → strong-later (strong (P a) x) time-x δ j k k≤j)) ⟩
      ↓ᵒ (suc k) (∀ᵒ[ a ] ↓ᵒ (suc k) (♯ (P a) (↓ᵈ j x δ)))   ⩦⟨ ≡ᵒ-sym nonexpansive-∀ ⟩
      ↓ᵒ (suc k) (∀ᵒ[ a ] ♯ (P a) (↓ᵈ j x δ))                 ∎
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
    → ↓ᵒ k (∃ᵒ[ a ] P a) ≡ᵒ ↓ᵒ k (∃ᵒ[ a ] ↓ᵒ k (P a))
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
      ↓ᵒ k (∃ᵒ[ a ] ♯ (P a) δ)                                      ⩦⟨ nonexpansive-∃ ⟩
      ↓ᵒ k (∃ᵒ[ a ] ↓ᵒ k (♯ (P a) δ))
          ⩦⟨ cong-↓ᵒ k (cong-∃(λ a → strong-now(strong(P a) x) time-x δ j k k≤j)) ⟩
      ↓ᵒ k (∃ᵒ[ a ] ↓ᵒ k (♯ (P a) (↓ᵈ j x δ)))               ⩦⟨ ≡ᵒ-sym nonexpansive-∃ ⟩
      ↓ᵒ k (∃ᵒ[ a ] ♯ (P a) (↓ᵈ j x δ))   ∎
... | Later = λ δ j k k≤j →
      ↓ᵒ (suc k) (∃ᵒ[ a ] ♯ (P a) δ)                                ⩦⟨ nonexpansive-∃ ⟩
      ↓ᵒ (suc k) (∃ᵒ[ a ] ↓ᵒ (suc k) (♯ (P a) δ))
                      ⩦⟨ cong-↓ᵒ (suc k) (cong-∃
                          (λ a → strong-later (strong (P a) x) time-x δ j k k≤j)) ⟩
      ↓ᵒ (suc k) (∃ᵒ[ a ] ↓ᵒ (suc k) (♯ (P a) (↓ᵈ j x δ)))   ⩦⟨ ≡ᵒ-sym nonexpansive-∃ ⟩
      ↓ᵒ (suc k) (∃ᵒ[ a ] ♯ (P a) (↓ᵈ j x δ))            ∎
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

Next we define conjunction in SIL. Given two step-indexed propositions
$ϕ$ and $ψ$, their conjunction is the function that takes the
conjunction of applying them to the step index. The proofs of
downward-closedness and true-at-zero are straightforward, relying on
the proofs of these properties for $ϕ$ and $ψ$.

\begin{code}
infixr 7 _×ᵒ_
_×ᵒ_ : Setᵒ → Setᵒ → Setᵒ
ϕ ×ᵒ ψ = record { # = λ k → # ϕ k × # ψ k
                ; down = λ k (ϕk , ψk) j j≤k → (down ϕ k ϕk j j≤k) , (down ψ k ψk j j≤k)
                ; tz = (tz ϕ) , (tz ψ) }

\end{code}

\begin{code}
timeof-combine : ∀{Γ}{Δ₁ Δ₂ : Times Γ}{A}{x : Γ ∋ A}
   → timeof x (Δ₁ ∪ Δ₂) ≡ choose (timeof x Δ₁) (timeof x Δ₂)
timeof-combine {B ∷ Γ} {cons s Δ₁} {cons t Δ₂} {.B} {zeroˢ} = refl
timeof-combine {B ∷ Γ} {cons s Δ₁} {cons t Δ₂} {A} {sucˢ x} =
  timeof-combine {Γ} {Δ₁} {Δ₂} {A} {x}

abstract
  down-× : ∀{S T : Setᵒ}{k}
     → ↓ᵒ k (S ×ᵒ T) ≡ᵒ ↓ᵒ k ((↓ᵒ k S) ×ᵒ (↓ᵒ k T))
  down-× zero = ⇔-intro (λ x → tt) (λ x → tt)
  down-× (suc i) =
      ⇔-intro
      (λ { (si<k , Ssi , Δi) → si<k , ((si<k , Ssi) , (si<k , Δi))})
      (λ { (si<k , (_ , Ssi) , _ , Δi) → si<k , Ssi , Δi})

  cong-×ᵒ : ∀{S S′ T T′ : Setᵒ}
     → S ≡ᵒ S′
     → T ≡ᵒ T′
     → S ×ᵒ T ≡ᵒ S′ ×ᵒ T′
  cong-×ᵒ {S}{S′}{T}{T′} SS′ TT′ k = ⇔-intro to fro
    where
    to : # (S ×ᵒ T) k → # (S′ ×ᵒ T′) k
    to (Sk , Tk) = (⇔-to (SS′ k) Sk) , (⇔-to (TT′ k) Tk)
    fro  : #(S′ ×ᵒ T′) k → #(S ×ᵒ T) k
    fro (S′k , T′k) = (⇔-fro (SS′ k) S′k) , (⇔-fro (TT′ k) T′k)

strong-pair : ∀{Γ}{Δ₁ Δ₂ : Times Γ}
   (S : Setˢ Γ Δ₁) (T : Setˢ Γ Δ₂)
   → strong-fun (Δ₁ ∪ Δ₂) (λ δ → ♯ S δ ×ᵒ ♯ T δ)
strong-pair {Γ}{Δ₁}{Δ₂} S T {A} x
    rewrite timeof-combine {Γ}{Δ₁}{Δ₂}{A}{x}
    with timeof x Δ₁ in time-x1 | timeof x Δ₂ in time-x2
... | Now | Now = λ δ j k k≤j →
    let strongS = strong-now (strong S x) time-x1 δ j k k≤j in
    let strongT = strong-now (strong T x) time-x2 δ j k k≤j in
    ↓ᵒ k (♯ S δ ×ᵒ ♯ T δ)                                         ⩦⟨ down-× ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S δ) ×ᵒ ↓ᵒ k (♯ T δ))
                                     ⩦⟨ cong-↓ᵒ k (cong-×ᵒ strongS (≡ᵒ-refl refl)) ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S (↓ᵈ j x δ)) ×ᵒ ↓ᵒ k (♯ T δ))
                                     ⩦⟨ cong-↓ᵒ k (cong-×ᵒ (≡ᵒ-refl refl) strongT) ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S (↓ᵈ j x δ)) ×ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ)))   ⩦⟨ ≡ᵒ-sym down-× ⟩
    ↓ᵒ k (♯ S (↓ᵈ j x δ) ×ᵒ ♯ T (↓ᵈ j x δ))  ∎
... | Now | Later = λ δ j k k≤j →
    let strongS = strong-now (strong S x) time-x1 δ j k k≤j in
    let strongT = strong-later (strong T x) time-x2 δ j k k≤j in
    ↓ᵒ k (♯ S δ ×ᵒ ♯ T δ)                             ⩦⟨ ≡ᵒ-sym (lemma17ᵒ k) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (♯ S δ ×ᵒ ♯ T δ))                ⩦⟨ cong-↓ᵒ k down-× ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S δ) ×ᵒ ↓ᵒ (suc k) (♯ T δ)))
                   ⩦⟨ cong-↓ᵒ k (cong-↓ᵒ (suc k) (cong-×ᵒ (≡ᵒ-refl refl) strongT)) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S δ) ×ᵒ ↓ᵒ (suc k) (♯ T (↓ᵈ j x δ))))
                                                ⩦⟨ ≡ᵒ-sym (cong-↓ᵒ k down-×) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (♯ S δ ×ᵒ ♯ T (↓ᵈ j x δ)))
               ⩦⟨ lemma17ᵒ k ⟩ 
    ↓ᵒ k (♯ S δ ×ᵒ ♯ T (↓ᵈ j x δ))
               ⩦⟨ down-× ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S δ) ×ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ)))
               ⩦⟨ cong-↓ᵒ k (cong-×ᵒ strongS (≡ᵒ-refl refl)) ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S (↓ᵈ j x δ)) ×ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ)))
               ⩦⟨ ≡ᵒ-sym down-× ⟩ 
    ↓ᵒ k (♯ S (↓ᵈ j x δ) ×ᵒ ♯ T (↓ᵈ j x δ))    ∎
... | Later | Now = λ δ j k k≤j →
    let strongS = strong-later (strong S x) time-x1 δ j k k≤j in
    let strongT = strong-now (strong T x) time-x2 δ j k k≤j in
    ↓ᵒ k (♯ S δ ×ᵒ ♯ T δ)                             ⩦⟨ ≡ᵒ-sym (lemma17ᵒ k) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (♯ S δ ×ᵒ ♯ T δ))                ⩦⟨ cong-↓ᵒ k down-× ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S δ) ×ᵒ ↓ᵒ (suc k) (♯ T δ)))
                   ⩦⟨ cong-↓ᵒ k (cong-↓ᵒ (suc k) (cong-×ᵒ strongS (≡ᵒ-refl refl))) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S (↓ᵈ j x δ)) ×ᵒ ↓ᵒ (suc k) (♯ T δ)))
                                                ⩦⟨ ≡ᵒ-sym (cong-↓ᵒ k down-×) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (♯ S (↓ᵈ j x δ) ×ᵒ ♯ T δ))
               ⩦⟨ lemma17ᵒ k ⟩ 
    ↓ᵒ k (♯ S (↓ᵈ j x δ) ×ᵒ ♯ T δ)
               ⩦⟨ down-× ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S (↓ᵈ j x δ)) ×ᵒ ↓ᵒ k (♯ T δ))
               ⩦⟨ cong-↓ᵒ k (cong-×ᵒ (≡ᵒ-refl refl) strongT) ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S (↓ᵈ j x δ)) ×ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ)))
               ⩦⟨ ≡ᵒ-sym down-× ⟩ 
    ↓ᵒ k (♯ S (↓ᵈ j x δ) ×ᵒ ♯ T (↓ᵈ j x δ))    ∎
... | Later | Later = λ δ j k k≤j →
    let strongS = strong-later (strong S x) time-x1 δ j k k≤j in
    let strongT = strong-later (strong T x) time-x2 δ j k k≤j in
    ↓ᵒ (suc k) (♯ S δ ×ᵒ ♯ T δ)                ⩦⟨ down-× ⟩ 
    ↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S δ) ×ᵒ ↓ᵒ (suc k) (♯ T δ))
                   ⩦⟨ cong-↓ᵒ (suc k) (cong-×ᵒ strongS strongT) ⟩ 
    ↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S (↓ᵈ j x δ))
                                  ×ᵒ ↓ᵒ (suc k) (♯ T (↓ᵈ j x δ)))
                                                ⩦⟨ ≡ᵒ-sym down-× ⟩ 
    ↓ᵒ (suc k) (♯ S (↓ᵈ j x δ) ×ᵒ ♯ T (↓ᵈ j x δ))   ∎

S ×ˢ T = record { ♯ = λ δ → ♯ S δ ×ᵒ ♯ T δ
                ; strong = strong-pair S T
                ; congr = λ d=d′ → cong-×ᵒ (congr S d=d′) (congr T d=d′)
                }
\end{code}

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


\begin{code}
abstract
  down-⊎ : ∀{S T : Setᵒ}{k}
     → ↓ᵒ k (S ⊎ᵒ T) ≡ᵒ ↓ᵒ k ((↓ᵒ k S) ⊎ᵒ (↓ᵒ k T))
  down-⊎ zero = ⇔-intro (λ x → tt) (λ x → tt)
  down-⊎ (suc i) =
      (λ { (x , inj₁ x₁) → x , inj₁ (x , x₁)
         ; (x , inj₂ y) → x , inj₂ (x , y)})
      ,
      λ { (x , inj₁ x₁) → x , inj₁ (proj₂ x₁)
        ; (x , inj₂ y) → x , inj₂ (proj₂ y)}

  cong-⊎ᵒ : ∀{S S′ T T′ : Setᵒ}
     → S ≡ᵒ S′
     → T ≡ᵒ T′
     → S ⊎ᵒ T ≡ᵒ S′ ⊎ᵒ T′
  cong-⊎ᵒ {S}{S′}{T}{T′} SS′ TT′ k = ⇔-intro to fro
    where
    to : # (S ⊎ᵒ T) k → # (S′ ⊎ᵒ T′) k
    to (inj₁ x) = inj₁ (proj₁ (SS′ k) x)
    to (inj₂ y) = inj₂ (proj₁ (TT′ k) y)
    fro  : #(S′ ⊎ᵒ T′) k → #(S ⊎ᵒ T) k
    fro (inj₁ x) = inj₁ (proj₂ (SS′ k) x)
    fro (inj₂ y) = inj₂ (proj₂ (TT′ k) y)

strong-sum : ∀{Γ}{Δ₁ Δ₂ : Times Γ}
   (S : Setˢ Γ Δ₁) (T : Setˢ Γ Δ₂)
   → strong-fun (Δ₁ ∪ Δ₂) (λ δ → ♯ S δ ⊎ᵒ ♯ T δ)
strong-sum {Γ}{Δ₁}{Δ₂} S T {A} x
    rewrite timeof-combine {Γ}{Δ₁}{Δ₂}{A}{x}
    with timeof x Δ₁ in time-x1 | timeof x Δ₂ in time-x2
... | Now | Now = λ δ j k k≤j →
    let strongS = strong-now (strong S x) time-x1 δ j k k≤j in
    let strongT = strong-now (strong T x) time-x2 δ j k k≤j in
    ↓ᵒ k (♯ S δ ⊎ᵒ ♯ T δ)                                         ⩦⟨ down-⊎ ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S δ) ⊎ᵒ ↓ᵒ k (♯ T δ))
                                     ⩦⟨ cong-↓ᵒ k (cong-⊎ᵒ strongS (≡ᵒ-refl refl)) ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S (↓ᵈ j x δ)) ⊎ᵒ ↓ᵒ k (♯ T δ))
                                     ⩦⟨ cong-↓ᵒ k (cong-⊎ᵒ (≡ᵒ-refl refl) strongT) ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S (↓ᵈ j x δ)) ⊎ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ)))   ⩦⟨ ≡ᵒ-sym down-⊎ ⟩
    ↓ᵒ k (♯ S (↓ᵈ j x δ) ⊎ᵒ ♯ T (↓ᵈ j x δ))  ∎
... | Now | Later = λ δ j k k≤j →
    let strongS = strong-now (strong S x) time-x1 δ j k k≤j in
    let strongT = strong-later (strong T x) time-x2 δ j k k≤j in
    ↓ᵒ k (♯ S δ ⊎ᵒ ♯ T δ)                             ⩦⟨ ≡ᵒ-sym (lemma17ᵒ k) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (♯ S δ ⊎ᵒ ♯ T δ))                ⩦⟨ cong-↓ᵒ k down-⊎ ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S δ) ⊎ᵒ ↓ᵒ (suc k) (♯ T δ)))
                   ⩦⟨ cong-↓ᵒ k (cong-↓ᵒ (suc k) (cong-⊎ᵒ (≡ᵒ-refl refl) strongT)) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S δ) ⊎ᵒ ↓ᵒ (suc k) (♯ T (↓ᵈ j x δ))))
                                                ⩦⟨ ≡ᵒ-sym (cong-↓ᵒ k down-⊎) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (♯ S δ ⊎ᵒ ♯ T (↓ᵈ j x δ)))
               ⩦⟨ lemma17ᵒ k ⟩ 
    ↓ᵒ k (♯ S δ ⊎ᵒ ♯ T (↓ᵈ j x δ))
               ⩦⟨ down-⊎ ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S δ) ⊎ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ)))
               ⩦⟨ cong-↓ᵒ k (cong-⊎ᵒ strongS (≡ᵒ-refl refl)) ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S (↓ᵈ j x δ)) ⊎ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ)))
               ⩦⟨ ≡ᵒ-sym down-⊎ ⟩ 
    ↓ᵒ k (♯ S (↓ᵈ j x δ) ⊎ᵒ ♯ T (↓ᵈ j x δ))    ∎
... | Later | Now = λ δ j k k≤j →
    let strongS = strong-later (strong S x) time-x1 δ j k k≤j in
    let strongT = strong-now (strong T x) time-x2 δ j k k≤j in
    ↓ᵒ k (♯ S δ ⊎ᵒ ♯ T δ)                             ⩦⟨ ≡ᵒ-sym (lemma17ᵒ k) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (♯ S δ ⊎ᵒ ♯ T δ))                ⩦⟨ cong-↓ᵒ k down-⊎ ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S δ) ⊎ᵒ ↓ᵒ (suc k) (♯ T δ)))
                   ⩦⟨ cong-↓ᵒ k (cong-↓ᵒ (suc k) (cong-⊎ᵒ strongS (≡ᵒ-refl refl))) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S (↓ᵈ j x δ)) ⊎ᵒ ↓ᵒ (suc k) (♯ T δ)))
                                                ⩦⟨ ≡ᵒ-sym (cong-↓ᵒ k down-⊎) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (♯ S (↓ᵈ j x δ) ⊎ᵒ ♯ T δ))
               ⩦⟨ lemma17ᵒ k ⟩ 
    ↓ᵒ k (♯ S (↓ᵈ j x δ) ⊎ᵒ ♯ T δ)
               ⩦⟨ down-⊎ ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S (↓ᵈ j x δ)) ⊎ᵒ ↓ᵒ k (♯ T δ))
               ⩦⟨ cong-↓ᵒ k (cong-⊎ᵒ (≡ᵒ-refl refl) strongT) ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S (↓ᵈ j x δ)) ⊎ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ)))
               ⩦⟨ ≡ᵒ-sym down-⊎ ⟩ 
    ↓ᵒ k (♯ S (↓ᵈ j x δ) ⊎ᵒ ♯ T (↓ᵈ j x δ))    ∎
... | Later | Later = λ δ j k k≤j →
    let strongS = strong-later (strong S x) time-x1 δ j k k≤j in
    let strongT = strong-later (strong T x) time-x2 δ j k k≤j in
    ↓ᵒ (suc k) (♯ S δ ⊎ᵒ ♯ T δ)                ⩦⟨ down-⊎ ⟩ 
    ↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S δ) ⊎ᵒ ↓ᵒ (suc k) (♯ T δ))
                   ⩦⟨ cong-↓ᵒ (suc k) (cong-⊎ᵒ strongS strongT) ⟩ 
    ↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S (↓ᵈ j x δ))
                                  ⊎ᵒ ↓ᵒ (suc k) (♯ T (↓ᵈ j x δ)))
                                                ⩦⟨ ≡ᵒ-sym down-⊎ ⟩ 
    ↓ᵒ (suc k) (♯ S (↓ᵈ j x δ) ⊎ᵒ ♯ T (↓ᵈ j x δ))   ∎

S ⊎ˢ T = record { ♯ = λ δ → ♯ S δ ⊎ᵒ ♯ T δ
                ; strong = strong-sum S T
                ; congr = λ d=d′ → cong-⊎ᵒ (congr S d=d′) (congr T d=d′)
                }
\end{code}

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

The standard workaround is to force implication to be downward closed
by definition. We define $ϕ$ implies $ψ$ at $k$ to mean that for all
$j \leq k$, $ϕ$ at $j$ implies $ψ$ at $j$.

\begin{code}
infixr 6 _→ᵒ_
_→ᵒ_ : Setᵒ → Setᵒ → Setᵒ
ϕ →ᵒ ψ = record { # = λ k → ∀ j → j ≤ k → # ϕ j → # ψ j
                ; down = λ k ∀j≤k→ϕj→ψj j j≤k i i≤j ϕi →
                     ∀j≤k→ϕj→ψj i (≤-trans i≤j j≤k) ϕi
                ; tz = λ { .zero z≤n _ → tz ψ} }
\end{code}

\begin{code}
abstract
  down-→ : ∀{S T : Setᵒ}{k}
     → ↓ᵒ k (S →ᵒ T) ≡ᵒ ↓ᵒ k ((↓ᵒ k S) →ᵒ (↓ᵒ k T))
  down-→ zero = (λ x → tt) , (λ x → tt)
  down-→{S}{T} (suc i) =
      (λ {(x , y) → x , (λ { zero x₁ x₂ → tt
                           ; (suc j) x₁ (x₂ , x₃) → x₂ , y (suc j) x₁ x₃})})
      , λ {(x , y) → x , (λ { zero x₁ x₂ → tz T
                            ; (suc j) x₁ x₂ →
                              let z = y (suc j) x₁ ((≤-trans (s≤s x₁) x) , x₂)
                              in proj₂ z})}

  cong-→ : ∀{S S′ T T′ : Setᵒ}
     → S ≡ᵒ S′
     → T ≡ᵒ T′
     → S →ᵒ T ≡ᵒ S′ →ᵒ T′
  cong-→ {S}{S′}{T}{T′} SS′ TT′ k =
    (λ x j x₁ x₂ → proj₁ (TT′ j) (x j x₁ (proj₂ (SS′ j) x₂)))
    , (λ z j z₁ z₂ → proj₂ (TT′ j) (z j z₁ (proj₁ (SS′ j) z₂)))

strong-imp : ∀{Γ}{Δ₁ Δ₂ : Times Γ}
   (S : Setˢ Γ Δ₁) (T : Setˢ Γ Δ₂)
   → strong-fun (Δ₁ ∪ Δ₂) (λ δ → ♯ S δ →ᵒ ♯ T δ)
strong-imp {Γ}{Δ₁}{Δ₂} S T {A} x
    rewrite timeof-combine {Γ}{Δ₁}{Δ₂}{A}{x}
    with timeof x Δ₁ in time-x1 | timeof x Δ₂ in time-x2
... | Now | Now = λ δ j k k≤j →
    let strongS = strong-now (strong S x) time-x1 δ j k k≤j in
    let strongT = strong-now (strong T x) time-x2 δ j k k≤j in
    ↓ᵒ k (♯ S δ →ᵒ ♯ T δ)                         ⩦⟨ down-→{♯ S δ}{♯ T δ} ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S δ) →ᵒ ↓ᵒ k (♯ T δ))
                                     ⩦⟨ cong-↓ᵒ k (cong-→ strongS (≡ᵒ-refl refl)) ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S (↓ᵈ j x δ)) →ᵒ ↓ᵒ k (♯ T δ))
                       ⩦⟨ cong-↓ᵒ k (cong-→{↓ᵒ k (♯ S (↓ᵈ j x δ))}
                                           {↓ᵒ k (♯ S (↓ᵈ j x δ))}
                                           {↓ᵒ k (♯ T δ)}
                                           {↓ᵒ k (♯ T (↓ᵈ j x δ))}
                                    (≡ᵒ-refl refl) strongT) ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S (↓ᵈ j x δ)) →ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ)))
                          ⩦⟨ ≡ᵒ-sym (down-→{♯ S (↓ᵈ j x δ)}{♯ T (↓ᵈ j x δ)}) ⟩
    ↓ᵒ k (♯ S (↓ᵈ j x δ) →ᵒ ♯ T (↓ᵈ j x δ))  ∎
... | Now | Later = λ δ j k k≤j →
    let strongS = strong-now (strong S x) time-x1 δ j k k≤j in
    let strongT = strong-later (strong T x) time-x2 δ j k k≤j in
    ↓ᵒ k (♯ S δ →ᵒ ♯ T δ)                             ⩦⟨ ≡ᵒ-sym (lemma17ᵒ k) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (♯ S δ →ᵒ ♯ T δ))   ⩦⟨ cong-↓ᵒ k (down-→{♯ S δ}{♯ T δ}) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S δ) →ᵒ ↓ᵒ (suc k) (♯ T δ)))
         ⩦⟨ cong-↓ᵒ k (cong-↓ᵒ (suc k)
             (cong-→{↓ᵒ (suc k) (♯ S δ)}{↓ᵒ (suc k) (♯ S δ)}
                     {↓ᵒ (suc k) (♯ T δ)}{ ↓ᵒ (suc k) (♯ T (↓ᵈ j x δ))}
                     (≡ᵒ-refl refl) strongT)) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S δ) →ᵒ ↓ᵒ (suc k) (♯ T (↓ᵈ j x δ))))
                       ⩦⟨ ≡ᵒ-sym (cong-↓ᵒ k (down-→{♯ S δ}{♯ T (↓ᵈ j x δ)})) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (♯ S δ →ᵒ ♯ T (↓ᵈ j x δ)))
               ⩦⟨ lemma17ᵒ k ⟩ 
    ↓ᵒ k (♯ S δ →ᵒ ♯ T (↓ᵈ j x δ))
               ⩦⟨ down-→{♯ S δ}{♯ T (↓ᵈ j x δ)} ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S δ) →ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ)))
               ⩦⟨ cong-↓ᵒ k (cong-→ strongS (≡ᵒ-refl refl)) ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S (↓ᵈ j x δ)) →ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ)))
               ⩦⟨ ≡ᵒ-sym (down-→{♯ S (↓ᵈ j x δ)}{♯ T (↓ᵈ j x δ)}) ⟩ 
    ↓ᵒ k (♯ S (↓ᵈ j x δ) →ᵒ ♯ T (↓ᵈ j x δ))    ∎
... | Later | Now = λ δ j k k≤j →
    let strongS = strong-later (strong S x) time-x1 δ j k k≤j in
    let strongT = strong-now (strong T x) time-x2 δ j k k≤j in
    ↓ᵒ k (♯ S δ →ᵒ ♯ T δ)                             ⩦⟨ ≡ᵒ-sym (lemma17ᵒ k) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (♯ S δ →ᵒ ♯ T δ))   ⩦⟨ cong-↓ᵒ k (down-→{♯ S δ}{♯ T δ}) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S δ) →ᵒ ↓ᵒ (suc k) (♯ T δ)))
                   ⩦⟨ cong-↓ᵒ k (cong-↓ᵒ (suc k) (cong-→ strongS (≡ᵒ-refl refl))) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S (↓ᵈ j x δ)) →ᵒ ↓ᵒ (suc k) (♯ T δ)))
                       ⩦⟨ ≡ᵒ-sym (cong-↓ᵒ k (down-→{♯ S (↓ᵈ j x δ)}{♯ T δ})) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (♯ S (↓ᵈ j x δ) →ᵒ ♯ T δ))
               ⩦⟨ lemma17ᵒ k ⟩ 
    ↓ᵒ k (♯ S (↓ᵈ j x δ) →ᵒ ♯ T δ)
               ⩦⟨ down-→{♯ S (↓ᵈ j x δ)}{♯ T δ} ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S (↓ᵈ j x δ)) →ᵒ ↓ᵒ k (♯ T δ))
               ⩦⟨ cong-↓ᵒ k (cong-→{↓ᵒ k (♯ S (↓ᵈ j x δ))}
                     {↓ᵒ k (♯ S (↓ᵈ j x δ))}
                     {↓ᵒ k (♯ T δ)}{↓ᵒ k (♯ T (↓ᵈ j x δ))} (≡ᵒ-refl refl) strongT) ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S (↓ᵈ j x δ)) →ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ)))
               ⩦⟨ ≡ᵒ-sym (down-→{♯ S (↓ᵈ j x δ)}{♯ T (↓ᵈ j x δ)}) ⟩ 
    ↓ᵒ k (♯ S (↓ᵈ j x δ) →ᵒ ♯ T (↓ᵈ j x δ))    ∎
... | Later | Later = λ δ j k k≤j →
    let strongS = strong-later (strong S x) time-x1 δ j k k≤j in
    let strongT = strong-later (strong T x) time-x2 δ j k k≤j in
    ↓ᵒ (suc k) (♯ S δ →ᵒ ♯ T δ)                ⩦⟨ down-→{♯ S δ}{♯ T δ} ⟩ 
    ↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S δ) →ᵒ ↓ᵒ (suc k) (♯ T δ))
                   ⩦⟨ cong-↓ᵒ (suc k) (cong-→ strongS strongT) ⟩ 
    ↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S (↓ᵈ j x δ))
                                  →ᵒ ↓ᵒ (suc k) (♯ T (↓ᵈ j x δ)))
                         ⩦⟨ ≡ᵒ-sym (down-→{♯ S (↓ᵈ j x δ)}{♯ T (↓ᵈ j x δ)}) ⟩ 
    ↓ᵒ (suc k) (♯ S (↓ᵈ j x δ) →ᵒ ♯ T (↓ᵈ j x δ))   ∎

S →ˢ T = record { ♯ = λ δ → ♯ S δ →ᵒ ♯ T δ
                ; strong = strong-imp S T
                ; congr = λ d=d′ → cong-→ (congr S d=d′) (congr T d=d′)
                }
\end{code}





\section{Proof Rules for Step-Indexed Logic}

\begin{code}
{---------------------- Proof Theory for Step Indexed Logic -------------------}

Πᵒ : List Setᵒ → Setᵒ
Πᵒ [] = ⊤ᵒ
Πᵒ (P ∷ 𝒫) = P ×ᵒ Πᵒ 𝒫 

abstract 
  infix 1 _⊢ᵒ_
  _⊢ᵒ_ : List Setᵒ → Setᵒ → Set
  𝒫 ⊢ᵒ P = ∀ n → # (Πᵒ 𝒫) n → # P n

  ⊢ᵒ-intro : ∀{𝒫}{P}
     → (∀ n → # (Πᵒ 𝒫) n → # P n)
     → 𝒫 ⊢ᵒ P
  ⊢ᵒ-intro 𝒫→P = 𝒫→P

  ⊢ᵒ-elim : ∀{𝒫}{P}
     → 𝒫 ⊢ᵒ P
     → (∀ n → # (Πᵒ 𝒫) n → # P n)
  ⊢ᵒ-elim 𝒫⊢P = 𝒫⊢P

downClosed-Πᵒ :
    (𝒫 : List Setᵒ)
  → downClosed (# (Πᵒ 𝒫))
downClosed-Πᵒ [] = λ n _ k _ → tt
downClosed-Πᵒ (P ∷ 𝒫) n (Pn , ⊨𝒫n) k k≤n =
    (down P n Pn k k≤n) , (downClosed-Πᵒ 𝒫 n ⊨𝒫n k k≤n)

abstract
  monoᵒ : ∀ {𝒫}{P}
     → 𝒫 ⊢ᵒ P
       -----------
     → 𝒫 ⊢ᵒ  ▷ᵒ P
  monoᵒ {𝒫}{P} ⊢P zero ⊨𝒫n = tt
  monoᵒ {𝒫}{P} ⊢P (suc n) ⊨𝒫n =
    let ⊨𝒫n = downClosed-Πᵒ 𝒫 (suc n) ⊨𝒫n n (n≤1+n n) in
    ⊢P n ⊨𝒫n

  lobᵒ : ∀ {𝒫}{P}
     → (▷ᵒ P) ∷ 𝒫 ⊢ᵒ P
       ----------------
     → 𝒫 ⊢ᵒ P
  lobᵒ {𝒫}{P} step zero ⊨𝒫n = tz P
  lobᵒ {𝒫}{P} step (suc n) ⊨𝒫sn =
    let ⊨𝒫n = downClosed-Πᵒ 𝒫 (suc n) ⊨𝒫sn n (n≤1+n n) in
    let Pn = lobᵒ {𝒫}{P} step n ⊨𝒫n in
    step (suc n) (Pn , ⊨𝒫sn)

  ▷× : ∀{𝒫} {P Q : Setᵒ}
     → 𝒫 ⊢ᵒ (▷ᵒ (P ×ᵒ Q))
       ----------------------
     → 𝒫 ⊢ᵒ (▷ᵒ P) ×ᵒ (▷ᵒ Q)
  ▷× ▷P×Q zero = λ _ → tt , tt
  ▷× ▷P×Q (suc n) = ▷P×Q (suc n)

  ▷⊎ : ∀{𝒫}{P Q : Setᵒ}
     → 𝒫 ⊢ᵒ (▷ᵒ (P ⊎ᵒ Q))
       ----------------------
     → 𝒫 ⊢ᵒ (▷ᵒ P) ⊎ᵒ (▷ᵒ Q)
  ▷⊎ ▷P⊎Q zero = λ _ → inj₁ tt
  ▷⊎ ▷P⊎Q (suc n) = ▷P⊎Q (suc n) 

  ▷→ : ∀{𝒫}{P Q : Setᵒ}
     → 𝒫 ⊢ᵒ (▷ᵒ (P →ᵒ Q))
       ----------------------
     → 𝒫 ⊢ᵒ (▷ᵒ P) →ᵒ (▷ᵒ Q)
  ▷→ ▷P→Q zero ⊨𝒫n .zero z≤n tt = tt
  ▷→ ▷P→Q (suc n) ⊨𝒫n .zero z≤n ▷Pj = tt
  ▷→ ▷P→Q (suc n) ⊨𝒫n (suc j) (s≤s j≤n) Pj = ▷P→Q (suc n) ⊨𝒫n j j≤n Pj

  ▷∀ : ∀{𝒫}{A}{P : A → Setᵒ}
     → 𝒫 ⊢ᵒ ▷ᵒ (∀ᵒ[ a ] P a)
       ------------------------
     → 𝒫 ⊢ᵒ (∀ᵒ[ a ] ▷ᵒ (P a))
  ▷∀ 𝒫⊢▷∀P zero ⊨𝒫n a = tt
  ▷∀ 𝒫⊢▷∀P (suc n) ⊨𝒫sn a = 𝒫⊢▷∀P (suc n) ⊨𝒫sn a

abstract
  substᵒ : ∀{𝒫}{P Q : Setᵒ}
    → P ≡ᵒ Q
      -------------------
    → 𝒫 ⊢ᵒ P  →  𝒫 ⊢ᵒ Q
  substᵒ P=Q 𝒫⊢P n ⊨𝒫n = ⇔-to (P=Q n) (𝒫⊢P n ⊨𝒫n)

  ≡ᵖ⇒⊢ᵒ : ∀ 𝒫 {A} (P Q : Predᵒ A) {a : A}
    → 𝒫 ⊢ᵒ P a
    → (∀ a → P a ≡ᵒ Q a)
      ------------------
    → 𝒫 ⊢ᵒ Q a
  ≡ᵖ⇒⊢ᵒ 𝒫 {A} P Q {a} 𝒫⊢P P=Q n ⊨𝒫n =
      let Pan = 𝒫⊢P n ⊨𝒫n in
      let Qan = ⇔-to (P=Q a n) Pan in
      Qan

{-
⊢ᵒ-unfold : ∀ {A}{𝒫}{F : Fun A A Later}{a : A}
  → 𝒫 ⊢ᵒ (muᵒ F) a
    ------------------------------
  → 𝒫 ⊢ᵒ ((fun F) (muᵒ F)) a
⊢ᵒ-unfold {A}{𝒫}{F}{a} ⊢μa =
    ≡ᵖ⇒⊢ᵒ 𝒫 (muᵒ F) ((fun F) (muᵒ F)) ⊢μa (fixpoint F)

⊢ᵒ-fold : ∀ {A}{𝒫}{F : Fun A A Later}{a : A}
  → 𝒫 ⊢ᵒ ((fun F) (muᵒ F)) a
    ------------------------------
  → 𝒫 ⊢ᵒ (muᵒ F) a
⊢ᵒ-fold {A}{𝒫}{F}{a} ⊢μa =
    ≡ᵖ⇒⊢ᵒ 𝒫 ((fun F) (muᵒ F)) (muᵒ F) ⊢μa (≡ᵖ-sym (fixpoint F))
-}

abstract
  ttᵒ : ∀{𝒫 : List Setᵒ}
    → 𝒫 ⊢ᵒ ⊤ᵒ
  ttᵒ n _ = tt  

  ⊥-elimᵒ : ∀{𝒫 : List Setᵒ}
    → 𝒫 ⊢ᵒ ⊥ᵒ
    → (P : Setᵒ)
    → 𝒫 ⊢ᵒ P
  ⊥-elimᵒ ⊢⊥ P zero ⊨𝒫n = tz P
  ⊥-elimᵒ ⊢⊥ P (suc n) ⊨𝒫sn = ⊥-elim (⊢⊥ (suc n) ⊨𝒫sn)

  _,ᵒ_ : ∀{𝒫 : List Setᵒ }{P Q : Setᵒ}
    → 𝒫 ⊢ᵒ P
    → 𝒫 ⊢ᵒ Q
      ------------
    → 𝒫 ⊢ᵒ P ×ᵒ Q
  (𝒫⊢P ,ᵒ 𝒫⊢Q) n ⊨𝒫n = 𝒫⊢P n ⊨𝒫n , 𝒫⊢Q n ⊨𝒫n

  proj₁ᵒ : ∀{𝒫 : List Setᵒ }{P Q : Setᵒ}
    → 𝒫 ⊢ᵒ P ×ᵒ Q
      ------------
    → 𝒫 ⊢ᵒ P
  proj₁ᵒ 𝒫⊢P×Q n ⊨𝒫n = proj₁ (𝒫⊢P×Q n ⊨𝒫n)

  proj₂ᵒ : ∀{𝒫 : List Setᵒ }{P Q : Setᵒ}
    → 𝒫 ⊢ᵒ P ×ᵒ Q
      ------------
    → 𝒫 ⊢ᵒ Q
  proj₂ᵒ 𝒫⊢P×Q n ⊨𝒫n = proj₂ (𝒫⊢P×Q n ⊨𝒫n)

  ×-elim-L : ∀{P}{Q}{𝒫}{R}
     → P ∷ Q ∷ 𝒫 ⊢ᵒ R
     → (P ×ᵒ Q) ∷ 𝒫 ⊢ᵒ R
  ×-elim-L {P}{Q}{𝒫}{R} PQ𝒫⊢R n ((Pn , Qn) , 𝒫n) = PQ𝒫⊢R n (Pn , (Qn , 𝒫n))
  
  inj₁ᵒ : ∀{𝒫 : List Setᵒ }{P Q : Setᵒ}
    → 𝒫 ⊢ᵒ P
      ------------
    → 𝒫 ⊢ᵒ P ⊎ᵒ Q
  inj₁ᵒ 𝒫⊢P n ⊨𝒫n = inj₁ (𝒫⊢P n ⊨𝒫n)

  inj₂ᵒ : ∀{𝒫 : List Setᵒ }{P Q : Setᵒ}
    → 𝒫 ⊢ᵒ Q
      ------------
    → 𝒫 ⊢ᵒ P ⊎ᵒ Q
  inj₂ᵒ 𝒫⊢Q n ⊨𝒫n = inj₂ (𝒫⊢Q n ⊨𝒫n)

  caseᵒ : ∀{𝒫 : List Setᵒ }{P Q R : Setᵒ}
    → 𝒫 ⊢ᵒ P ⊎ᵒ Q
    → P ∷ 𝒫 ⊢ᵒ R
    → Q ∷ 𝒫 ⊢ᵒ R
      ------------
    → 𝒫 ⊢ᵒ R
  caseᵒ 𝒫⊢P⊎Q P∷𝒫⊢R Q∷𝒫⊢R n ⊨𝒫n
      with 𝒫⊢P⊎Q n ⊨𝒫n
  ... | inj₁ Pn = P∷𝒫⊢R n (Pn , ⊨𝒫n)
  ... | inj₂ Qn = Q∷𝒫⊢R n (Qn , ⊨𝒫n)

  case3ᵒ : ∀{𝒫 : List Setᵒ }{P Q R S : Setᵒ}
    → 𝒫 ⊢ᵒ P ⊎ᵒ (Q ⊎ᵒ R)
    → P ∷ 𝒫 ⊢ᵒ S
    → Q ∷ 𝒫 ⊢ᵒ S
    → R ∷ 𝒫 ⊢ᵒ S
      ------------
    → 𝒫 ⊢ᵒ S
  case3ᵒ 𝒫⊢P⊎Q⊎R P∷𝒫⊢S Q∷𝒫⊢S R∷𝒫⊢S n ⊨𝒫n
      with 𝒫⊢P⊎Q⊎R n ⊨𝒫n
  ... | inj₁ Pn = P∷𝒫⊢S n (Pn , ⊨𝒫n)
  ... | inj₂ (inj₁ Qn) = Q∷𝒫⊢S n (Qn , ⊨𝒫n)
  ... | inj₂ (inj₂ Rn) = R∷𝒫⊢S n (Rn , ⊨𝒫n)

  case4ᵒ : ∀{𝒫 : List Setᵒ }{P Q R S T : Setᵒ}
    → 𝒫 ⊢ᵒ P ⊎ᵒ (Q ⊎ᵒ (R ⊎ᵒ S))
    → P ∷ 𝒫 ⊢ᵒ T
    → Q ∷ 𝒫 ⊢ᵒ T
    → R ∷ 𝒫 ⊢ᵒ T
    → S ∷ 𝒫 ⊢ᵒ T
      ------------
    → 𝒫 ⊢ᵒ T
  case4ᵒ 𝒫⊢P⊎Q⊎R⊎S P∷𝒫⊢T Q∷𝒫⊢T R∷𝒫⊢T S∷𝒫⊢T n ⊨𝒫n
      with 𝒫⊢P⊎Q⊎R⊎S n ⊨𝒫n
  ... | inj₁ Pn = P∷𝒫⊢T n (Pn , ⊨𝒫n)
  ... | inj₂ (inj₁ Qn) = Q∷𝒫⊢T n (Qn , ⊨𝒫n)
  ... | inj₂ (inj₂ (inj₁ Rn)) = R∷𝒫⊢T n (Rn , ⊨𝒫n)
  ... | inj₂ (inj₂ (inj₂ Sn)) = S∷𝒫⊢T n (Sn , ⊨𝒫n)

  case-Lᵒ : ∀{𝒫 : List Setᵒ }{P Q R : Setᵒ}
     → P ∷ 𝒫 ⊢ᵒ R
     → Q ∷ 𝒫 ⊢ᵒ R
     → P ⊎ᵒ Q ∷ 𝒫 ⊢ᵒ R
  case-Lᵒ {𝒫} {P} {Q} {R} P⊢R Q⊢R n (inj₁ Pn , 𝒫n) = P⊢R n (Pn , 𝒫n)
  case-Lᵒ {𝒫} {P} {Q} {R} P⊢R Q⊢R n (inj₂ Qn , 𝒫n) = Q⊢R n (Qn , 𝒫n)

  {- todo: consider making P explicit -Jeremy -}
  →ᵒI : ∀{𝒫 : List Setᵒ }{P Q : Setᵒ}
    → P ∷ 𝒫 ⊢ᵒ Q
      ------------
    → 𝒫 ⊢ᵒ P →ᵒ Q
  →ᵒI {𝒫} P∷𝒫⊢Q n ⊨𝒫n j j≤n Pj =
      P∷𝒫⊢Q j (Pj , downClosed-Πᵒ 𝒫 n ⊨𝒫n j j≤n)

  appᵒ : ∀{𝒫 : List Setᵒ }{P Q : Setᵒ}
    → 𝒫 ⊢ᵒ P →ᵒ Q
    → 𝒫 ⊢ᵒ P
      ------------
    → 𝒫 ⊢ᵒ Q
  appᵒ {𝒫} 𝒫⊢P→Q 𝒫⊢P n ⊨𝒫n =
     let Pn = 𝒫⊢P n ⊨𝒫n in
     let Qn = 𝒫⊢P→Q n ⊨𝒫n n ≤-refl Pn in
     Qn

  ▷→▷ : ∀{𝒫}{P Q : Setᵒ}
     → 𝒫 ⊢ᵒ ▷ᵒ P
     → P ∷ 𝒫 ⊢ᵒ Q
       ------------
     → 𝒫 ⊢ᵒ ▷ᵒ Q
  ▷→▷ {𝒫}{P}{Q} ▷P P⊢Q n ⊨𝒫n =
    let ▷Q = appᵒ{𝒫}{▷ᵒ P}{▷ᵒ Q}
                (▷→{𝒫}{P}{Q}
                    (monoᵒ{𝒫}{P →ᵒ Q} (→ᵒI{𝒫}{P}{Q} P⊢Q))) ▷P in
    ▷Q n ⊨𝒫n

  ⊢ᵒ-∀-intro : ∀{𝒫 : List Setᵒ }{A}{P : A → Setᵒ}
    → (∀ a → 𝒫 ⊢ᵒ P a)
      ----------------------
    → 𝒫 ⊢ᵒ ∀ᵒ P
  ⊢ᵒ-∀-intro ∀Pa n ⊨𝒫n a = ∀Pa a n ⊨𝒫n

  ⊢ᵒ-∀-intro-new : ∀{𝒫 : List Setᵒ }{A}
    → (P : A → Setᵒ)
    → (∀ a → 𝒫 ⊢ᵒ P a)
      ----------------------
    → 𝒫 ⊢ᵒ ∀ᵒ P
  ⊢ᵒ-∀-intro-new P ∀Pa n ⊨𝒫n a = ∀Pa a n ⊨𝒫n

  instᵒ : ∀{𝒫 : List Setᵒ }{A}{P : A → Setᵒ}
    → 𝒫 ⊢ᵒ ∀ᵒ P
    → (a : A)
      ---------
    → 𝒫 ⊢ᵒ P a
  instᵒ ⊢∀P a n ⊨𝒫n = ⊢∀P n ⊨𝒫n a

  instᵒ-new : ∀{𝒫 : List Setᵒ }{A}
    → (P : A → Setᵒ)
    → 𝒫 ⊢ᵒ ∀ᵒ P
    → (a : A)
      ---------
    → 𝒫 ⊢ᵒ P a
  instᵒ-new P ⊢∀P a n ⊨𝒫n = ⊢∀P n ⊨𝒫n a

Λᵒ-syntax = ⊢ᵒ-∀-intro
infix 1 Λᵒ-syntax
syntax Λᵒ-syntax (λ a → ⊢Pa) = Λᵒ[ a ] ⊢Pa

abstract
  ⊢ᵒ-∃-intro : ∀{𝒫 : List Setᵒ }{A}{P : A → Setᵒ}{{_ : Inhabited A}}
    → (a : A)
    → 𝒫 ⊢ᵒ P a
      ----------
    → 𝒫 ⊢ᵒ ∃ᵒ P
  ⊢ᵒ-∃-intro a ⊢Pa n ⊨𝒫n = a , (⊢Pa n ⊨𝒫n)

  ⊢ᵒ-∃-intro-new : ∀{𝒫 : List Setᵒ }{A}{{_ : Inhabited A}}
    → (P : A → Setᵒ)
    → (a : A)
    → 𝒫 ⊢ᵒ P a
      ----------
    → 𝒫 ⊢ᵒ ∃ᵒ P
  ⊢ᵒ-∃-intro-new P a ⊢Pa n ⊨𝒫n = a , (⊢Pa n ⊨𝒫n)

  ⊢ᵒ-∃-elim : ∀{𝒫 : List Setᵒ }{A}{P : A → Setᵒ}{R : Setᵒ}{{_ : Inhabited A}}
    → 𝒫 ⊢ᵒ ∃ᵒ P
    → (∀ a → P a ∷ 𝒫 ⊢ᵒ R)
      ---------------------
    → 𝒫 ⊢ᵒ R
  ⊢ᵒ-∃-elim{R = R} ⊢∃P cont zero ⊨𝒫n = tz R
  ⊢ᵒ-∃-elim ⊢∃P cont (suc n) ⊨𝒫n
      with ⊢∃P (suc n) ⊨𝒫n
  ... | (a , Pasn) = cont a (suc n) (Pasn , ⊨𝒫n)

  {- making P explicit, inference not working -}
  ⊢ᵒ-∃-elim-new : ∀{𝒫 : List Setᵒ }{A}{R : Setᵒ}{{_ : Inhabited A}}
    → (P : A → Setᵒ)
    → 𝒫 ⊢ᵒ ∃ᵒ P
    → (∀ a → P a ∷ 𝒫 ⊢ᵒ R)
      ---------------------
    → 𝒫 ⊢ᵒ R
  ⊢ᵒ-∃-elim-new{R = R} P ⊢∃P cont zero ⊨𝒫n = tz R
  ⊢ᵒ-∃-elim-new P ⊢∃P cont (suc n) ⊨𝒫n
      with ⊢∃P (suc n) ⊨𝒫n
  ... | (a , Pasn) = cont a (suc n) (Pasn , ⊨𝒫n)

  ⊢ᵒ-∃-elim-L : ∀{𝒫 : List Setᵒ }{A}{R : Setᵒ}{{_ : Inhabited A}}
    → (P : A → Setᵒ)
    → (∀ a → P a ∷ 𝒫 ⊢ᵒ R)
      ---------------------
    → (∃ᵒ P) ∷ 𝒫 ⊢ᵒ R
  ⊢ᵒ-∃-elim-L {R = R} P Pa⊢R n ((a , Pan) , ⊨𝒫n) = Pa⊢R a n (Pan , ⊨𝒫n)

abstract
  Zᵒ : ∀{𝒫 : List Setᵒ}{S : Setᵒ}
     → S ∷ 𝒫 ⊢ᵒ S
  Zᵒ n (Sn , ⊨𝒫n) = Sn

  Sᵒ : ∀{𝒫 : List Setᵒ}{T : Setᵒ}{S : Setᵒ}
     → 𝒫 ⊢ᵒ T
     → S ∷ 𝒫 ⊢ᵒ T
  Sᵒ 𝒫⊢T n (Sn , ⊨𝒫n) = 𝒫⊢T n ⊨𝒫n

  ⊢ᵒ-swap : ∀{𝒫 : List Setᵒ}{T : Setᵒ}{S S′ : Setᵒ}
     → S ∷ S′ ∷ 𝒫 ⊢ᵒ T
     → S′ ∷ S ∷ 𝒫 ⊢ᵒ T
  ⊢ᵒ-swap {𝒫}{T}{S}{S′} SS′𝒫⊢T n (S′n , Sn , ⊨𝒫n) =
      SS′𝒫⊢T n (Sn , S′n , ⊨𝒫n)

  {- same as Sᵒ 
  ⊢ᵒ-weaken : ∀{𝒫 : List Setᵒ}{P R : Setᵒ}
    → 𝒫 ⊢ᵒ R
    → P ∷ 𝒫 ⊢ᵒ R
  ⊢ᵒ-weaken ⊢R n (Pn , 𝒫n) = ⊢R n 𝒫n
  -}

  →ᵒI′ : ∀{𝒫 : List Setᵒ }{P Q : Setᵒ}
    → (P ∷ 𝒫 ⊢ᵒ P → P ∷ 𝒫 ⊢ᵒ Q)
      -----------------------
    → 𝒫 ⊢ᵒ P →ᵒ Q
  →ᵒI′ {𝒫}{P}{Q} P→Q = →ᵒI{𝒫}{P}{Q} (P→Q (Zᵒ{𝒫}{P}))

λᵒ-syntax = →ᵒI′
infix 1 λᵒ-syntax
syntax λᵒ-syntax (λ ⊢P → ⊢Q) = λᵒ[ ⊢P ] ⊢Q

abstract
  constᵒI : ∀{𝒫}{S : Set}
     → S
     → 𝒫 ⊢ᵒ S ᵒ
  constᵒI s zero ⊨𝒫n = tt
  constᵒI s (suc n) ⊨𝒫n = s

  constᵒE : ∀ {𝒫}{S : Set}{R : Setᵒ}
     → 𝒫 ⊢ᵒ S ᵒ
     → (S → 𝒫 ⊢ᵒ R)
     → 𝒫 ⊢ᵒ R
  constᵒE {𝒫} {S} {R} ⊢S S→⊢R zero 𝒫n = tz R
  constᵒE {𝒫} {S} {R} ⊢S S→⊢R (suc n) 𝒫n = S→⊢R (⊢S (suc n) 𝒫n) (suc n) 𝒫n

  constᵒE-L : ∀ {𝒫}{S : Set}{R : Setᵒ}
     → (S → 𝒫 ⊢ᵒ R)
     → S ᵒ ∷ 𝒫 ⊢ᵒ R
  constᵒE-L {𝒫} {S} {R} S→𝒫R zero (s , 𝒫n) = tz R
  constᵒE-L {𝒫} {S} {R} S→𝒫R (suc n) (s , 𝒫n) = S→𝒫R s (suc n) 𝒫n

  caseᵒ-L : ∀{𝒫 : List Setᵒ }{P Q R : Setᵒ}
    → P ∷ 𝒫 ⊢ᵒ R
    → Q ∷ 𝒫 ⊢ᵒ R
      ------------------
    → (P ⊎ᵒ Q) ∷ 𝒫 ⊢ᵒ R
  caseᵒ-L{𝒫}{P}{Q}{R} P∷𝒫⊢R Q∷𝒫⊢R =
      let 𝒫′ = P ∷ Q ∷ (P ⊎ᵒ Q) ∷ 𝒫 in
      let ⊢P⊎Q : (P ⊎ᵒ Q) ∷ 𝒫 ⊢ᵒ P ⊎ᵒ Q
          ⊢P⊎Q = Zᵒ{𝒫}{P ⊎ᵒ Q} in
      let P⊢R = ⊢ᵒ-swap{𝒫}{R}{P ⊎ᵒ Q}{P}
            (Sᵒ{P ∷ 𝒫}{R}{P ⊎ᵒ Q} P∷𝒫⊢R) in
      let Q⊢R = ⊢ᵒ-swap{𝒫}{R}{P ⊎ᵒ Q}{Q}
            (Sᵒ{Q ∷ 𝒫}{R}{P ⊎ᵒ Q} Q∷𝒫⊢R) in
      caseᵒ{(P ⊎ᵒ Q) ∷ 𝒫}{P}{Q}{R} ⊢P⊎Q P⊢R Q⊢R

⊢ᵒ-sucP : ∀{𝒫}{P Q : Setᵒ}
   → 𝒫 ⊢ᵒ P
   → (∀{n} → # P (suc n) → 𝒫 ⊢ᵒ Q)
   → 𝒫 ⊢ᵒ Q
⊢ᵒ-sucP {𝒫}{P}{Q} ⊢P Psn⊢Q =
    ⊢ᵒ-intro λ { zero x → tz Q
               ; (suc n) 𝒫sn →
                 let ⊢Q = Psn⊢Q (⊢ᵒ-elim ⊢P (suc n) 𝒫sn) in
                 let Qsn = ⊢ᵒ-elim ⊢Q (suc n) 𝒫sn in
                 Qsn}
\end{code}
