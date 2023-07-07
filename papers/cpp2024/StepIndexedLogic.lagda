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
variable P Q : Predᵒ A
\end{code}

We define the constantly true predicate as follows.
\begin{code}
⊤ᵖ : ∀{A} → Predᵒ A
⊤ᵖ = (λ a → ⊤ᵒ)
\end{code}

The equivalence of predicates applied to the same argument forms and
equivalence relation.

\begin{code}
≡ᵖ-refl : ∀{A}{P Q : Predᵒ A} → P ≡ Q → ∀ {a} → P a ≡ᵒ Q a
≡ᵖ-refl refl {a} = ≡ᵒ-refl refl

≡ᵖ-sym : ∀{A}{P Q : Predᵒ A} → (∀ {a} → P a ≡ᵒ Q a) → ∀ {a} → Q a ≡ᵒ P a
≡ᵖ-sym P=Q {a} = ≡ᵒ-sym P=Q

≡ᵖ-trans : ∀{A}{P Q R : Predᵒ A} → (∀ {a} → P a ≡ᵒ Q a) → (∀ {a} → Q a ≡ᵒ R a) → ∀ {a} → P a ≡ᵒ R a
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
congruentᵖ : ∀{A}{B} (f : Predᵒ A → Predᵒ B) → Set₁
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

The $k$-approximation of any two step-indexed propositions is
equivalent when $k=0$.

\begin{code}
↓ᵒ-zero : ↓ᵒ zero ϕ ≡ᵒ ↓ᵒ zero ψ
↓ᵒ-zero = ≡ᵒ-intro λ {zero → (λ _ → tt) , λ _ → tt
                     ; (suc i) → (λ {()}) , (λ {()})}
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
double-↓ : ∀{j k a} (P : Predᵒ A) → j ≤ k → ↓ᵖ j (↓ᵖ k P) a ≡ᵒ ↓ᵖ j P a
double-↓ {A}{j}{k}{a} P j≤k = ≡ᵒ-intro aux
  where
  aux : ∀ i → # (↓ᵖ j (↓ᵖ k P) a) i ⇔ # (↓ᵖ j P a) i
  aux zero = (λ _ → tt) , (λ _ → tt)
  aux (suc i) = (λ { (i≤j , ↓kPasi) → i≤j , proj₂ ↓kPasi}) , λ {(i≤j , Pasi) → i≤j , ((≤-trans i≤j j≤k) , Pasi)}
\end{code}

This is a generalization of Lemma 17 of \citet{Appel:2001aa}, in which
$j = k - 1$.

\begin{code}
lemma17 : ∀{k}{a} → ↓ᵖ k (↓ᵖ (suc k) P) a ≡ᵒ ↓ᵖ k P a
lemma17 {A}{P}{k}{a} = double-↓ P (n≤1+n k)
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
\emph{environment functional}.

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

We define another record type, $\mathsf{Set}ˢ$ for open step-indexed
propositions, that is, propositions that may contain free variables.
\begin{code}
record Setˢ (Γ : Context) (Δ : Times Γ) : Set₁
\end{code}
Let $F,G,H$ range over $\mathsf{Set}ˢ$.
\begin{code}
variable F G H : Setˢ Γ Δ
\end{code}

We explain the type system for \textsf{Set}$^s$ in
Figure~\ref{fig:SIL-type-system}.  The membership formula $a ∈ x$ is
well-typed when variable $x$ is in $Γ$ and $Δ$ assigns $x$ to $\Now$ and all
the other variables in $Γ$ to $\Later$. We use the function $\varnow$
to express this constraint, which also relies on the
auxiliary $\laters$ function.
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

The later formula $▷ˢ F$ is well-typed at $\laters(Γ)$ when $F$ is
well-typed at $Δ$.

The implication formula $F →ˢ G$ is well-typed in $Γ$ at the combined
times $Δ₁ ∪ Δ₂$ when $F$ is well-typed in $Γ$ at $Δ₁$ and $G$ is
well-typed in $Γ$ at $Δ₂$. We combine lists of times using the
following auxiliary functions.

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

The universal and exists quantifiers use Agda functions, as one would
do in higher-order abstract syntax.  The exists quantifier requires
that the type $A$ be inhabited to obtain the true-at-zero property. We
do not wish this requirement to clutter every use of the exists
quantifier, so we use Agda's support for instance arguments (think
type classes). So we define the following record type and use it as an
implicit instance argument in the definition of the exists quantifier.

\begin{code}
record Inhabited (A : Set) : Set where
  field elt : A
open Inhabited {{...}} public
\end{code}

The recursive formula $μˢ F$ is well-typed in $Γ$ at $Δ$ if $F$ is
well typed in $Γ,A$ at $Δ,\Later$. That is, the variable $\zero$ bound
by the $μˢ$ has type $A$ and may only be used later.


\begin{figure}
\raggedright
\fbox{$F : \mathsf{Set}ˢ \, Γ \, Δ$}
\begin{gather*}
\inference{a : A & x : Γ ∋ A}
          {a ∈ x  : \mathsf{Set}ˢ \,Γ \,\varnow\,Γ\,x} \quad
\inference{F : \mathsf{Set}ˢ\,Γ\, Δ}
          {▷ˢ F : \mathsf{Set}ˢ \,Γ\,\laters(Γ)} \\[2ex]
\inference{F : \mathsf{Set}ˢ\, Γ \, Δ₁  & G : \mathsf{Set}ˢ\,Γ\, Δ₂}
          {F →ˢ G : \mathsf{Set}ˢ\,Γ\, (Δ₁ ∪ Δ₂)} \quad
\inference{F : \mathsf{Set}ˢ\,Γ\, Δ₁ & G : \mathsf{Set}ˢ\,Γ\, Δ₂}
          {F ×ˢ G : \mathsf{Set}ˢ\,Γ\, (Δ₁ ∪ Δ₂)} \quad
\inference{F : \mathsf{Set}ˢ\,Γ\, Δ₁ & G : \mathsf{Set}ˢ\,Γ\, Δ₂}
          {F ⊎ˢ G : \mathsf{Set}ˢ\,Γ\, (Δ₁ ∪ Δ₂)} \\[2ex]
\inference{∀ a ∈ A.\, f a : \mathsf{Set}ˢ\,Γ\, Δ}
          {∀ˢ f : \mathsf{Set}ˢ\,Γ\, Δ} \quad
\inference{∀ a ∈ A.\, f a : \mathsf{Set}ˢ\,Γ\, Δ}
          {∃ˢ f : \mathsf{Set}ˢ\,Γ\, Δ} \quad
\inference{}{p ˢ : \mathsf{Set}ˢ\,Γ\, \laters(Δ)}\\[2ex]
\inference{F : \mathsf{Set}ˢ\,(Γ,A)\, Δ,\mathsf{Later}}
          {μˢ F : \mathsf{Set}ˢ\,Γ\, Δ}
\end{gather*}
\caption{Type System for Open Step-Indexed Formulas}
\label{fig:SIL-type-system}
\end{figure}

The type system is implemented by the type signatures for the logical
operators, which we declare in Figure~{fig:SIL-decl}.

\begin{figure}
\begin{code}
_∈_ : A → (x : Γ ∋ A) → Setˢ Γ (var-now Γ x)

▷ˢ : Setˢ Γ Δ → Setˢ Γ (laters Γ)

infixr 6 _→ˢ_
_→ˢ_ : Setˢ Γ Δ₁ → Setˢ Γ Δ₂ → Setˢ Γ (Δ₁ ∪ Δ₂)

infixr 7 _×ˢ_
_×ˢ_ : Setˢ Γ Δ₁ → Setˢ Γ Δ₂ → Setˢ Γ (Δ₁ ∪ Δ₂)

infixr 7 _⊎ˢ_
_⊎ˢ_ : Setˢ Γ Δ₁ → Setˢ Γ Δ₂ → Setˢ Γ (Δ₁ ∪ Δ₂)

∀ˢ : (A → Setˢ Γ Δ) → Setˢ Γ Δ

∃ˢ : {{_ : Inhabited A}} → (A → Setˢ Γ Δ) → Setˢ Γ Δ

_ˢ : Set → Setˢ Γ (laters Γ)

μˢ : (A → Setˢ (A ∷ Γ) (cons Later Δ)) → (A → Setˢ Γ Δ)
\end{code}
\caption{Declarations of the Open Step-Indexed Formula}
\label{fig:SIL-decl}
\end{figure}

We have declared the type $\mathsf{Set}ˢ$ for open propositions but we
have not yet given its definition. Similar to $\mathsf{Set}ᵒ$ it will
be a record type. Its principal field is an environment functional
($\mathsf{RecEnv}\app Γ → \mathsf{Set}ᵒ$) that represents the meaning
of the formula. The record will also include two properties, that the
functional is congruent and that it is wellfounded in a sense that is
somewhat involved.

We apply $k$-approximation to one of the predicates in an environment
with the $↓ᵈ$ operator. The second parameter, a variable, specifies
which predicate to apply the $k$-approximation.

\begin{code}
↓ᵈ : ℕ → Γ ∋ A → RecEnv Γ → RecEnv Γ
↓ᵈ k zeroˢ (P , δ) = ↓ᵖ k P , δ
↓ᵈ k (sucˢ x) (P , δ) = P , ↓ᵈ k x δ
\end{code}

The semantic conditions that correspond to using the variable for a
recursive predicate now vs. later are the notion of nonexpansive
and wellfounded we reviewed in Section~\ref{sec:intro}.
A direct adaptation of nonexpansive to our setting yields the following,
which says that given any environment $δ$ and variable $x$,
the $k$-approximation of $P\app δ$ is equivalent to the
$k$-approximation of $P$ applied to the $k$ approximation of
the $δ$ with respect to variable $x$.
\[
  ↓ k (P δ) ≡ᵒ ↓ k (P (↓ᵈ k x δ)
\]
Simlarly, the direct adaption of wellfounded to our setting says
that the $k \plus 1$ approximation of $P\app δ$ is equivalent to the
$k \plus 1$ approximation of $P$ applied to the $k$ approximation of
the $δ$ with respect to variable $x$.
\[
  ↓ (suc \app k) (P δ) ≡ᵒ ↓ (suc\app k) (P (↓ᵈ k x δ)
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
strongly-nonexpansive x f = ∀ δ j k → k ≤ j → ↓ᵒ k (f δ) ≡ᵒ ↓ᵒ k (f (↓ᵈ j x δ))

strongly-wellfounded : (x : Γ ∋ A) → (RecEnv Γ → Setᵒ) → Set₁
strongly-wellfounded x f = ∀ δ j k → k ≤ j → ↓ᵒ (suc k) (f δ) ≡ᵒ ↓ᵒ (suc k) (f (↓ᵈ j x δ))
\end{code}

We say that a functional $f$ is ``good'' with respect to variable $x$
at time $t$ if it is either \textsf{nonexpansive} (when $t = \Now$) or
\textsf{wellfounded} (when $t = \Later$).

\begin{code}
good-var : (x : Γ ∋ A) → Time → (RecEnv Γ → Setᵒ) → Set₁
good-var x Now f = strongly-nonexpansive x f
good-var x Later f = strongly-wellfounded x f
\end{code}

\noindent Next we define the \textsf{timeof} function to lookup the
time for a variable $x$ in $Δ$.

\begin{code}
timeof : ∀{Γ}{A} → (x : Γ ∋ A) → Times Γ → Time
timeof {B ∷ Γ} zeroˢ (cons t Δ) = t
timeof {B ∷ Γ} (sucˢ x) (cons t Δ) = timeof x Δ
\end{code}

\noindent We say that a functional is ``good'' if it is good with respect to
every variable that is in scope.

\begin{code}
good-fun : ∀{Γ} → Times Γ → (RecEnv Γ → Setᵒ) → Set₁
good-fun {Γ} Δ f = ∀{A} (x : Γ ∋ A) → good-var x (timeof x Δ) f
\end{code}

\noindent Two environments are equivalent if they are point-wise equivalent.

\begin{code}
_≡ᵈ_ : ∀{Γ} → RecEnv Γ → RecEnv Γ → Set
_≡ᵈ_ {[]} δ δ′ = ⊤
_≡ᵈ_ {A ∷ Γ} (P , δ) (Q , δ′) = (∀ a → P a ≡ᵒ Q a) × δ ≡ᵈ δ′
\end{code}

\noindent A functional is congruent if applying it to equivalent
environments produces equivalent step-indexed propositions.

\begin{code}
congruent : ∀{Γ : Context} → (RecEnv Γ → Setᵒ) → Set₁
congruent f = ∀{δ δ′} → δ ≡ᵈ δ′ → (f δ) ≡ᵒ (f δ′)
\end{code}

We define $\mathsf{Set}ˢ$ as the following record type.  The meaning
is given by a functional and we require proofs that the functional is
good and congruent.

\begin{code}
record Setˢ Γ Δ where
  field
    ♯ : RecEnv Γ → Setᵒ 
    good : good-fun Δ ♯
    congr : congruent ♯
open Setˢ public
\end{code}

In the following subsections we define the logic operators that are
declared in Figure~\ref{fig:SIL-decl}. We start with the membership
formula to get warmed up, and then dive into the most difficult case,
of recursive predicates.

\subsection{Membership in Recursive Predicate}

The following \textsf{lookup} function retrieves from the environment
the predicate associated with a particular variable.

\begin{code}
lookup : Γ ∋ A → RecEnv Γ → Predᵒ A
lookup zeroˢ (P , δ) = P
lookup (sucˢ x) (P , δ) = lookup x δ
\end{code}

The lemma $\mathsf{double}\mbox{-}↓$ that we defined in Section~\ref{sec:fun-approx-iter}
generalizes to the \textsf{lookup} function as follows.

\begin{code}
↓-lookup : ∀{a}{k j}{δ : RecEnv Γ} (x : Γ ∋ A) (y : Γ ∋ B) → k ≤ j
   → ↓ᵒ k (lookup{Γ}{A} x δ a) ≡ᵒ ↓ᵒ k (lookup{Γ}{A} x (↓ᵈ j y δ) a)
↓-lookup {δ = P , δ} zeroˢ zeroˢ k≤j = ≡ᵒ-sym (double-↓ P k≤j)
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

The time of a variable $x$ in the list of times produced by $\varnow\,Γ\,x$
is \textsf{Now}.

\begin{code}
timeof-var-now : ∀{Γ}{A} → (x : Γ ∋ A) → timeof x (var-now Γ x) ≡ Now
timeof-var-now {B ∷ Γ} zeroˢ = refl
timeof-var-now {B ∷ Γ} (sucˢ x) = timeof-var-now x
\end{code}

The time of a variable $x$ in the list of times produced by $\laters(Γ)$
is \textsf{Later}.

\begin{code}
timeof-later : ∀{Γ}{A} (x : Γ ∋ A) → (timeof x (laters Γ)) ≡ Later
timeof-later {B ∷ Γ} zeroˢ = refl
timeof-later {B ∷ Γ} (sucˢ x) = timeof-later x
\end{code}

The \textsf{lookup} function for a variable $x$ is a ``good''
functional when the list of times Δ is the result of
$\varnow\,Γ\,x$. Because the time of $x$ in $\varnow\,Γ\,x$ is
\textsf{Now}, this amounts to proving that \textsf{lookup} is strongly
nonexpansive in $x$ and strongly wellfounded in the other variables.

\begin{code}
good-lookup : ∀{Γ}{A}{a} → (x : Γ ∋ A) → good-fun (var-now Γ x) (λ δ → lookup x δ a)
good-lookup {.(A ∷ _)} {A} {a} zeroˢ zeroˢ = SNE where
  SNE : strongly-nonexpansive zeroˢ (λ {(P , δ) → P a})
  SNE (P , δ) j k k≤j = ≡ᵒ-sym (double-↓ P k≤j)
good-lookup {.(A ∷ _)} {A} {a} zeroˢ (sucˢ y) rewrite timeof-later y = SWF where
  SWF : strongly-wellfounded (sucˢ y) (λ {(P , δ) → P a})
  SWF (P , δ) j k k≤j = ≡ᵒ-refl refl
good-lookup {.(_ ∷ _)} {A} {a} (sucˢ x) zeroˢ = SWF where
  SWF : strongly-wellfounded zeroˢ (λ (P , δ) → lookup x δ a)
  SWF (P , δ) j k k≤j = ≡ᵒ-refl refl
good-lookup {B ∷ Γ} {A} {a} (sucˢ x) (sucˢ y)
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
      let eq = (lookup-diff{Γ}{_}{_}{_}{δ}{j} x y (timeof-diff x y (timeof-var-now x) eq-y)) in
      subst (λ X → ↓ᵒ (suc k) (lookup x δ a) ≡ᵒ ↓ᵒ (suc k) (X a)) (sym eq) (≡ᵒ-refl refl)
\end{code}

The \textsf{lookup} function for a variable $x$ is congruent. That is,
given two equivalent environments, \textsf{lookup} produces equivalent
predicates.

\begin{code}
congruent-lookup : ∀ (x : Γ ∋ A) (a : A) → congruent (λ δ → lookup x δ a)
congruent-lookup x a d=d′ = aux x a d=d′
  where
  aux : ∀{Γ}{A}{δ δ′ : RecEnv Γ} (x : Γ ∋ A) (a : A) → δ ≡ᵈ δ′ → lookup x δ a ≡ᵒ lookup x δ′ a
  aux {B ∷ Γ} {.B}{P , δ}{P′ , δ′} zeroˢ a (P=P′ , d=d′) = P=P′ a
  aux {B ∷ Γ} {A}{P , δ}{P′ , δ′} (sucˢ x) a (P=P′ , d=d′) =
     aux x a d=d′
\end{code}

We conclude by constructing the \textsf{Set}ˢ record for the predicate
membership operator as follows.

\begin{code}
a ∈ x = record { ♯ = λ δ → (lookup x δ) a ; good = good-lookup x ; congr = congruent-lookup x a }
\end{code}

\subsection{Recursive Predicate}

As mentioned previously, we use iteration to define recursive
predicates. We begin this process by defining an auxilliary function
$μᵖ$ that takes a functional $f$ and produces a raw step-indexed
predicate (without the proofs.) It iterates the function $k \plus 1$
times, starting at the true formula.

\begin{code}
μᵖ : (Predᵒ A → Predᵒ A) → A → (ℕ → Set)
μᵖ f a k = #(iter (suc k) f (λ a → ⊤ᵒ) a) k
\end{code}

Now, recall that the body $f$ of a $μˢ f$ has type
\[
    A → \mathsf{Set}ˢ (A ∷ Γ) (\mathsf{cons}\, \Later\, Δ))
\]
and not $\mathsf{Pred}ᵒ A → \mathsf{Pred}ᵒ A$.  So we define the
following function to convert from the former to the later.

\begin{code}
toFun : RecEnv Γ → (A → Setˢ (A ∷ Γ) (cons Later Δ)) → (Predᵒ A → Predᵒ A)
toFun δ f μf = λ a → ♯ (f a) (μf , δ)
\end{code}


\begin{code}
nonexpansiveˢ : ∀{Γ}{A} (S : RecEnv (A ∷ Γ) → Setᵒ) (δ : RecEnv Γ) → Set₁
nonexpansiveˢ{Γ}{A} S δ = ∀ P k → ↓ᵒ k (S (P , δ)) ≡ᵒ ↓ᵒ k (S ((↓ᵖ k P) , δ))

wellfoundedˢ : ∀{Γ}{A} (S : RecEnv (A ∷ Γ) → Setᵒ) (δ : RecEnv Γ) → Set₁
wellfoundedˢ{Γ}{A} S δ = ∀ P k → ↓ᵒ (suc k) (S (P , δ)) ≡ᵒ ↓ᵒ (suc k) (S ((↓ᵖ k P) , δ))

goodness : ∀{Γ} → Times Γ → (RecEnv Γ → Setᵒ) → Set₁
goodness {[]} ts S = topᵖ
goodness {A ∷ Γ} (cons Now ts) S = ∀ δ → nonexpansiveˢ S δ
goodness {A ∷ Γ} (cons Later ts) S = ∀ δ → wellfoundedˢ S δ

g⇒g : ∀{Γ}{ts : Times Γ}{S : RecEnv Γ → Setᵒ}
   → good-fun ts S
   → goodness ts S
g⇒g {[]} {ts} {S} gs = ttᵖ
g⇒g {A ∷ Γ} {cons Now ts} {S} gs δ P k = gs zeroˢ (P , δ) k k ≤-refl
g⇒g {A ∷ Γ} {cons Later ts} {S} gs δ P k = gs zeroˢ (P , δ) k k ≤-refl

≡ᵈ-refl : ∀{Γ}{δ : RecEnv Γ}
   → δ ≡ᵈ δ
≡ᵈ-refl {[]} {δ} = tt
≡ᵈ-refl {A ∷ Γ} {(P , δ)} = (λ a → ≡ᵒ-refl refl) , ≡ᵈ-refl
\end{code}


\begin{code}
cong-head : ∀{Γ : Context} → (RecEnv Γ → Setᵒ) → Set₁
cong-head {[]} S = topᵖ
cong-head {A ∷ Γ} S =
  ∀{P Q} → (∀ a → P a ≡ᵒ Q a) → (∀ δ → S (P , δ) ≡ᵒ S (Q , δ))

cong⇒head : ∀{Γ : Context}{S : RecEnv Γ → Setᵒ}
  → congruent S
  → cong-head S
cong⇒head {[]} {S} congS′ = ttᵖ
cong⇒head {A ∷ Γ} {S} congS′ P=Q δ = congS′ (P=Q , ≡ᵈ-refl{Γ}{δ})
\end{code}

\begin{code}
lemma15a-toFun : ∀{Γ}{A}{ts : Times Γ}{P Q : Predᵒ A}{δ : RecEnv Γ}
  → (j : ℕ) → (Fᵃ : A → Setˢ (A ∷ Γ) (cons Later ts)) → (a : A)
  → ↓ᵒ j (iter j (toFun δ Fᵃ) P a) ≡ᵒ ↓ᵒ j (iter j (toFun δ Fᵃ) Q a)
lemma15a-toFun {Γ}{A}{ts}{P}{Q}{δ} j Fᵃ a =
  lemma15a j (toFun δ Fᵃ) a (λ a P k → g⇒g (good (Fᵃ a)) δ P k)
    (λ {P}{Q} P=Q a → cong⇒head (congr (Fᵃ a)) P=Q δ)
\end{code}




\begin{code}
lemma15b-toFun : ∀{Γ}{A}{ts : Times Γ}{P : Predᵒ A}{δ : RecEnv Γ}
  → (k j : ℕ) → (F : A → Setˢ (A ∷ Γ) (cons Later ts)) → (a : A)
  → j ≤ k
  → ↓ᵒ j (iter j (toFun δ F) P a) ≡ᵒ ↓ᵒ j (iter k (toFun δ F) P a)
lemma15b-toFun{Γ}{A}{ts}{P}{δ} k j F a j≤k =
  let f = toFun δ F in
  ↓ᵒ j (iter j f P a)                     ⩦⟨ lemma15a-toFun j F a ⟩
  ↓ᵒ j (iter j f (iter (k ∸ j) f P) a)
                      ⩦⟨ cong-↓{A}{j}{iter j f (iter (k ∸ j) f P)}{iter k f P}
                              (λ a → ≡ᵖ-refl (iter-subtract f j k j≤k)) a ⟩
  ↓ᵒ j (iter k f P a)   ∎
\end{code}

\begin{code}
dc-iter : ∀(i : ℕ){A} (F : Predᵒ A → Predᵒ A) → ∀ a
   → downClosed (#(iter i F ⊤ᵖ a))
dc-iter zero F = λ a n _ k _ → tt
dc-iter (suc i) F = λ a → down (F (iter i F ⊤ᵖ) a)
\end{code}

The $μᵖ$ function is downward closed when applied to the
result of $\mathsf{toFun}$.
\begin{code}
down-μᵖ : ∀{Γ}{ts : Times Γ}{A}{P : A → Setˢ (A ∷ Γ) (cons Later ts)}
    {a : A}{δ : RecEnv Γ}
  → downClosed (μᵖ (toFun δ P) a)
down-μᵖ {Γ}{ts}{A}{P}{a}{δ} k iterskPk zero j≤k = tz (toFun δ P (id ⊤ᵖ) a)
down-μᵖ {Γ}{ts}{A}{P}{a}{δ} (suc k′) μPa (suc j′) (s≤s j′≤k′) =
  let f = toFun δ P in
  let dc-iter-ssk : downClosed (# ((iter (suc (suc k′)) f ⊤ᵖ) a))
      dc-iter-ssk = dc-iter (suc (suc k′)) (toFun δ P) a in
  let ↓-iter-ssk : #(↓ᵒ (suc (suc j′)) ((iter (suc (suc k′)) f ⊤ᵖ) a))(suc j′)
      ↓-iter-ssk = ≤-refl , (dc-iter-ssk (suc k′) μPa (suc j′) (s≤s j′≤k′))
  in
  let eq : ↓ᵒ (suc (suc j′)) ((iter (suc (suc j′)) (toFun δ P) ⊤ᵖ) a)
        ≡ᵒ ↓ᵒ (suc (suc j′)) ((iter (suc (suc k′)) (toFun δ P) ⊤ᵖ) a)
      eq = lemma15b-toFun {P = ⊤ᵖ}{δ} (suc (suc k′)) (suc (suc j′)) P a
                (s≤s (s≤s j′≤k′)) in
  let ↓-iter-ssj : #(↓ᵒ (suc (suc j′)) ((iter (suc (suc j′)) f ⊤ᵖ) a))
                    (suc j′)
      ↓-iter-ssj = ⇔-to (≡ᵒ-elim (≡ᵒ-sym eq)) ↓-iter-ssk in
  proj₂ ↓-iter-ssj
\end{code}

\begin{code}
muᵒ : ∀{Γ}{ts : Times Γ}{A}
   → (A → Setˢ (A ∷ Γ) (cons Later ts))
   → RecEnv Γ
     ----------------------------------
   → (A → Setᵒ)
muᵒ {Γ}{ts}{A} f δ a =
  record { # = μᵖ (toFun δ f) a
         ; down = down-μᵖ {Γ}{ts}{A}{f}{a}{δ}
         ; tz = tz ((toFun δ f) ⊤ᵖ a) }
\end{code}

\begin{code}
abstract
  lemma18a : ∀{Γ}{Δ : Times Γ}{A} (k : ℕ) (F : A → Setˢ (A ∷ Γ) (cons Later Δ))
     (a : A) (δ : RecEnv Γ)
     → ↓ᵒ k (muᵒ F δ a) ≡ᵒ ↓ᵒ k (iter k (toFun δ F) ⊤ᵖ a)
  lemma18a zero F a δ zero = (λ x → tt) , (λ {x → tt})
  lemma18a zero F a δ (suc j) = (λ {()}) , λ {()}
  lemma18a (suc k) F a δ zero = (λ {x → tt}) , λ {x → tt}
  lemma18a (suc k′) F a δ (suc j′) =
    let k = suc k′ in
    let j = suc j′ in 
    ↓ k (λ j₁ → # (toFun δ F (iter j₁ (toFun δ F) ⊤ᵖ) a) j₁) j
         ⩦⟨ ⩦-refl refl ⟩    
    j < k  ×  # (iter (suc j) (toFun δ F) ⊤ᵖ a) j
         ⩦⟨ (λ {(s≤s x , y) → s≤s x , ≤-refl , y})
            , (λ {(s≤s x , (y , z)) → (s≤s x) , z}) ⟩
    j < k  ×  # (↓ᵒ (suc j) (iter (suc j) (toFun δ F) ⊤ᵖ a)) j
         ⩦⟨ EQ  ⟩    
    j < k  ×  # (↓ᵒ (suc j) (iter k (toFun δ F) ⊤ᵖ a)) j
         ⩦⟨ (λ {(s≤s x , (s≤s y , z)) → (s≤s x) , z})
             , (λ {(x , y) → x , (≤-refl , y)})  ⟩
    j < k  ×  # (iter k (toFun δ F) ⊤ᵖ a) j
       ⩦⟨ ⩦-refl refl  ⟩    
    ↓ k (# (iter k (toFun δ F) ⊤ᵖ a)) j   ∎
    where
    k : ℕ
    k = suc k′
    j : ℕ
    j = suc j′
    EQ : (j < k  ×  # (↓ᵒ (suc j) (iter (suc j) (toFun δ F) ⊤ᵖ a)) j)
         ⇔ (j < k  ×  # (↓ᵒ (suc j) (iter k (toFun δ F) ⊤ᵖ a)) j)
    EQ =
      (λ {(s≤s x , y) →
        let xx = proj₁ ((lemma15b-toFun (suc k′) (suc j) F a (s≤s x)) j) y in
        (s≤s x) , (≤-refl , proj₂ xx)})
      ,
      λ {(s≤s x , (s≤s y , z)) →
        let xx = proj₂ ((lemma15b-toFun(suc k′)(suc j) F a (s≤s x)) j) (≤-refl , z) in
        s≤s x , (≤-refl , (proj₂ xx))}

lemma18b : ∀{Γ}{Δ : Times Γ}{A} (j : ℕ) (F : A → Setˢ (A ∷ Γ) (cons Later Δ)) (a : A) (δ : RecEnv Γ)
     → ↓ᵒ (suc j) (♯ (F a) (muᵒ F δ , δ))
       ≡ᵒ ↓ᵒ (suc j) (iter (suc j) (toFun δ F) ⊤ᵖ a)
lemma18b{Γ}{Δ}{A} j F a δ =
   ↓ᵒ (suc j) (♯ (F a) (muᵒ F δ , δ))      ⩦⟨ g⇒g (good (F a)) δ (muᵒ F δ) j ⟩
   ↓ᵒ (suc j) (♯ (F a) (↓ᵖ j (muᵒ F δ) , δ))
                                     ⩦⟨ cong-↓ (λ a → cong⇒head (congr (F a))
                                               (λ a → lemma18a j F a δ ) δ) a ⟩
   ↓ᵒ (suc j) (♯ (F a) (↓ᵖ j (iter j (toFun δ F) ⊤ᵖ) , δ))
             ⩦⟨ ≡ᵖ-sym{A} (g⇒g (good (F a)) δ (iter j (toFun δ F) ⊤ᵖ) j) {a} ⟩
   ↓ᵒ (suc j) (♯ (F a) (iter j (toFun δ F) ⊤ᵖ , δ))           ⩦⟨ ≡ᵒ-refl refl ⟩
   ↓ᵒ (suc j) (iter (suc j) (toFun δ F) ⊤ᵖ a)     ∎
       
lemma19a : ∀{Γ}{Δ : Times Γ}{A} (F : A → Setˢ (A ∷ Γ) (cons Later Δ)) (a : A) (j : ℕ) (δ : RecEnv Γ)
   → ↓ᵒ j (muᵒ F δ a) ≡ᵒ ↓ᵒ j (♯ (F a) (muᵒ F δ , δ))
lemma19a{Γ}{Δ}{A} F a j δ = 
    ↓ᵒ j (muᵒ F δ a)                                     ⩦⟨ lemma18a j F a δ  ⟩
    ↓ᵒ j (iter j (toFun δ F) ⊤ᵖ a)        ⩦⟨ lemma15b-toFun (suc j) j F a (n≤1+n j) ⟩
    ↓ᵒ j (iter (suc j) (toFun δ F) ⊤ᵖ a)
              ⩦⟨ ≡ᵖ-sym (lemma17{A}{(iter (suc j) (toFun δ F) ⊤ᵖ)}{j}{a}) {a} ⟩
    ↓ᵒ j (↓ᵒ (suc j) (iter (suc j) (toFun δ F) ⊤ᵖ a))
                              ⩦⟨ cong-↓ (λ a → ≡ᵒ-sym (lemma18b j F a δ))  a  ⟩
    ↓ᵒ j (↓ᵒ (suc j) (♯ (F a) (muᵒ F δ , δ)))
                         ⩦⟨ lemma17{A}{λ a → (♯ (F a) (muᵒ F δ , δ))}{j}{a}  ⟩
    ↓ᵒ j (♯ (F a) (muᵒ F δ , δ))                      ∎
\end{code}

\begin{code}
good-now : ∀{Γ}{A}{x : Γ ∋ A}{Δ : Times Γ}{S : RecEnv Γ → Setᵒ}
   → good-var x (timeof x Δ) S
   → timeof x Δ ≡ Now
   → ∀ δ j k → k ≤ j → ↓ᵒ k (S δ) ≡ᵒ ↓ᵒ k (S (↓ᵈ j x δ))
good-now gS eq rewrite eq = gS

good-later : ∀{Γ}{A}{x : Γ ∋ A}{Δ : Times Γ}{S : RecEnv Γ → Setᵒ}
   → good-var x (timeof x Δ) S
   → timeof x Δ ≡ Later
   → ∀ δ j k → k ≤ j → ↓ᵒ (suc k) (S δ) ≡ᵒ ↓ᵒ (suc k) (S (↓ᵈ j x δ))
good-later gS eq rewrite eq = gS

good-now-mu : ∀{Γ}{Δ : Times Γ}{A}{B}
   → (S : A → Setˢ (A ∷ Γ) (cons Later Δ))
     (a : A) (x : Γ ∋ B)
   → timeof x Δ ≡ Now
   → (δ : RecEnv Γ) (k j : ℕ)
   → (k ≤ j)
   → ↓ᵒ k (muᵒ S δ a) ≡ᵒ ↓ᵒ k (muᵒ S (↓ᵈ j x δ) a)
good-now-mu {Γ} {Δ} {A} S a x time-x δ zero j k≤j = ↓ᵒ-zero
good-now-mu {Γ} {Δ} {A}{B} S a x time-x δ (suc k′) j k≤j =
  let k = suc k′ in
  let gSa = good-now{A = B}{sucˢ x}{Δ = cons Later Δ}
              (good (S a) (sucˢ x)) time-x (muᵒ S δ , δ)
              j k k≤j in
  let gSaz = good (S a) zeroˢ (muᵒ S δ , ↓ᵈ j x δ) k′ k′ ≤-refl in
  let gSaz2 = good (S a) zeroˢ (muᵒ S (↓ᵈ j x δ) , ↓ᵈ j x δ) k′ k′ ≤-refl in
  let IH = cong-↓ (λ a → congr (S a)
           ((λ a → good-now-mu S a x time-x δ k′ j (≤-trans (n≤1+n _) k≤j))
            , ≡ᵈ-refl)) a in
  ↓ᵒ k (muᵒ S δ a)                                        ⩦⟨ lemma19a S a k δ ⟩
  ↓ᵒ k (♯ (S a) (muᵒ S δ , δ))                                         ⩦⟨ gSa ⟩
  ↓ᵒ k (♯ (S a) (muᵒ S δ , ↓ᵈ j x δ))                                 ⩦⟨ gSaz ⟩
  ↓ᵒ k (♯ (S a) (↓ᵖ k′ (muᵒ S δ) , ↓ᵈ j x δ))                           ⩦⟨ IH ⟩
  ↓ᵒ k (♯ (S a) (↓ᵖ k′ (muᵒ S (↓ᵈ j x δ)) , ↓ᵈ j x δ))        ⩦⟨ ≡ᵒ-sym gSaz2 ⟩
  ↓ᵒ k (♯ (S a) (muᵒ S (↓ᵈ j x δ) , ↓ᵈ j x δ))
                                        ⩦⟨ ≡ᵒ-sym (lemma19a S a k (↓ᵈ j x δ)) ⟩
  ↓ᵒ k (muᵒ S (↓ᵈ j x δ) a)   ∎

abstract
  down-1-mu : ∀{Γ}{Δ : Times Γ}{A}{B}
       (S : A → Setˢ (A ∷ Γ) (cons Later Δ))
       (a : A) (x : Γ ∋ B) (δ : RecEnv Γ) (j : ℕ)
   → ↓ᵒ 1 (muᵒ S δ a) ≡ᵒ ↓ᵒ 1 (muᵒ S (↓ᵈ j x δ) a)
  down-1-mu S a x δ j zero = (λ _ → tt) , (λ _ → tt)
  down-1-mu S a x δ j (suc i) = (λ { (s≤s () , _)}) , λ { (s≤s () , _)}

good-later-mu : ∀{Γ}{Δ : Times Γ}{A}{B}
   → (S : A → Setˢ (A ∷ Γ) (cons Later Δ))
     (a : A) (x : Γ ∋ B)
   → timeof x Δ ≡ Later
   → (δ : RecEnv Γ) (k j : ℕ)
   → (k ≤ j)
   → ↓ᵒ (suc k) (muᵒ S δ a) ≡ᵒ ↓ᵒ (suc k) (muᵒ S (↓ᵈ j x δ) a)
good-later-mu {Γ} {Δ} {A} S a x time-x δ zero j k≤j = down-1-mu S a x δ j
good-later-mu {Γ} {Δ} {A} {B} S a x time-x δ (suc k′) j k≤j =
  let k = suc k′ in
  let gSa = good-later{A = B}{sucˢ x}{Δ = cons Later Δ}
              (good (S a) (sucˢ x)) time-x (muᵒ S δ , δ)
              j k k≤j in
  let gSaz = good (S a) zeroˢ (muᵒ S δ , ↓ᵈ j x δ) (suc k′) k ≤-refl in
  let gSaz2 = good (S a) zeroˢ (muᵒ S (↓ᵈ j x δ) , ↓ᵈ j x δ) k k ≤-refl in
  let IH = cong-↓ (λ a → congr (S a)
           ((λ a → good-later-mu S a x time-x δ k′ j (≤-trans (n≤1+n _) k≤j))
            , ≡ᵈ-refl)) a in

  ↓ᵒ (suc k) (muᵒ S δ a)                            ⩦⟨ lemma19a S a (suc k) δ ⟩
  ↓ᵒ (suc k) (♯ (S a) (muᵒ S δ , δ))                                   ⩦⟨ gSa ⟩
  ↓ᵒ (suc k) (♯ (S a) (muᵒ S δ , ↓ᵈ j x δ))                           ⩦⟨ gSaz ⟩
  ↓ᵒ (suc k) (♯ (S a) (↓ᵖ k (muᵒ S δ) , ↓ᵈ j x δ))                      ⩦⟨ IH ⟩
  ↓ᵒ (suc k) (♯ (S a) (↓ᵖ k (muᵒ S (↓ᵈ j x δ)) , ↓ᵈ j x δ))   ⩦⟨ ≡ᵒ-sym gSaz2 ⟩
  ↓ᵒ (suc k) (♯ (S a) (muᵒ S (↓ᵈ j x δ) , (↓ᵈ j x δ)))
                              ⩦⟨ ≡ᵒ-sym (lemma19a S a (suc k) (↓ᵈ j x δ)) ⟩
  ↓ᵒ (suc k) (muᵒ S (↓ᵈ j x δ) a)   ∎

good-fun-mu : ∀{Γ}{Δ : Times Γ}{A}
   → (S : A → Setˢ (A ∷ Γ) (cons Later Δ))
   → (a : A)
   → good-fun Δ (λ δ → muᵒ S δ a)
good-fun-mu {Γ} {Δ} {A} S a x
    with timeof x Δ in time-x
... | Now = λ δ j k k≤j → good-now-mu S a x time-x δ k j k≤j
... | Later = λ δ j k k≤j → good-later-mu S a x time-x δ k j k≤j

cong-toFun : ∀{A}{Γ}{δ δ′ : RecEnv Γ}{Δ : Times Γ}
   → (S : A → Setˢ (A ∷ Γ) (cons Later Δ))
   → δ ≡ᵈ δ′
   → (P Q : Predᵒ A)
   → (a : A)
   → (∀ b → P b ≡ᵒ Q b)
   → toFun δ S P a ≡ᵒ toFun δ′ S Q a
cong-toFun{A}{Γ}{δ}{δ′} S δ=δ′ P Q a P=Q =
  let Pδ=Qδ′ : (P , δ) ≡ᵈ (Q , δ′)
      Pδ=Qδ′ = P=Q , δ=δ′ in
  congr (S a) Pδ=Qδ′

cong-iter : ∀{A}{a : A}
  → (i : ℕ)
  → (F G : Predᵒ A → Predᵒ A)
  → (∀ P Q a → (∀ b → P b ≡ᵒ Q b) → F P a ≡ᵒ G Q a)
  → (I : Predᵒ A)
  → iter i F I a ≡ᵒ iter i G I a
cong-iter zero F G F=G I = ≡ᵒ-refl refl
cong-iter{A}{a} (suc i) F G F=G I =
  let IH = λ b → cong-iter{A}{b} i F G F=G I in
  F=G (iter i F I) (iter i G I) a IH

congruent-mu : ∀{Γ}{Δ : Times Γ}{A} (P : A → Setˢ (A ∷ Γ) (cons Later Δ)) (a : A)
   → congruent (λ δ → muᵒ P δ a)
congruent-mu{Γ}{Δ}{A} P a {δ}{δ′} δ=δ′ = ≡ᵒ-intro Goal
  where
  Goal : (k : ℕ) → μᵖ (toFun δ P) a k ⇔ μᵖ (toFun δ′ P) a k
  Goal k = ≡ᵒ-elim (cong-iter{A}{a} (suc k) (toFun δ P) (toFun δ′ P)
                    (cong-toFun P δ=δ′) ⊤ᵖ)
\end{code}



\begin{code}
μˢ {Γ}{Δ}{A} P a =
  record { ♯ = λ δ → muᵒ P δ a
         ; good = good-fun-mu P a
         ; congr = congruent-mu P a }
\end{code}



\subsection{False}

The false formula for SIL is embedded in Agda by defining an instance
of this record type, with the representation function mapping zero
to true and every other natural number to false. The proofs of
downward-closedness and true-at-zero are straightforward.

\begin{code}
⊥ᵒ : Setᵒ
⊥ᵒ = record { # = λ { zero → ⊤ ; (suc k) → ⊥}
            ; down = λ { zero x .zero z≤n → tt} ; tz = tt }
\end{code}


\subsection{Constant}

A step-indexed logic such as LSLR is typically specialized to include
atomic formulas to express properties of programs in a particular
language. Here instead we simply allow arbitrary Agda propositions to
be included in a step-indexed proposition by way of the following
operator. So, given a proposition $ϕ$, the formula $ϕᵒ$ is true at
zero and everywhere else it is equivalent to $ϕ$.

\begin{code}
_ᵒ : Set → Setᵒ
ϕ ᵒ = record { # = λ { zero → ⊤ ; (suc k) → ϕ }
             ; down = λ { k ϕk zero j≤k → tt
                        ; (suc k) ϕk (suc j) j≤k → ϕk}
             ; tz = tt }
\end{code}

\begin{code}
const-good : ∀{Γ}{Δ : Times Γ}{A}
   → (S : Set)
   → (x : Γ ∋ A)
   → good-var x (timeof x Δ) (λ δ → S ᵒ)
const-good{Γ}{Δ} S x
    with timeof x Δ
... | Now = λ δ j k k≤j → ≡ᵒ-refl refl
... | Later = λ δ j k k≤j → ≡ᵒ-refl refl

S ˢ = record { ♯ = λ δ → S ᵒ
             ; good = λ x → const-good S x
             ; congr = λ d=d′ → ≡ᵒ-refl refl
             }
\end{code}


\subsection{Forall}

The forall quantifier maps a step-indexed predicate to $Setᵒ$.

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


\begin{code}
abstract
  down-∀ : ∀{A}{P : Predᵒ A}{k}
    → ↓ᵒ k (∀ᵒ[ a ] P a) ≡ᵒ ↓ᵒ k (∀ᵒ[ a ] ↓ᵒ k (P a))
  down-∀ {A} {P} {k} zero = (λ x → tt) , (λ x → tt)
  down-∀ {A} {P} {k} (suc i) =
    (λ {(a , b) → a , (λ c → a , b c)})
    , λ {(a , b) → a , (λ a → proj₂ (b a))}

  cong-∀ : ∀{A}{P Q : Predᵒ A}
    → (∀ a → P a ≡ᵒ Q a)
    → (∀ᵒ P) ≡ᵒ (∀ᵒ Q)
  cong-∀ {A} {P} {k} P=Q zero =
      (λ z a → proj₁ (P=Q a zero) (z a)) , (λ _ a → tz (P a))
  cong-∀ {A} {P} {k} P=Q (suc i) =
        (λ z a → proj₁ (P=Q a (suc i)) (z a))
      , (λ z a → proj₂ (P=Q a (suc i)) (z a))
  
good-all : ∀{Γ}{Δ : Times Γ}{A : Set}
   (P : A → Setˢ Γ Δ)
  → good-fun Δ (λ δ → ∀ᵒ[ a ] ♯ (P a) δ)
good-all {Γ}{Δ}{A} P x
    with timeof x Δ in time-x
... | Now = λ δ j k k≤j →
      ↓ᵒ k (∀ᵒ[ a ] ♯ (P a) δ)                                      ⩦⟨ down-∀ ⟩
      ↓ᵒ k (∀ᵒ[ a ] ↓ᵒ k (♯ (P a) δ))
          ⩦⟨ cong-↓ᵒ k (cong-∀(λ a → good-now(good(P a) x) time-x δ j k k≤j)) ⟩
      ↓ᵒ k (∀ᵒ[ a ] ↓ᵒ k (♯ (P a) (↓ᵈ j x δ)))               ⩦⟨ ≡ᵒ-sym down-∀ ⟩
      ↓ᵒ k (∀ᵒ[ a ] ♯ (P a) (↓ᵈ j x δ))   ∎

... | Later = λ δ j k k≤j → 
      ↓ᵒ (suc k) (∀ᵒ[ a ] ♯ (P a) δ)                                ⩦⟨ down-∀ ⟩
      ↓ᵒ (suc k) (∀ᵒ[ a ] ↓ᵒ (suc k) (♯ (P a) δ))
                      ⩦⟨ cong-↓ᵒ (suc k) (cong-∀
                          (λ a → good-later (good (P a) x) time-x δ j k k≤j)) ⟩
      ↓ᵒ (suc k) (∀ᵒ[ a ] ↓ᵒ (suc k) (♯ (P a) (↓ᵈ j x δ)))   ⩦⟨ ≡ᵒ-sym down-∀ ⟩
      ↓ᵒ (suc k) (∀ᵒ[ a ] ♯ (P a) (↓ᵈ j x δ))            ∎

∀ˢ{Γ}{Δ}{A} P =
  record { ♯ = λ δ → ∀ᵒ[ a ] ♯ (P a) δ
         ; good = good-all P
         ; congr = λ d=d′ → cong-∀ λ a → congr (P a) d=d′
         }

∀ˢ-syntax = ∀ˢ
infix 1 ∀ˢ-syntax
syntax ∀ˢ-syntax (λ x → P) = ∀ˢ[ x ] P
\end{code}

\subsection{Exist}


\noindent We define the formula $∃ᵒ P$ at $k$ to mean that there
exists a value $a ∈ A$ such that $P \app a$ is true at $k$.  For the
true-at-zero property, we use the \textsf{elt} field of
\textsf{Inhabited} to obtain a witness.

\begin{code}
∃ᵒ : ∀{{_ : Inhabited A}} → Predᵒ A → Setᵒ
∃ᵒ P = record { # = λ k → ∃[ a ] # (P a) k
              ; down = λ n (a , Pa) k k≤n → a , (down (P a) n Pa k k≤n)
              ; tz = elt , tz (P elt) }

∃ᵒ-syntax = ∃ᵒ
infix 2 ∃ᵒ-syntax
syntax ∃ᵒ-syntax (λ x → P) = ∃ᵒ[ x ] P
\end{code}

\begin{code}
abstract
  down-∃ : ∀{A}{P : Predᵒ A}{k}{{_ : Inhabited A}}
    → ↓ᵒ k (∃ᵒ[ a ] P a) ≡ᵒ ↓ᵒ k (∃ᵒ[ a ] ↓ᵒ k (P a))
  down-∃ {A} {P} {k} zero = (λ x → tt) , (λ x → tt)
  down-∃ {A} {P} {k} (suc i) =
    (λ {(a , (b , c)) → a , (b , (a , c))})
    , λ { (a , b , c) → a , b , proj₂ c}

  cong-∃ : ∀{A}{P Q : Predᵒ A}{{_ : Inhabited A}}
    → (∀ a → P a ≡ᵒ Q a)
    → (∃ᵒ P) ≡ᵒ (∃ᵒ Q)
  cong-∃ {A} {P} {Q} P=Q i =
      (λ {(a , b) → a , proj₁ (P=Q a i) b})
      , λ {(a , b) → a , (proj₂ (P=Q a i) b)}

good-exists : ∀{Γ}{Δ : Times Γ}{A : Set}{{_ : Inhabited A}}
   (P : A → Setˢ Γ Δ)
  → good-fun Δ (λ δ → ∃ᵒ[ a ] ♯ (P a) δ)
good-exists {Γ}{Δ}{A} P x
    with timeof x Δ in time-x
... | Now = λ δ j k k≤j →
      ↓ᵒ k (∃ᵒ[ a ] ♯ (P a) δ)                                      ⩦⟨ down-∃ ⟩
      ↓ᵒ k (∃ᵒ[ a ] ↓ᵒ k (♯ (P a) δ))
          ⩦⟨ cong-↓ᵒ k (cong-∃(λ a → good-now(good(P a) x) time-x δ j k k≤j)) ⟩
      ↓ᵒ k (∃ᵒ[ a ] ↓ᵒ k (♯ (P a) (↓ᵈ j x δ)))               ⩦⟨ ≡ᵒ-sym down-∃ ⟩
      ↓ᵒ k (∃ᵒ[ a ] ♯ (P a) (↓ᵈ j x δ))   ∎
... | Later = λ δ j k k≤j →
      ↓ᵒ (suc k) (∃ᵒ[ a ] ♯ (P a) δ)                                ⩦⟨ down-∃ ⟩
      ↓ᵒ (suc k) (∃ᵒ[ a ] ↓ᵒ (suc k) (♯ (P a) δ))
                      ⩦⟨ cong-↓ᵒ (suc k) (cong-∃
                          (λ a → good-later (good (P a) x) time-x δ j k k≤j)) ⟩
      ↓ᵒ (suc k) (∃ᵒ[ a ] ↓ᵒ (suc k) (♯ (P a) (↓ᵈ j x δ)))   ⩦⟨ ≡ᵒ-sym down-∃ ⟩
      ↓ᵒ (suc k) (∃ᵒ[ a ] ♯ (P a) (↓ᵈ j x δ))            ∎

∃ˢ{Γ}{Δ}{A} P =
  record { ♯ = λ δ → ∃ᵒ[ a ] ♯ (P a) δ
         ; good = good-exists P
         ; congr = λ d=d′ → cong-∃ λ a → congr (P a) d=d′ }

∃ˢ-syntax = ∃ˢ
infix 1 ∃ˢ-syntax
syntax ∃ˢ-syntax (λ x → P) = ∃ˢ[ x ] P
\end{code}

\subsection{Later Operator}

Next we come to the important ``later`` operator, written $▷ᵒ ϕ$.  Of
course, at zero it is true. For any other index of the form
$\mathsf{suc}\app k$, $▷ᵒ ϕ$ means $ϕ$ at $k$, that is, subtract
one from the step index.

\begin{code}
▷ᵒ_ : Setᵒ → Setᵒ
▷ᵒ ϕ = record { # = λ { zero → ⊤ ; (suc k) → # ϕ k }
              ; down = λ { zero ▷ϕn .zero z≤n → tt
                         ; (suc n) ▷ϕn .zero z≤n → tt
                         ; (suc n) ▷ϕn (suc k) (s≤s k≤n) → down ϕ n ▷ϕn k k≤n}
              ; tz = tt }
\end{code}

\begin{code}
abstract
  cong-▷ : ∀{S T : Setᵒ}
    → S ≡ᵒ T
    → ▷ᵒ S ≡ᵒ ▷ᵒ T
  cong-▷ S=T zero = (λ x → tt) , (λ x → tt)
  cong-▷ S=T (suc i) = (proj₁ (S=T i)) , (proj₂ (S=T i))

abstract
  down-▷ : ∀{k} (S : Setᵒ)
    → ↓ᵒ (suc k) (▷ᵒ S) ≡ᵒ ↓ᵒ (suc k) (▷ᵒ (↓ᵒ k S))
  down-▷ S zero = ⇔-intro (λ x → tt) (λ x → tt)
  down-▷ S (suc zero) =
      ⇔-intro (λ {(a , b) → a , tt}) (λ {(a , b) → a , (tz S)})
  down-▷ S (suc (suc i)) =
    ⇔-intro
    (λ {(s≤s i≤1+k , ▷Si) →
                 s≤s i≤1+k , i≤1+k , ▷Si})
    (λ {(i≤1+k , (_ , ▷Si)) → i≤1+k , ▷Si})

abstract
  lemma17ᵒ : ∀{S : Setᵒ}
     → (k : ℕ)
     → ↓ᵒ k (↓ᵒ (suc k) S) ≡ᵒ ↓ᵒ k S
  lemma17ᵒ {S} k zero = (λ _ → tt) , (λ _ → tt)
  lemma17ᵒ {S} k (suc i) = (λ {(x , (y , z)) → x , z}) , λ {(x , y) → x , ((s≤s (<⇒≤ x)) , y)}

good-▷ : ∀{Γ}{Δ : Times Γ}
   → (S : Setˢ Γ Δ)
   → good-fun (laters Γ) (λ δ → ▷ᵒ (♯ S δ))
good-▷{Γ}{Δ} S x
    with good S x
... | gS
    with timeof x Δ
... | Now rewrite timeof-later{Γ} x =
  λ δ j k k≤j →
  ↓ᵒ (suc k) (▷ᵒ (♯ S δ))                              ⩦⟨ down-▷ {k} (♯ S δ) ⟩ 
  ↓ᵒ (suc k) (▷ᵒ (↓ᵒ k (♯ S δ)))  ⩦⟨ cong-↓ᵒ (suc k) (cong-▷ (gS δ j k k≤j)) ⟩ 
  ↓ᵒ (suc k) (▷ᵒ (↓ᵒ k (♯ S (↓ᵈ j x δ))))
                                     ⩦⟨ ≡ᵒ-sym (down-▷ {k} (♯ S (↓ᵈ j x δ))) ⟩ 
  ↓ᵒ (suc k) (▷ᵒ (♯ S (↓ᵈ j x δ)))   ∎
... | Later rewrite timeof-later{Γ} x =
  λ δ j k k≤j →
  ↓ᵒ (suc k) (▷ᵒ (♯ S δ))                       ⩦⟨ ≡ᵒ-sym (lemma17ᵒ (suc k)) ⟩ 
  ↓ᵒ (suc k) (↓ᵒ (2 + k) (▷ᵒ (♯ S δ)))    ⩦⟨ cong-↓ᵒ (suc k) (down-▷ _) ⟩
  ↓ᵒ (suc k) (↓ᵒ (2 + k) (▷ᵒ (↓ᵒ (suc k) (♯ S δ))))
           ⩦⟨ cong-↓ᵒ (suc k) (cong-↓ᵒ (suc (suc k)) (cong-▷ (gS δ j k k≤j))) ⟩
  ↓ᵒ (suc k) (↓ᵒ (2 + k) (▷ᵒ (↓ᵒ (suc k) (♯ S (↓ᵈ j x δ)))))
                                       ⩦⟨ ≡ᵒ-sym (cong-↓ᵒ (suc k) (down-▷ _)) ⟩
  ↓ᵒ (suc k) (↓ᵒ (2 + k) (▷ᵒ (♯ S (↓ᵈ j x δ))))     ⩦⟨ lemma17ᵒ (suc k) ⟩
  ↓ᵒ (suc k) (▷ᵒ (♯ S (↓ᵈ j x δ)))    ∎

▷ˢ S = record { ♯ = λ δ → ▷ᵒ (♯ S δ)
              ; good = good-▷ S
              ; congr = λ d=d′ → cong-▷ (congr S d=d′)
              }
\end{code}

{---------------------- Only Step-indexed  ------------------------------------}

\begin{code}
step-indexed-good : ∀{Γ}{Δ : Times Γ}{A}
   → (S : Setᵒ)
   → (x : Γ ∋ A)
   → good-var x (timeof x Δ) (λ δ → S)
step-indexed-good{Γ}{Δ} S x
    with timeof x Δ
... | Now = λ δ j k x₁ → ≡ᵒ-refl refl
... | Later = λ δ j k x₁ → ≡ᵒ-refl refl

_ⁱ : ∀{Γ} → Setᵒ → Setˢ Γ (laters Γ)
S ⁱ = record { ♯ = λ δ → S
             ; good = λ x → step-indexed-good S x
             ; congr = λ d=d′ → ≡ᵒ-refl refl
             }
\end{code}

\subsection{Conjunction}

Next we define conjunction in SIL. Given two step-indexed propositions
$ϕ$ and $ψ$, their conjunction is the function that takes the
conjunction of applying them to the step index. The proofs of
downward-closedness and true-at-zero are straightforward, relying on
the proofs of these properties for $ϕ$ and $ψ$.

\begin{code}
_×ᵒ_ : Setᵒ → Setᵒ → Setᵒ
ϕ ×ᵒ ψ = record { # = λ k → # ϕ k × # ψ k
                ; down = λ k (ϕk , ψk) j j≤k →
                          (down ϕ k ϕk j j≤k) , (down ψ k ψk j j≤k)
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

good-pair : ∀{Γ}{Δ₁ Δ₂ : Times Γ}
   (S : Setˢ Γ Δ₁) (T : Setˢ Γ Δ₂)
   → good-fun (Δ₁ ∪ Δ₂) (λ δ → ♯ S δ ×ᵒ ♯ T δ)
good-pair {Γ}{Δ₁}{Δ₂} S T {A} x
    rewrite timeof-combine {Γ}{Δ₁}{Δ₂}{A}{x}
    with timeof x Δ₁ in time-x1 | timeof x Δ₂ in time-x2
... | Now | Now = λ δ j k k≤j →
    let gS = good-now (good S x) time-x1 δ j k k≤j in
    let gT = good-now (good T x) time-x2 δ j k k≤j in
    ↓ᵒ k (♯ S δ ×ᵒ ♯ T δ)                                         ⩦⟨ down-× ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S δ) ×ᵒ ↓ᵒ k (♯ T δ))
                                     ⩦⟨ cong-↓ᵒ k (cong-×ᵒ gS (≡ᵒ-refl refl)) ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S (↓ᵈ j x δ)) ×ᵒ ↓ᵒ k (♯ T δ))
                                     ⩦⟨ cong-↓ᵒ k (cong-×ᵒ (≡ᵒ-refl refl) gT) ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S (↓ᵈ j x δ)) ×ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ)))   ⩦⟨ ≡ᵒ-sym down-× ⟩
    ↓ᵒ k (♯ S (↓ᵈ j x δ) ×ᵒ ♯ T (↓ᵈ j x δ))  ∎
... | Now | Later = λ δ j k k≤j →
    let gS = good-now (good S x) time-x1 δ j k k≤j in
    let gT = good-later (good T x) time-x2 δ j k k≤j in
    ↓ᵒ k (♯ S δ ×ᵒ ♯ T δ)                             ⩦⟨ ≡ᵒ-sym (lemma17ᵒ k) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (♯ S δ ×ᵒ ♯ T δ))                ⩦⟨ cong-↓ᵒ k down-× ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S δ) ×ᵒ ↓ᵒ (suc k) (♯ T δ)))
                   ⩦⟨ cong-↓ᵒ k (cong-↓ᵒ (suc k) (cong-×ᵒ (≡ᵒ-refl refl) gT)) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S δ) ×ᵒ ↓ᵒ (suc k) (♯ T (↓ᵈ j x δ))))
                                                ⩦⟨ ≡ᵒ-sym (cong-↓ᵒ k down-×) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (♯ S δ ×ᵒ ♯ T (↓ᵈ j x δ)))
               ⩦⟨ lemma17ᵒ k ⟩ 
    ↓ᵒ k (♯ S δ ×ᵒ ♯ T (↓ᵈ j x δ))
               ⩦⟨ down-× ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S δ) ×ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ)))
               ⩦⟨ cong-↓ᵒ k (cong-×ᵒ gS (≡ᵒ-refl refl)) ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S (↓ᵈ j x δ)) ×ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ)))
               ⩦⟨ ≡ᵒ-sym down-× ⟩ 
    ↓ᵒ k (♯ S (↓ᵈ j x δ) ×ᵒ ♯ T (↓ᵈ j x δ))    ∎
... | Later | Now = λ δ j k k≤j →
    let gS = good-later (good S x) time-x1 δ j k k≤j in
    let gT = good-now (good T x) time-x2 δ j k k≤j in
    ↓ᵒ k (♯ S δ ×ᵒ ♯ T δ)                             ⩦⟨ ≡ᵒ-sym (lemma17ᵒ k) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (♯ S δ ×ᵒ ♯ T δ))                ⩦⟨ cong-↓ᵒ k down-× ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S δ) ×ᵒ ↓ᵒ (suc k) (♯ T δ)))
                   ⩦⟨ cong-↓ᵒ k (cong-↓ᵒ (suc k) (cong-×ᵒ gS (≡ᵒ-refl refl))) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S (↓ᵈ j x δ)) ×ᵒ ↓ᵒ (suc k) (♯ T δ)))
                                                ⩦⟨ ≡ᵒ-sym (cong-↓ᵒ k down-×) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (♯ S (↓ᵈ j x δ) ×ᵒ ♯ T δ))
               ⩦⟨ lemma17ᵒ k ⟩ 
    ↓ᵒ k (♯ S (↓ᵈ j x δ) ×ᵒ ♯ T δ)
               ⩦⟨ down-× ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S (↓ᵈ j x δ)) ×ᵒ ↓ᵒ k (♯ T δ))
               ⩦⟨ cong-↓ᵒ k (cong-×ᵒ (≡ᵒ-refl refl) gT) ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S (↓ᵈ j x δ)) ×ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ)))
               ⩦⟨ ≡ᵒ-sym down-× ⟩ 
    ↓ᵒ k (♯ S (↓ᵈ j x δ) ×ᵒ ♯ T (↓ᵈ j x δ))    ∎
... | Later | Later = λ δ j k k≤j →
    let gS = good-later (good S x) time-x1 δ j k k≤j in
    let gT = good-later (good T x) time-x2 δ j k k≤j in
    ↓ᵒ (suc k) (♯ S δ ×ᵒ ♯ T δ)                ⩦⟨ down-× ⟩ 
    ↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S δ) ×ᵒ ↓ᵒ (suc k) (♯ T δ))
                   ⩦⟨ cong-↓ᵒ (suc k) (cong-×ᵒ gS gT) ⟩ 
    ↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S (↓ᵈ j x δ))
                                  ×ᵒ ↓ᵒ (suc k) (♯ T (↓ᵈ j x δ)))
                                                ⩦⟨ ≡ᵒ-sym down-× ⟩ 
    ↓ᵒ (suc k) (♯ S (↓ᵈ j x δ) ×ᵒ ♯ T (↓ᵈ j x δ))   ∎

S ×ˢ T = record { ♯ = λ δ → ♯ S δ ×ᵒ ♯ T δ
                ; good = good-pair S T
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

good-sum : ∀{Γ}{Δ₁ Δ₂ : Times Γ}
   (S : Setˢ Γ Δ₁) (T : Setˢ Γ Δ₂)
   → good-fun (Δ₁ ∪ Δ₂) (λ δ → ♯ S δ ⊎ᵒ ♯ T δ)
good-sum {Γ}{Δ₁}{Δ₂} S T {A} x
    rewrite timeof-combine {Γ}{Δ₁}{Δ₂}{A}{x}
    with timeof x Δ₁ in time-x1 | timeof x Δ₂ in time-x2
... | Now | Now = λ δ j k k≤j →
    let gS = good-now (good S x) time-x1 δ j k k≤j in
    let gT = good-now (good T x) time-x2 δ j k k≤j in
    ↓ᵒ k (♯ S δ ⊎ᵒ ♯ T δ)                                         ⩦⟨ down-⊎ ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S δ) ⊎ᵒ ↓ᵒ k (♯ T δ))
                                     ⩦⟨ cong-↓ᵒ k (cong-⊎ᵒ gS (≡ᵒ-refl refl)) ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S (↓ᵈ j x δ)) ⊎ᵒ ↓ᵒ k (♯ T δ))
                                     ⩦⟨ cong-↓ᵒ k (cong-⊎ᵒ (≡ᵒ-refl refl) gT) ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S (↓ᵈ j x δ)) ⊎ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ)))   ⩦⟨ ≡ᵒ-sym down-⊎ ⟩
    ↓ᵒ k (♯ S (↓ᵈ j x δ) ⊎ᵒ ♯ T (↓ᵈ j x δ))  ∎
... | Now | Later = λ δ j k k≤j →
    let gS = good-now (good S x) time-x1 δ j k k≤j in
    let gT = good-later (good T x) time-x2 δ j k k≤j in
    ↓ᵒ k (♯ S δ ⊎ᵒ ♯ T δ)                             ⩦⟨ ≡ᵒ-sym (lemma17ᵒ k) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (♯ S δ ⊎ᵒ ♯ T δ))                ⩦⟨ cong-↓ᵒ k down-⊎ ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S δ) ⊎ᵒ ↓ᵒ (suc k) (♯ T δ)))
                   ⩦⟨ cong-↓ᵒ k (cong-↓ᵒ (suc k) (cong-⊎ᵒ (≡ᵒ-refl refl) gT)) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S δ) ⊎ᵒ ↓ᵒ (suc k) (♯ T (↓ᵈ j x δ))))
                                                ⩦⟨ ≡ᵒ-sym (cong-↓ᵒ k down-⊎) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (♯ S δ ⊎ᵒ ♯ T (↓ᵈ j x δ)))
               ⩦⟨ lemma17ᵒ k ⟩ 
    ↓ᵒ k (♯ S δ ⊎ᵒ ♯ T (↓ᵈ j x δ))
               ⩦⟨ down-⊎ ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S δ) ⊎ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ)))
               ⩦⟨ cong-↓ᵒ k (cong-⊎ᵒ gS (≡ᵒ-refl refl)) ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S (↓ᵈ j x δ)) ⊎ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ)))
               ⩦⟨ ≡ᵒ-sym down-⊎ ⟩ 
    ↓ᵒ k (♯ S (↓ᵈ j x δ) ⊎ᵒ ♯ T (↓ᵈ j x δ))    ∎
... | Later | Now = λ δ j k k≤j →
    let gS = good-later (good S x) time-x1 δ j k k≤j in
    let gT = good-now (good T x) time-x2 δ j k k≤j in
    ↓ᵒ k (♯ S δ ⊎ᵒ ♯ T δ)                             ⩦⟨ ≡ᵒ-sym (lemma17ᵒ k) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (♯ S δ ⊎ᵒ ♯ T δ))                ⩦⟨ cong-↓ᵒ k down-⊎ ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S δ) ⊎ᵒ ↓ᵒ (suc k) (♯ T δ)))
                   ⩦⟨ cong-↓ᵒ k (cong-↓ᵒ (suc k) (cong-⊎ᵒ gS (≡ᵒ-refl refl))) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S (↓ᵈ j x δ)) ⊎ᵒ ↓ᵒ (suc k) (♯ T δ)))
                                                ⩦⟨ ≡ᵒ-sym (cong-↓ᵒ k down-⊎) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (♯ S (↓ᵈ j x δ) ⊎ᵒ ♯ T δ))
               ⩦⟨ lemma17ᵒ k ⟩ 
    ↓ᵒ k (♯ S (↓ᵈ j x δ) ⊎ᵒ ♯ T δ)
               ⩦⟨ down-⊎ ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S (↓ᵈ j x δ)) ⊎ᵒ ↓ᵒ k (♯ T δ))
               ⩦⟨ cong-↓ᵒ k (cong-⊎ᵒ (≡ᵒ-refl refl) gT) ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S (↓ᵈ j x δ)) ⊎ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ)))
               ⩦⟨ ≡ᵒ-sym down-⊎ ⟩ 
    ↓ᵒ k (♯ S (↓ᵈ j x δ) ⊎ᵒ ♯ T (↓ᵈ j x δ))    ∎
... | Later | Later = λ δ j k k≤j →
    let gS = good-later (good S x) time-x1 δ j k k≤j in
    let gT = good-later (good T x) time-x2 δ j k k≤j in
    ↓ᵒ (suc k) (♯ S δ ⊎ᵒ ♯ T δ)                ⩦⟨ down-⊎ ⟩ 
    ↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S δ) ⊎ᵒ ↓ᵒ (suc k) (♯ T δ))
                   ⩦⟨ cong-↓ᵒ (suc k) (cong-⊎ᵒ gS gT) ⟩ 
    ↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S (↓ᵈ j x δ))
                                  ⊎ᵒ ↓ᵒ (suc k) (♯ T (↓ᵈ j x δ)))
                                                ⩦⟨ ≡ᵒ-sym down-⊎ ⟩ 
    ↓ᵒ (suc k) (♯ S (↓ᵈ j x δ) ⊎ᵒ ♯ T (↓ᵈ j x δ))   ∎

S ⊎ˢ T = record { ♯ = λ δ → ♯ S δ ⊎ᵒ ♯ T δ
                ; good = good-sum S T
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

good-imp : ∀{Γ}{Δ₁ Δ₂ : Times Γ}
   (S : Setˢ Γ Δ₁) (T : Setˢ Γ Δ₂)
   → good-fun (Δ₁ ∪ Δ₂) (λ δ → ♯ S δ →ᵒ ♯ T δ)
good-imp {Γ}{Δ₁}{Δ₂} S T {A} x
    rewrite timeof-combine {Γ}{Δ₁}{Δ₂}{A}{x}
    with timeof x Δ₁ in time-x1 | timeof x Δ₂ in time-x2
... | Now | Now = λ δ j k k≤j →
    let gS = good-now (good S x) time-x1 δ j k k≤j in
    let gT = good-now (good T x) time-x2 δ j k k≤j in
    ↓ᵒ k (♯ S δ →ᵒ ♯ T δ)                         ⩦⟨ down-→{♯ S δ}{♯ T δ} ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S δ) →ᵒ ↓ᵒ k (♯ T δ))
                                     ⩦⟨ cong-↓ᵒ k (cong-→ gS (≡ᵒ-refl refl)) ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S (↓ᵈ j x δ)) →ᵒ ↓ᵒ k (♯ T δ))
                       ⩦⟨ cong-↓ᵒ k (cong-→{↓ᵒ k (♯ S (↓ᵈ j x δ))}
                                           {↓ᵒ k (♯ S (↓ᵈ j x δ))}
                                           {↓ᵒ k (♯ T δ)}
                                           {↓ᵒ k (♯ T (↓ᵈ j x δ))}
                                    (≡ᵒ-refl refl) gT) ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S (↓ᵈ j x δ)) →ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ)))
                          ⩦⟨ ≡ᵒ-sym (down-→{♯ S (↓ᵈ j x δ)}{♯ T (↓ᵈ j x δ)}) ⟩
    ↓ᵒ k (♯ S (↓ᵈ j x δ) →ᵒ ♯ T (↓ᵈ j x δ))  ∎
... | Now | Later = λ δ j k k≤j →
    let gS = good-now (good S x) time-x1 δ j k k≤j in
    let gT = good-later (good T x) time-x2 δ j k k≤j in
    ↓ᵒ k (♯ S δ →ᵒ ♯ T δ)                             ⩦⟨ ≡ᵒ-sym (lemma17ᵒ k) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (♯ S δ →ᵒ ♯ T δ))   ⩦⟨ cong-↓ᵒ k (down-→{♯ S δ}{♯ T δ}) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S δ) →ᵒ ↓ᵒ (suc k) (♯ T δ)))
         ⩦⟨ cong-↓ᵒ k (cong-↓ᵒ (suc k)
             (cong-→{↓ᵒ (suc k) (♯ S δ)}{↓ᵒ (suc k) (♯ S δ)}
                     {↓ᵒ (suc k) (♯ T δ)}{ ↓ᵒ (suc k) (♯ T (↓ᵈ j x δ))}
                     (≡ᵒ-refl refl) gT)) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S δ) →ᵒ ↓ᵒ (suc k) (♯ T (↓ᵈ j x δ))))
                       ⩦⟨ ≡ᵒ-sym (cong-↓ᵒ k (down-→{♯ S δ}{♯ T (↓ᵈ j x δ)})) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (♯ S δ →ᵒ ♯ T (↓ᵈ j x δ)))
               ⩦⟨ lemma17ᵒ k ⟩ 
    ↓ᵒ k (♯ S δ →ᵒ ♯ T (↓ᵈ j x δ))
               ⩦⟨ down-→{♯ S δ}{♯ T (↓ᵈ j x δ)} ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S δ) →ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ)))
               ⩦⟨ cong-↓ᵒ k (cong-→ gS (≡ᵒ-refl refl)) ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S (↓ᵈ j x δ)) →ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ)))
               ⩦⟨ ≡ᵒ-sym (down-→{♯ S (↓ᵈ j x δ)}{♯ T (↓ᵈ j x δ)}) ⟩ 
    ↓ᵒ k (♯ S (↓ᵈ j x δ) →ᵒ ♯ T (↓ᵈ j x δ))    ∎
... | Later | Now = λ δ j k k≤j →
    let gS = good-later (good S x) time-x1 δ j k k≤j in
    let gT = good-now (good T x) time-x2 δ j k k≤j in
    ↓ᵒ k (♯ S δ →ᵒ ♯ T δ)                             ⩦⟨ ≡ᵒ-sym (lemma17ᵒ k) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (♯ S δ →ᵒ ♯ T δ))   ⩦⟨ cong-↓ᵒ k (down-→{♯ S δ}{♯ T δ}) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S δ) →ᵒ ↓ᵒ (suc k) (♯ T δ)))
                   ⩦⟨ cong-↓ᵒ k (cong-↓ᵒ (suc k) (cong-→ gS (≡ᵒ-refl refl))) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S (↓ᵈ j x δ)) →ᵒ ↓ᵒ (suc k) (♯ T δ)))
                       ⩦⟨ ≡ᵒ-sym (cong-↓ᵒ k (down-→{♯ S (↓ᵈ j x δ)}{♯ T δ})) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (♯ S (↓ᵈ j x δ) →ᵒ ♯ T δ))
               ⩦⟨ lemma17ᵒ k ⟩ 
    ↓ᵒ k (♯ S (↓ᵈ j x δ) →ᵒ ♯ T δ)
               ⩦⟨ down-→{♯ S (↓ᵈ j x δ)}{♯ T δ} ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S (↓ᵈ j x δ)) →ᵒ ↓ᵒ k (♯ T δ))
               ⩦⟨ cong-↓ᵒ k (cong-→{↓ᵒ k (♯ S (↓ᵈ j x δ))}
                     {↓ᵒ k (♯ S (↓ᵈ j x δ))}
                     {↓ᵒ k (♯ T δ)}{↓ᵒ k (♯ T (↓ᵈ j x δ))} (≡ᵒ-refl refl) gT) ⟩ 
    ↓ᵒ k (↓ᵒ k (♯ S (↓ᵈ j x δ)) →ᵒ ↓ᵒ k (♯ T (↓ᵈ j x δ)))
               ⩦⟨ ≡ᵒ-sym (down-→{♯ S (↓ᵈ j x δ)}{♯ T (↓ᵈ j x δ)}) ⟩ 
    ↓ᵒ k (♯ S (↓ᵈ j x δ) →ᵒ ♯ T (↓ᵈ j x δ))    ∎
... | Later | Later = λ δ j k k≤j →
    let gS = good-later (good S x) time-x1 δ j k k≤j in
    let gT = good-later (good T x) time-x2 δ j k k≤j in
    ↓ᵒ (suc k) (♯ S δ →ᵒ ♯ T δ)                ⩦⟨ down-→{♯ S δ}{♯ T δ} ⟩ 
    ↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S δ) →ᵒ ↓ᵒ (suc k) (♯ T δ))
                   ⩦⟨ cong-↓ᵒ (suc k) (cong-→ gS gT) ⟩ 
    ↓ᵒ (suc k) (↓ᵒ (suc k) (♯ S (↓ᵈ j x δ))
                                  →ᵒ ↓ᵒ (suc k) (♯ T (↓ᵈ j x δ)))
                         ⩦⟨ ≡ᵒ-sym (down-→{♯ S (↓ᵈ j x δ)}{♯ T (↓ᵈ j x δ)}) ⟩ 
    ↓ᵒ (suc k) (♯ S (↓ᵈ j x δ) →ᵒ ♯ T (↓ᵈ j x δ))   ∎

S →ˢ T = record { ♯ = λ δ → ♯ S δ →ᵒ ♯ T δ
                ; good = good-imp S T
                ; congr = λ d=d′ → cong-→ (congr S d=d′) (congr T d=d′)
                }
\end{code}

\subsection{Approximation Operator}

\begin{code}
abstract
  permute-↓ : ∀{S : Setᵒ}{j}{k}
     → ↓ᵒ k (↓ᵒ j S) ≡ᵒ ↓ᵒ j (↓ᵒ k S)
  permute-↓ {S} {j} {k} zero = (λ x → tt) , (λ x → tt)
  permute-↓ {S} {j} {k} (suc i) =
    (λ {(x , (y , z)) → y , x , z}) , λ {(x , (y , z)) → y , x , z}

good-↓ : ∀{Γ}{Δ : Times Γ}{i}
   (S : Setˢ Γ Δ)
   → good-fun Δ (λ δ → ↓ᵒ i (♯ S δ))
good-↓ {Γ}{Δ}{i} S {A} x
    with timeof x Δ in time-x
... | Now = λ δ j k k≤j → 
    let gS = good-now (good S x) time-x δ j k k≤j in
    ↓ᵒ k (↓ᵒ i (♯ S δ))              ⩦⟨ permute-↓  ⟩ 
    ↓ᵒ i (↓ᵒ k (♯ S δ))              ⩦⟨ cong-↓ᵒ i gS ⟩ 
    ↓ᵒ i (↓ᵒ k (♯ S (↓ᵈ j x δ)))     ⩦⟨ permute-↓ ⟩
    ↓ᵒ k (↓ᵒ i (♯ S (↓ᵈ j x δ)))  ∎
... | Later = λ δ j k k≤j →
    let gS = good-later (good S x) time-x δ j k k≤j in
    ↓ᵒ (suc k) (↓ᵒ i (♯ S δ))              ⩦⟨ permute-↓  ⟩ 
    ↓ᵒ i (↓ᵒ (suc k) (♯ S δ))              ⩦⟨ cong-↓ᵒ i gS ⟩ 
    ↓ᵒ i (↓ᵒ (suc k) (♯ S (↓ᵈ j x δ)))     ⩦⟨ permute-↓ ⟩
    ↓ᵒ (suc k) (↓ᵒ i (♯ S (↓ᵈ j x δ)))  ∎

↓ˢ : ∀{Γ}{Δ : Times Γ}
   → ℕ
   → Setˢ Γ Δ
     ----------
   → Setˢ Γ Δ
↓ˢ k S = record { ♯ = λ δ → ↓ᵒ k (♯ S δ)
                ; good = good-↓ S
                ; congr = λ d=d′ → cong-↓ᵒ k (congr S d=d′)}

⇓ˢ : ℕ → ∀{Γ} → RecEnv Γ → RecEnv Γ
⇓ˢ k {[]} ttᵖ = ttᵖ
⇓ˢ k {A ∷ Γ} (P , δ) = ↓ᵖ k P , ⇓ˢ k δ

{---------------------- Predicate Application ----------------------------}

good-apply : ∀{Γ}{Δ : Times Γ}{A}
   (S : Setˢ (A ∷ Γ) (cons Later Δ))
   (P : A → Setˢ Γ Δ)
   → good-fun Δ (λ δ → ♯ S ((λ a → ♯ (P a) δ) , δ))
good-apply {Γ}{Δ}{A} S P x
   with timeof x Δ in time-x
... | Now = λ δ j k k≤j →
    let gSz = ((good S) zeroˢ) ((λ a → ♯ (P a) δ) , δ) j k k≤j in
    let gSz2 = ((good S) zeroˢ) ((λ a → ♯ (P a) (↓ᵈ j x δ)) , (↓ᵈ j x δ))
                   j k k≤j in
    let gSsx = good-now{Δ = cons Now Δ} ((good S) (sucˢ x)) time-x
                 ((λ a → ↓ᵒ j (♯ (P a) δ)) , δ) j k k≤j in

    let EQ : ((λ a → ↓ᵒ j (♯ (P a) δ)) , ↓ᵈ j x δ)
              ≡ᵈ ((λ a → ↓ᵒ j  (♯ (P a) (↓ᵈ j x δ))) , ↓ᵈ j x δ)
        EQ = (λ a → good-now (good (P a) x) time-x δ j j ≤-refl) , ≡ᵈ-refl in
    
    ↓ᵒ k (♯ S ((λ a → ♯ (P a) δ) , δ))               ⩦⟨ ≡ᵒ-sym (lemma17ᵒ k) ⟩
    ↓ᵒ k (↓ᵒ (suc k) (♯ S ((λ a → ♯ (P a) δ) , δ)))
      ⩦⟨ cong-↓ᵒ k gSz ⟩
    ↓ᵒ k (↓ᵒ (suc k) (♯ S ((λ a → ↓ᵒ j (♯ (P a) δ)) , δ)))
      ⩦⟨ lemma17ᵒ k ⟩
    ↓ᵒ k (♯ S ((λ a → ↓ᵒ j (♯ (P a) δ)) , δ))
      ⩦⟨ gSsx ⟩
    ↓ᵒ k (♯ S ((λ a → ↓ᵒ j (♯ (P a) δ)) , ↓ᵈ j x δ))
      ⩦⟨ cong-↓ᵒ k (congr S EQ) ⟩
    ↓ᵒ k (♯ S ((λ a → ↓ᵒ j (♯ (P a) (↓ᵈ j x δ))) , ↓ᵈ j x δ))
                        ⩦⟨ ≡ᵒ-sym (lemma17ᵒ k) ⟩
    ↓ᵒ k (↓ᵒ (suc k) (♯ S ((λ a → ↓ᵒ j (♯ (P a) (↓ᵈ j x δ))) , ↓ᵈ j x δ)))
      ⩦⟨ cong-↓ᵒ k (≡ᵒ-sym gSz2) ⟩
    ↓ᵒ k (↓ᵒ (suc k) (♯ S ((λ a → ♯ (P a) (↓ᵈ j x δ)) , ↓ᵈ j x δ)))
      ⩦⟨ lemma17ᵒ k ⟩
    ↓ᵒ k (♯ S ((λ a → ♯ (P a) (↓ᵈ j x δ)) , ↓ᵈ j x δ))   ∎

... | Later = λ δ j k k≤j →
    let gSz = ((good S) zeroˢ) ((λ a → ♯ (P a) δ) , δ) (suc j) k
                    (≤-trans k≤j (n≤1+n _)) in
    let gSz2 = ((good S) zeroˢ) (((λ a → ♯ (P a) (↓ᵈ j x δ))) , δ) (suc j) k
                    (≤-trans k≤j (n≤1+n _)) in
    let EQ : ((λ a → ↓ᵒ (suc j) (♯ (P a) δ)) , δ)
              ≡ᵈ ((λ a → ↓ᵒ (suc j)  (♯ (P a) (↓ᵈ j x δ))) , δ)
        EQ = (λ a → good-later (good (P a) x) time-x δ j j ≤-refl) , ≡ᵈ-refl in
    let gSsx = good-later{Δ = cons Now Δ} ((good S) (sucˢ x)) time-x
                 ((λ a → ♯ (P a) (↓ᵈ j x δ)) , δ) j k k≤j in
    ↓ᵒ (suc k) (♯ S ((λ a → ♯ (P a) δ) , δ)) 
      ⩦⟨ gSz ⟩
    ↓ᵒ (suc k) (♯ S (↓ᵖ (suc j) (λ a → ♯ (P a) δ) , δ)) 
      ⩦⟨ cong-↓ᵒ (suc k) (congr S EQ) ⟩
    ↓ᵒ (suc k) (♯ S (↓ᵖ (suc j) (λ a → ♯ (P a) (↓ᵈ j x δ)) , δ)) 
      ⩦⟨ ≡ᵒ-sym gSz2 ⟩
    ↓ᵒ (suc k) (♯ S ((λ a → ♯ (P a) (↓ᵈ j x δ)) , δ)) 
      ⩦⟨ gSsx ⟩
    ↓ᵒ (suc k) (♯ S ((λ a → ♯ (P a) (↓ᵈ j x δ)) , ↓ᵈ j x δ))  ∎

applyˢ : ∀ {Γ}{Δ : Times Γ}{A}
   (S : Setˢ (A ∷ Γ) (cons Later Δ))
   (P : A → Setˢ Γ Δ)
   → Setˢ Γ Δ   
applyˢ S P =
  record { ♯ = λ δ → (♯ S) ((λ a → ♯ (P a) δ) , δ)
         ; good = good-apply S P
         ; congr = λ d=d′ → congr S ((λ a → congr (P a) d=d′) , d=d′)
         }
\end{code}


\subsection{Equivalence for Open Step-Indexed Formulas}

\begin{code}
abstract
  infix 2 _≡ˢ_
  _≡ˢ_ : ∀{Γ}{Δ : Times Γ} → Setˢ Γ Δ → Setˢ Γ Δ → Set₁
  S ≡ˢ T = ∀ δ → ♯ S δ ≡ᵒ ♯ T δ

  ≡ˢ-intro : ∀{Γ}{Δ : Times Γ}{S T : Setˢ Γ Δ}
    → (∀ δ → ♯ S δ ≡ᵒ ♯ T δ)
      ---------------------
    → S ≡ˢ T
  ≡ˢ-intro S=T eq δ = S=T eq δ

  ≡ˢ-elim : ∀{Γ}{Δ : Times Γ}{S T : Setˢ Γ Δ}
    → S ≡ˢ T
      ---------------------
    → (∀ δ → ♯ S δ ≡ᵒ ♯ T δ)
  ≡ˢ-elim S=T δ = S=T δ

  ≡ˢ-refl : ∀{Γ}{Δ : Times Γ}{S T : Setˢ Γ Δ}
    → S ≡ T
    → S ≡ˢ T
  ≡ˢ-refl{S = S}{T} refl δ = ≡ᵒ-refl{♯ S δ}{♯ T δ} refl

  ≡ˢ-sym : ∀{Γ}{Δ : Times Γ}{S T : Setˢ Γ Δ}
    → S ≡ˢ T
    → T ≡ˢ S
  ≡ˢ-sym{S = S}{T} ST δ = ≡ᵒ-sym{♯ S δ}{♯ T δ} (ST δ)

  ≡ˢ-trans : ∀{Γ}{Δ : Times Γ}{S T R : Setˢ Γ Δ}
    → S ≡ˢ T
    → T ≡ˢ R
    → S ≡ˢ R
  ≡ˢ-trans{S = S}{T}{R} ST TR δ = ≡ᵒ-trans{♯ S δ}{♯ T δ}{♯ R δ} (ST δ) (TR δ)
  
instance
  SIL-Eqˢ : ∀{Γ}{Δ : Times Γ} → EquivalenceRelation (Setˢ Γ Δ)
  SIL-Eqˢ = record { _⩦_ = _≡ˢ_ ; ⩦-refl = ≡ˢ-refl
                   ; ⩦-sym = ≡ˢ-sym ; ⩦-trans = ≡ˢ-trans }
\end{code}

\section{Fixpoint Theorem}

\begin{code}
abstract
  equiv-downᵒ : ∀{S T : Setᵒ}
    → (∀ j → ↓ᵒ j S ≡ᵒ ↓ᵒ j T)
    → S ≡ᵒ T
  equiv-downᵒ {S} {T} ↓S=↓T zero = (λ _ → tz T) , (λ _ → tz S)
  equiv-downᵒ {S} {T} ↓S=↓T (suc k) =
    (λ Ssk → proj₂ (proj₁ (↓S=↓T (suc (suc k)) (suc k)) (≤-refl , Ssk)))
    ,
    λ Δk → proj₂ (proj₂ (↓S=↓T (suc (suc k)) (suc k)) (≤-refl , Δk))
  
  equiv-downˢ : ∀{Γ}{Δ : Times Γ}{S T : Setˢ Γ Δ}
    → (∀ j → ↓ˢ j S ≡ˢ ↓ˢ j T)
    → S ≡ˢ T
  equiv-downˢ {Γ}{Δ}{S}{T} ↓S=↓T δ =
     equiv-downᵒ{♯ S δ}{♯ T δ} λ j → (↓S=↓T j) δ

nonexpansive : ∀{A} (F : Predᵒ A → Predᵒ A) (a : A) → Set₁
nonexpansive F a = ∀ P k → ↓ᵒ k (F P a) ≡ᵒ ↓ᵒ k (F (↓ᵖ k P) a)

nonexpansive′ : ∀{Γ}{A}{Δ : Times Γ}{δ : RecEnv Γ}
  (F : A → Setˢ (A ∷ Γ) (cons Later Δ)) (a : A) → Set₁
nonexpansive′{Γ}{A}{Δ}{δ} F a =
  ∀ P k → ↓ᵒ k (♯ (F a) (P , δ)) ≡ᵒ ↓ᵒ k (♯ (F a) ((↓ᵖ k P) , δ))

{- sanity check -}
cont-toFun : ∀{Γ}{A}{Δ : Times Γ}{δ : RecEnv Γ}
  → (F : A → Setˢ (A ∷ Γ) (cons Later Δ))
  → (a : A)
  → nonexpansive′{δ = δ} F a
  → nonexpansive (toFun δ F) a
cont-toFun{Γ}{A}{Δ}{δ} F a cont′ = cont′

wellfounded : ∀{A} (F : Predᵒ A → Predᵒ A) (a : A) → Set₁
wellfounded F a = ∀ P k → ↓ᵒ (suc k) (F P a) ≡ᵒ ↓ᵒ (suc k) (F (↓ᵖ k P) a)

wellfounded′ : ∀{Γ}{A}{Δ : Times Γ}{δ : RecEnv Γ}
  (F : A → Setˢ (A ∷ Γ) (cons Later Δ)) (a : A) → Set₁
wellfounded′{Γ}{A}{Δ}{δ} F a =
  ∀ P k → ↓ᵒ (suc k) (♯ (F a) (P , δ))
       ≡ᵒ ↓ᵒ (suc k) (♯ (F a) ((↓ᵖ k P) , δ))

{- sanity check -}
WF-toFun : ∀{Γ}{A}{Δ : Times Γ}{δ : RecEnv Γ}
  → (F : A → Setˢ (A ∷ Γ) (cons Later Δ))
  → (a : A)
  → wellfounded′{δ = δ} F a
  → wellfounded (toFun δ F) a
WF-toFun{Γ}{A}{Δ}{δ} F a cont′ = cont′

lemma19 : ∀{Γ}{Δ : Times Γ}{A} (F : A → Setˢ (A ∷ Γ) (cons Later Δ)) (a : A) (j : ℕ)
   → ↓ˢ j (μˢ F a) ≡ˢ ↓ˢ j (applyˢ (F a) (μˢ F))
lemma19{Γ}{Δ}{A} F a j = ≡ˢ-intro (lemma19a F a j)

fixpointˢ : ∀{Γ}{Δ : Times Γ}{A} (F : A → Setˢ (A ∷ Γ) (cons Later Δ)) (a : A)
   → μˢ F a ≡ˢ applyˢ (F a) (μˢ F)
fixpointˢ F a = equiv-downˢ (lemma19 F a)

μᵒ : ∀{A}
   → (A → Setˢ (A ∷ []) (cons Later ∅))
     ----------------------------------
   → (A → Setᵒ)
μᵒ {A} P = muᵒ P ttᵖ

fixpointᵒ : ∀{A} (P : A → Setˢ (A ∷ []) (cons Later ∅)) (a : A)
   → μᵒ P a ≡ᵒ ♯ (P a) (μᵒ P , ttᵖ)
fixpointᵒ P a = ≡ˢ-elim (fixpointˢ P a) ttᵖ

fixpoint-step : ∀{A} (P : A → Setˢ (A ∷ []) (cons Later ∅)) (a : A) (k : ℕ)
   → (#(μᵒ P a) k) ⇔ #(♯ (P a) (μᵒ P , ttᵖ)) k
fixpoint-step P a k = ≡ᵒ-elim{k = k} (fixpointᵒ P a)
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
       -----------------------
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
