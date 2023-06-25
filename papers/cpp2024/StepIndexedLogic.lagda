\begin{comment}
\begin{code}
module cpp2024.StepIndexedLogic where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat
   using (ℕ; zero; suc; _≤_; _<_; _+_; _∸_; z≤n; s≤s; _≤′_; ≤′-step)
open import Data.Nat.Properties
   using (≤-refl; ≤-antisym; ≤-trans; ≤-step; ≤⇒≤′; ≤′⇒≤; n≤1+n; <⇒≤)
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


\section{Step-Indexed First-Order Logic}

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
    # : (ℕ → Set)
    down : downClosed #
    tz : # 0
open Setᵒ public
\end{code}
Let $P, Q, R$ range over step-indexed propositions.
\begin{code}
variable P Q R : Setᵒ
\end{code}
Let $p, q$ range over (regular) propositions.
\begin{code}
variable p q : Set
\end{code}

The false formula for SIL is embedded in Agda by defining an instance
of this record type, with the representation function mapping zero
to true and every other natural number to false. The proofs of
downward-closedness and true-at-zero are straightforward.
The embedding of the true formula into Agda is even more straightforward.
\begin{code}
⊥ᵒ : Setᵒ
⊥ᵒ = record { # = λ { zero → ⊤ ; (suc k) → ⊥}
            ; down = λ { zero x .zero z≤n → tt} ; tz = tt }

⊤ᵒ : Setᵒ
⊤ᵒ = record { # = λ k → ⊤
            ; down = λ n _ k _ → tt ; tz = tt }
\end{code}

Next we define conjunction and disjunction in SIL. Given two
step-indexed propositions $P$ and $Q$, their conjunction is the
function that takes the conjunction of applying them to the step
index. The proofs of downward-closedness and true-at-zero are
straightforward, relying on the proofs of these properties for $P$ and $Q$.
The story for disjunction is similar.
\begin{code}
_×ᵒ_ : Setᵒ → Setᵒ → Setᵒ
P ×ᵒ Q = record { # = λ k → # P k × # Q k
                ; down = λ k (Pk , Qk) j j≤k →
                          (down P k Pk j j≤k) , (down Q k Qk j j≤k)
                ; tz = (tz P) , (tz Q) }

_⊎ᵒ_ : Setᵒ → Setᵒ → Setᵒ
P ⊎ᵒ Q = record { # = λ k → # P k ⊎ # Q k
                ; down = λ { k (inj₁ Pk) j j≤k → inj₁ (down P k Pk j j≤k)
                           ; k (inj₂ Qk) j j≤k → inj₂ (down Q k Qk j j≤k)}
                ; tz = inj₁ (tz P) }
\end{code}

The definition of impliciation is more interesting.  The following is
a naive first attempt, in which we following the same pattern as for
conjuction and disjunction, by saying that the meaning of $P$ implies
$Q$ at index $k$ is that $P$ at $k$ implies $Q$ at $k$. We run intro
trouble proving that this is downward closed. We are given that $P$ at
$j$ for some $j \leq k$, but we have no way to prove that $Q$ at $j$.

\begin{code}
_→n_ : Setᵒ → Setᵒ → Setᵒ
P →n Q = record { # = λ k → # P k → # Q k
                ; down = λ k Pk→Qk j j≤k Pj → impossible
                ; tz = λ Pz → tz Q }
\end{code}

The standard workaround is to force implication to be downward closed
by definition. We define $P$ implies $Q$ at $k$ to mean that for all
$j \leq k$, $P$ at $j$ implies $Q$ at $j$.

\begin{code}
_→ᵒ_ : Setᵒ → Setᵒ → Setᵒ
P →ᵒ Q = record { # = λ k → ∀ j → j ≤ k → # P j → # Q j
                ; down = λ k ∀j≤k→Pj→Qj j j≤k i i≤j Pi →
                     ∀j≤k→Pj→Qj i (≤-trans i≤j j≤k) Pi
                ; tz = λ { .zero z≤n _ → tz Q} }
\end{code}

Next we come to the important ``later`` operator, written $▷ᵒ P$.  Of
course, at zero it is true. For any other index of the form
$\mathsf{suc}\app k$, $▷ᵒ P$ means $P$ at $k$, that is, subtract
one from the step index.

\begin{code}
▷ᵒ_ : Setᵒ → Setᵒ
▷ᵒ P = record { # = λ { zero → ⊤ ; (suc k) → # P k }
              ; down = λ { zero ▷Pn .zero z≤n → tt
                         ; (suc n) ▷Pn .zero z≤n → tt
                         ; (suc n) ▷Pn (suc k) (s≤s k≤n) → down P n ▷Pn k k≤n}
              ; tz = tt }
\end{code}

A step-indexed logic such as LSLR is typically specialized to include
atomic formulas to express properties of programs in a particular
language. Here instead we simply allow arbitrary Agda propositions to
be included in a step-indexed proposition by way of the following
operator. So, given a proposition $P$, the formula $Pᵒ$ is true at
zero and everywhere else it is equivalent to $P$.

\begin{code}
_ᵒ : Set → Setᵒ
P ᵒ = record { # = λ { zero → ⊤ ; (suc k) → P }
             ; down = λ { k Pk zero j≤k → tt
                        ; (suc k) Pk (suc j) j≤k → Pk}
             ; tz = tt }
\end{code}

It remains to define the forall and exists quantifiers of SIL.  The
main idea is that we use Agda functions and variables to represent
quantification in SIL, as one would do in higher-order abstract
syntax. 

Let $A,B,C$ range over Agda types (element of \textsf{Set}).
\begin{code}
variable
  A B C : Set
\end{code}
We define a step-indexed predicate over type $A$ to be a function from
$A$ to $Setᵒ$.
\begin{code}
Predᵒ : Set → Set₁
Predᵒ A = A → Setᵒ
\end{code}

\noindent The forall quantifier maps a step-indexed predicate to $Setᵒ$.

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

The treatment of the exists quantifier is similar, except that to
obtain the true-at-zero property we require that the type $A$ be
inhabited. We do not wish this requirement to clutter every use of the
exists quantifier, so we use Agda's support for instance arguments
(think type classes). So we define the following record type and use
it as an implicit instance argument in the definition of the exists
quantifier.

\begin{code}
record Inhabited (A : Set) : Set where
  field
    elt : A
open Inhabited {{...}} public
\end{code}

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


\section{Equivalence for Step-Indexed Propositions}

We define equivalence of step-indexed propositions $P$ and $Q$ to be
that for any step $k$, $P$ at $k$ is true if and only if $Q$ at $k$ is
true. This is of course an equivalence relation (the proofs are in the
Appendix), and we make use of a library named
\textsf{EquivalenceRelation} to provide nice syntax for equational
reasoning.

\begin{code}
abstract
  infix 2 _≡ᵒ_
  _≡ᵒ_ : Setᵒ → Setᵒ → Set
  P ≡ᵒ Q = ∀ k → # P k ⇔ # Q k

  ≡ᵒ-refl : P ≡ Q → P ≡ᵒ Q
  ≡ᵒ-sym : P ≡ᵒ Q → Q ≡ᵒ P
  ≡ᵒ-trans : P ≡ᵒ Q → Q ≡ᵒ R → P ≡ᵒ R

instance
  SIL-Eqᵒ : EquivalenceRelation Setᵒ
  SIL-Eqᵒ = record { _⩦_ = _≡ᵒ_ ; ⩦-refl = ≡ᵒ-refl ; ⩦-sym = ≡ᵒ-sym ; ⩦-trans = ≡ᵒ-trans }
\end{code}

\section{Recursive Predicates and Relations}
\label{sec:rec-pred}

Our goal is to define an operator for recursive predicates and relations
with syntax that is something like $μᵒ x. R$, where $x$ is the name of the
recursive relation and $R$ is the definition of the relation, which
can refer to $x$. We shall prove a fixpoint theorem which states that
the recursive predicate is equal to its unfolding, something like the
following.
\[
  (μᵒ x. R) \app δ \app a ≡ᵒ R \app δ(x:= μᵒ x. R) \app a
\]
where $δ$ is an environment mapping variables to predicates.

\subsection{Review of the Fixpoint Theorem of Appel and McAllester}

Our proof of this fixpoint theorem is inspired by the fixpoint theorem
of \citet{Appel:2001aa}. In that work, \citet{Appel:2001aa} use
step-indexing to give a semantic definition of recursive types. Their
fixpoint theorem proves that a recursive type is equal to its unfolding.
They define a (semantic) type $\tau$ to be a relation between step indexes and
syntactic values. They do not define a syntax for types, but instead
define operators for constructing semantic types as follows.
\begin{align*}
  ⊥ &= \{ \} \\
  ⊤ &= \{ ⟨k,v⟩ \mid k ∈ ℕ\} \\
  \mathbf{int} &= \{⟨k,n⟩ \mid k ∈ ℕ, n ∈ ℤ \}\\
  τ₁ × τ₂ &= \{ ⟨k,(v₁,v₂)⟩ \mid ∀j<k. ⟨j,v₁⟩∈τ₁, ⟨j,v₂⟩∈τ₂ \} \\
  τ₁ → τ₂ &= \{ ⟨k,λx.e⟩ \mid ∀j<k.∀v. ⟨j,v⟩∈τ₁ ⇒ e[v/x] :ⱼ τ₂ \} \\
  μ F &= \{ ⟨k,v⟩ \mid ⟨k,v⟩ ∈ F^{k\plus 1}(⊥) \}
    & \text{if } F : \tau \to \tau'
\end{align*}
Their fixpoint theorem says that for any well founded $F$,
\[
  μ F = F(μF)
\]
A well founded function $F$ on types is
one in which each pair in the output $⟨k,v⟩$ only depends
on later pairs in the input, that is, pairs of the form $⟨j,v′⟩$
where $j < k$. \citet{Appel:2001aa} characterize this dependency
with the help of the $k$-approximation function:
\[
  \kapprox(k,τ) = \{ ⟨j,v⟩ \mid j < k, ⟨j,v⟩ ∈ τ\} 
\]
They define a \emph{well founded} function $F$ to be one that
satisfies the following equation.
\[
  \kapprox(k \plus 1, F(τ)) = \kapprox(k \plus 1, F(\kapprox(k,τ)))
\]

Functions over semantic types are not always well founded.  For
example, the identity function $λα.α$ is not well founded, so one
cannot apply the fixpoint theorem to the recursive type $μ(λα.α)$
(which corresponds to the syntactic type $μα.α$).
On the other hand, the function
$λα.α×α$ is well founded because of the strict less-than in the
definition of the $×$ operator. So the fixpont theorem applies to
$μ(λα.α×α)$.  In general, a function built from the type operators is
well founded so long as the recursive $α$ only appears underneath a
type constructor such as $×$ or $→$. \citet{Appel:2001aa} prove this
fact, which relies on the auxilliary notion of a nonexpansive
function. In such a function, the output can depend on pairs at the
current step index as well as later ones. So a \emph{nonexpansive}
function satisfies the following equation.
\[
  \kapprox(k, F(τ)) = \kapprox(k, F(\kapprox(k,τ)))
\]
For example, $λα.α$ is nonexpansive and so is $λα.\mathbf{int}$.
\citet{Appel:2001aa} then prove lemmas about the type constructors.
For example, regarding products, they prove that if $F$ and $G$
are nonexpansive functions, then so is $λ α. (F α) × (G α)$.

It is worth noting that \citet{Appel:2001aa} neglect to prove such 
lemmas for the $μ$ operator itself. For example, given $F : τ₁ → τ₂ → τ₃$
that is nonexpansive in its first parameter and well founded in
its second, then $λ α. μ (F α)$ is nonexpansive.
On the other hand, if $F$ is well founded in both parameters,
then $λ α. μ (F α)$ is well founded. We shall return to this point later.

\subsection{Step-Indexed Logic with Recursive Predicates}

Comparing the type operators of \citet{Appel:2001aa} to the logic
operators of SIL, there are striking similarities. The function type
operator is quite similar to implication, although one difference is
that the function type operator uses strict less-than whereas
implication uses non-strict less-than. The logic introduces the
``later`` operator, whereas the type operators essentially bake the
later operator into the type operators through their use of strict
less-than.

Our definition of recursive predicates will be similar to the
recursive type of \citet{Appel:2001aa} in that we shall define the
meaning of a recursive predicate by iteration.  On the other hand, we
do not want a fixpoint theorem that requires the user of the logic to
provide a proof that a particular proposition is well
founded. Instead, we shall introduce a type system for propositions
that ensure that $μ$ is only applied to well founded propositions, and
that the proof of well foundedness is provided by our logic operators,
not by the user of the logic.

We shall require that a recursive predicate is only used underneath at
least one ``later'' operator. To enforce this restriction, we use an
explicit representation for variables (unlike the situation for forall
and exists quantifiers). We choose de Bruijn indices that are well
typed. That is, the type of the variable specifies the input type of
the predicate.  (For relations, the input type is a product.)

\begin{code}
Context : Set₁
Context = List Set
variable Γ : Context

data _∋_ : Context → Set → Set₁ where
  zeroˢ : (A ∷ Γ) ∋ A
  sucˢ : Γ ∋ B → (A ∷ Γ) ∋ B
variable x y z : Γ ∋ A
\end{code}

These indices are used to index into a tuple of recursive
predicates. The following is the type for such a tuple, with one
predicate for each variable in the context.\footnote{$\mathsf{top}ᵖ$
is how to say ``true`` in $\mathsf{Set}₁$.}

\begin{code}
RecEnv : Context → Set₁
RecEnv [] = topᵖ 
RecEnv (A ∷ Γ) = (Predᵒ A) × RecEnv Γ
\end{code}

We refer to a function of type $\mathsf{RecEnv}\app Γ → \mathsf{Set}ᵒ$ as a
\emph{functional}.

To keep track of whether a variable has been used inside or outside of
a later operator, we introduce a notion of time and we introduce a
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

We shall define another record type, \textsf{Set}$^s$ for step-indexed
propositions that may contain free variables.
\begin{code}
record Setˢ (Γ : Context) (Δ : Times Γ) : Set₁
\end{code}
Let $F,G,H$ range over \textsf{Set}$^s$.
\begin{code}
variable F G H : Setˢ Γ Δ
\end{code}

We explain the type system for \textsf{Set}$^s$ in 
Figure~\ref{fig:SIL-type-system}, using traditional notation.
The judgment $Γ ⊢ F ⊣ Δ$ holds when $F$ uses the variables
in $Γ$ at the times specified in $Δ$. For example,
membership $M ∈ x$ is well typed when $x$ is in $Γ$
and $Δ$ assigns $x$ to $\Now$ and all the other variables
in $Γ$ to $\Later$. The later formula $▷ˢ F$ is well typed
at $▷ Δ$ when $F$ is well typed at $Δ$. The recursive formula
$μˢ F$ is well typed in $Γ$ at $Δ$ if $F$ is well typed
in $Γ,A$ at $Δ,\Later$. That is, the variable $\zero$ bound
by the $μˢ$ has type $A$ and may only be used later.
There is some redundancy in the type system, for example,
in the rule for membership $\varnow(Γ,x) = Δ$ could
instead simply check that $Δ$ maps $x$ to $\Now$.
However, this redundancy helps the Agda inference algorithm
when working with partial proofs.

\begin{code}
laters : ∀ (Γ : Context) → Times Γ
laters [] = ∅
laters (A ∷ Γ) = cons Later (laters Γ)
\end{code}

\begin{code}
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

_∪_ : ∀{Γ} (Δ₁ Δ₂ : Times Γ) → Times Γ
_∪_ {[]} Δ₁ Δ₂ = ∅
_∪_ {A ∷ Γ} (cons x Δ₁) (cons y Δ₂) = cons (choose x y) (_∪_ Δ₁ Δ₂)
\end{code}

\begin{figure}
\raggedright
\begin{center}
\begin{minipage}{0.3\textwidth}
\begin{align*}
  ▷ \mathsf{Now} &= \mathsf{Later} \\
  ▷ \mathsf{Later} &= \mathsf{Later}
\end{align*}
\end{minipage}  
\begin{minipage}{0.3\textwidth}
\begin{align*}
  ▷ ∅ &= ∅ \\
  ▷ (Δ,T) &= ▷ Δ,\, ▷ T
\end{align*}
\end{minipage}
\end{center}

\vspace{5pt}

\fbox{$Γ ⊢ F ⊣ Δ$}
\begin{gather*}
\inference{M : A & x : Γ ∋ A & \varnow(Γ,x) = Δ}{Γ ⊢ M ∈ x ⊣ Δ} \quad
\inference{Γ ⊢ F ⊣ Δ}{Γ ⊢ \, ▷ˢ F ⊣\, ▷ Δ} \\[2ex]
\inference{Γ⊢ F ⊣ Δ₁  & Γ ⊢ G ⊣ Δ₂}{Γ ⊢ F →ˢ G ⊣ Δ₁ ∪ Δ₂} \quad
\inference{Γ ⊢ F ⊣ Δ₁ & Γ ⊢ G ⊣ Δ₂}{Γ ⊢ F ×ˢ G ⊣ Δ₁ ∪ Δ₂} \quad
\inference{Γ ⊢ F ⊣ Δ₁ & Γ ⊢ G ⊣ Δ₂}{Γ ⊢ F ⊎ˢ G ⊣ Δ₁ ∪ Δ₂} \\[2ex]
\inference{∀ a ∈ A.\, Γ ⊢ f a ⊣ Δ}{Γ ⊢ ∀ˢ f ⊣ Δ} \quad
\inference{∀ a ∈ A.\, Γ ⊢ f a ⊣ Δ}{Γ ⊢ ∃ˢ f ⊣ Δ} \quad
\inference{}{Γ ⊢ p ˢ ⊣ \mathsf{laters}(Δ)}\\[2ex]
\inference{Γ,A ⊢ F ⊣ Δ,\mathsf{Later}}{Γ ⊢ μˢ F ⊣ Δ}
\end{gather*}
\caption{Type System for Well Founded and Nonexpansive Formulas}
\label{fig:SIL-type-system}
\end{figure}

% TODO: decide whether applyˢ is needed

The type system is implemented in the type signatures for the logical
operators, which we declare as follows.
\begin{code}
postulate _∈_ : A → (x : Γ ∋ A) → Setˢ Γ (var-now Γ x)
postulate ▷ˢ : Setˢ Γ Δ → Setˢ Γ (laters Γ)
infixr 6 _→ˢ_
postulate _→ˢ_ : Setˢ Γ Δ₁ → Setˢ Γ Δ₂ → Setˢ Γ (Δ₁ ∪ Δ₂)
infixr 7 _×ˢ_
postulate _×ˢ_ : Setˢ Γ Δ₁ → Setˢ Γ Δ₂ → Setˢ Γ (Δ₁ ∪ Δ₂)
infixr 7 _⊎ˢ_
postulate _⊎ˢ_ : Setˢ Γ Δ₁ → Setˢ Γ Δ₂ → Setˢ Γ (Δ₁ ∪ Δ₂)
postulate ∀ˢ : (A → Setˢ Γ Δ) → Setˢ Γ Δ
postulate ∃ˢ : {{_ : Inhabited A}} → (A → Setˢ Γ Δ) → Setˢ Γ Δ
postulate _ˢ : Set → Setˢ Γ (laters Γ)
postulate μˢ : (A → Setˢ (A ∷ Γ) (cons Later Δ)) → (A → Setˢ Γ Δ)
\end{code}

\section{Semantic Definitions and Proofs}

As mentioned previously, \citet{Appel:2001aa} use the notion of
$k$-approximation to define a semantic characterization of well
founded types. Similarly, we define the $k$-approximation of a
step-indexed proposition, using the notation $↓ᵒ k P$.  The
proposition $↓ᵒ k P$ is true at $i$ if $P$ at $i$ is true and $i < k$,
except when $k = 0$, in which case $↓ᵒ k P$ has to be true
unconditionally. (This differs from \citet{Appel:2001aa} in the
$\zero$ case.)

\begin{code}
↓ : ℕ → (ℕ → Set) → (ℕ → Set)
↓ k P zero = ⊤
↓ k P (suc j) = suc j < k × (P (suc j))

↓-down : ∀ k → downClosed (↓ k (# P))

↓ᵒ : ℕ → Setᵒ → Setᵒ
↓ᵒ k P = record { # = ↓ k (# P) ; down = ↓-down {P} k ; tz = tt }
\end{code}

We lift $k$-approximation to step-indexed predicates with the
following definition.

\begin{code}
↓ᵖ : ℕ → ∀{A} → Predᵒ A → Predᵒ A
↓ᵖ j P a = ↓ᵒ j (P a)
\end{code}

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
and wellfounded we reviewed in Section~\ref{sec:rec-pred}.
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
(Recall that \citet{Appel:2001aa} neglected to prove that $μ$ preserves
nonexpansive and wellfounded propositions.)
So instead of taking the $k$-approximation of the input $δ$, we
generalize $k$ to any $j$ greater or equal to $k$.

\begin{code}
nonexpansive : (x : Γ ∋ A) → (RecEnv Γ → Setᵒ) → Set₁
nonexpansive x P = ∀ δ j k → k ≤ j → ↓ᵒ k (P δ) ≡ᵒ ↓ᵒ k (P (↓ᵈ j x δ))

wellfounded : (x : Γ ∋ A) → (RecEnv Γ → Setᵒ) → Set₁
wellfounded x P = ∀ δ j k → k ≤ j → ↓ᵒ (suc k) (P δ) ≡ᵒ ↓ᵒ (suc k) (P (↓ᵈ j x δ))
\end{code}

We say that a functional $f$ is ``good'' with respect to variable $x$
at time $t$ if it is either \textsf{nonexpansive} (when $t = \Now$) or
\textsf{wellfounded} (when $t = \Later$).

\begin{code}
good-var : (x : Γ ∋ A) → Time → (RecEnv Γ → Setᵒ) → Set₁
good-var x Now f = nonexpansive x f
good-var x Later f = wellfounded x f
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

Two environments are equivalent if they are point-wise equivalent.

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

We can now define $\mathsf{Set}ˢ$ as the following record type.
The meaning is given by a functional and we require proofs that
the functional is good and congruent.

\begin{code}
record Setˢ Γ Δ where
  field
    ♯ : RecEnv Γ → Setᵒ 
    good : good-fun Δ ♯
    congr : congruent ♯
open Setˢ public
\end{code}

\section*{Appendix}

Step-indexed equality is an equivalence relation.

\begin{code}
abstract
  ≡ᵒ-refl refl i = (λ x → x) , (λ x → x)
  
  ≡ᵒ-sym PQ i = (proj₂ (PQ i)) , (proj₁ (PQ i))
  
  ≡ᵒ-trans PQ QR i = (λ z → proj₁ (QR i) (proj₁ (PQ i) z))
                   , (λ z → proj₂ (PQ i) (proj₂ (QR i) z))
\end{code}

The $k$-approximation operator is downward closed.

\begin{code}
↓-down {P} k = λ { zero x .zero z≤n → tt
                 ; (suc n) (sn<k , Pn) zero j≤n → tt
                 ; (suc n) (sn<k , Psn) (suc j) (s≤s j≤n) →
                     (≤-trans (s≤s (s≤s j≤n)) sn<k)
                   , (down P (suc n) Psn (suc j) (s≤s j≤n))}
\end{code}

