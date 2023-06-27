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


%===============================================================================
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
Let $ϕ, ψ, þ$ range over step-indexed propositions.
\begin{code}
variable ϕ ψ þ : Setᵒ
\end{code}
Let $p, q, r$ range over (regular) propositions.
\begin{code}
variable p q r : Set
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
step-indexed propositions $ϕ$ and $ψ$, their conjunction is the
function that takes the conjunction of applying them to the step
index. The proofs of downward-closedness and true-at-zero are
straightforward, relying on the proofs of these properties for $ϕ$ and $ψ$.
The story for disjunction is similar.
\begin{code}
_×ᵒ_ : Setᵒ → Setᵒ → Setᵒ
ϕ ×ᵒ ψ = record { # = λ k → # ϕ k × # ψ k
                ; down = λ k (ϕk , ψk) j j≤k →
                          (down ϕ k ϕk j j≤k) , (down ψ k ψk j j≤k)
                ; tz = (tz ϕ) , (tz ψ) }

_⊎ᵒ_ : Setᵒ → Setᵒ → Setᵒ
ϕ ⊎ᵒ ψ = record { # = λ k → # ϕ k ⊎ # ψ k
                ; down = λ { k (inj₁ ϕk) j j≤k → inj₁ (down ϕ k ϕk j j≤k)
                           ; k (inj₂ ψk) j j≤k → inj₂ (down ψ k ψk j j≤k)}
                ; tz = inj₁ (tz ϕ) }
\end{code}

The definition of impliciation is more interesting.  The following is
a naive first attempt, in which we following the same pattern as for
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

It remains to define the forall and exists quantifiers of SIL.  The
main idea is that we use Agda functions and variables to represent
quantification in SIL, as one would do in higher-order abstract
syntax. 

Let $A,B,C$ range over Agda types (element of \textsf{Set}).
\begin{code}
variable A B C : Set
\end{code}
We define a step-indexed predicate over type $A$ to be a function from
$A$ to $Setᵒ$.
\begin{code}
Predᵒ : Set → Set₁
Predᵒ A = A → Setᵒ
\end{code}
Let $P, Q$ range over step-indexed predicates.
\begin{code}
variable P Q : Predᵒ A
\end{code}

We define the constantly true predicate as follows.
\begin{code}
⊤ᵖ : ∀{A} → Predᵒ A
⊤ᵖ = (λ a → ⊤ᵒ)
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
  field elt : A
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

%===============================================================================
\section{Approximation}

THIS MOVED, UPDATE TEXT

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
\end{code}

The $k$-approximation operator is downward closed.

\begin{code}
↓-down : ∀ k → downClosed (↓ k (# ϕ))
↓-down {P} k = λ { zero x .zero z≤n → tt
                 ; (suc n) (sn<k , Pn) zero j≤n → tt
                 ; (suc n) (sn<k , Psn) (suc j) (s≤s j≤n) →
                     (≤-trans (s≤s (s≤s j≤n)) sn<k)
                   , (down P (suc n) Psn (suc j) (s≤s j≤n))}
\end{code}

\begin{code}
↓ᵒ : ℕ → Setᵒ → Setᵒ
↓ᵒ k P = record { # = ↓ k (# P) ; down = ↓-down {P} k ; tz = tt }
\end{code}

%===============================================================================
\section{Equivalence for Step-Indexed Propositions}

We define equivalence of step-indexed propositions $ϕ$ and $ψ$ to be
that for any step $k$, $ϕ$ at $k$ is true if and only if $ψ$ at $k$ is
true. This is of course an equivalence relation (the proofs are in the
Appendix), and we make use of a library named
\textsf{EquivalenceRelation} to provide nice syntax for equational
reasoning.

\begin{code}
abstract
  infix 2 _≡ᵒ_
  _≡ᵒ_ : Setᵒ → Setᵒ → Set
  ϕ ≡ᵒ ψ = ∀ k → # ϕ k ⇔ # ψ k

  ≡ᵒ-refl : ϕ ≡ ψ → ϕ ≡ᵒ ψ
  ≡ᵒ-sym : ϕ ≡ᵒ ψ → ψ ≡ᵒ ϕ
  ≡ᵒ-trans : ϕ ≡ᵒ ψ → ψ ≡ᵒ þ → ϕ ≡ᵒ þ

  ≡ᵒ-intro : ∀{ϕ ψ : Setᵒ} → (∀ k → # ϕ k ⇔ # ψ k) → ϕ ≡ᵒ ψ
  ≡ᵒ-intro P⇔Q k = P⇔Q k
  
  ≡ᵒ⇒⇔ : ∀{S T : Setᵒ}{k} → S ≡ᵒ T → # S k ⇔ # T k
  ≡ᵒ⇒⇔ {S}{T}{k} eq = eq k

  ≡ᵒ-to : ∀{ϕ ψ : Setᵒ} → ϕ ≡ᵒ ψ → (∀ k → # ϕ k → # ψ k)
  ≡ᵒ-to ϕψ k = ⇔-to (ϕψ k) 

  ≡ᵒ-fro : ∀{ϕ ψ : Setᵒ} → ϕ ≡ᵒ ψ → (∀ k → # ψ k → # ϕ k)
  ≡ᵒ-fro ϕψ k = ⇔-fro (ϕψ k)
instance
  SIL-Eqᵒ : EquivalenceRelation Setᵒ
  SIL-Eqᵒ = record { _⩦_ = _≡ᵒ_ ; ⩦-refl = ≡ᵒ-refl ; ⩦-sym = ≡ᵒ-sym ; ⩦-trans = ≡ᵒ-trans }
\end{code}

The $k$-approximation of any two step-indexed propositions is
equivalent when $k=0$.

\begin{code}
↓ᵒ-zero : ↓ᵒ zero ϕ ≡ᵒ ↓ᵒ zero ψ
↓ᵒ-zero = ≡ᵒ-intro λ {zero → (λ _ → tt) , λ _ → tt
                     ; (suc i) → (λ {()}) , (λ {()})}
\end{code}

OBSOLETE, REPLACE WITH ABOVE
\begin{code}
↓ᵒ-zeroᵖ : ∀{A}{P Q : Predᵒ A} (a : A) → ↓ᵒ zero (P a) ≡ᵒ ↓ᵒ zero (Q a)
↓ᵒ-zeroᵖ{A}{P}{Q} a = ≡ᵒ-intro λ {zero → (λ _ → tt) , λ _ → tt
                                ; (suc i) → (λ {()}) , (λ {()})}
\end{code}

\begin{code}
≡ᵖ-refl : ∀{A}{P Q : Predᵒ A}
  → P ≡ Q
  → ∀ {a} → P a ≡ᵒ Q a
≡ᵖ-refl refl {a} = ≡ᵒ-refl refl

≡ᵖ-sym : ∀{A}{P Q : Predᵒ A}
  → (∀ {a} → P a ≡ᵒ Q a)
  → ∀ {a} → Q a ≡ᵒ P a
≡ᵖ-sym P=Q {a} = ≡ᵒ-sym P=Q
\end{code}

%===============================================================================
\section{Functionals and Iteration}
\label{sec:rec-pred}

A function over step-indexed predicates is a \emph{functional}.
Let $f,g,h$ range over functionals.
\begin{code}
variable f g h : Predᵒ A → Predᵒ B
\end{code}

We say that a functional is congruent if it maps equivalent predicates
to equivalent predicates.

\begin{code}
congruentᵖ : ∀{A}{B} (f : Predᵒ A → Predᵒ B) → Set₁
congruentᵖ f = ∀ {P Q} → (∀ a → P a ≡ᵒ Q a) → ∀ b → (f P b) ≡ᵒ (f Q b)
\end{code}

We lift $k$-approximation to be a function over step-indexed
predicates with the following definition.

\begin{code}
↓ᵖ : ℕ → ∀{A} → (Predᵒ A → Predᵒ A)
↓ᵖ j P a = ↓ᵒ j (P a)
\end{code}
The $↓ᵖ$ operator is congruent
\begin{code}
cong-↓ : ∀{A}{k : ℕ} → congruentᵖ{A}{A} (↓ᵖ k)
cong-↓ {A} {k} {P} {Q} eq a = ≡ᵒ-intro aux
  where
  aux : (i : ℕ) → ↓ k (# (P a)) i ⇔ ↓ k (# (Q a)) i
  aux zero = (λ _ → tt) , λ _ → tt
  aux (suc i) = 
    (λ {(si≤k , Pasi) → si≤k , ≡ᵒ-to (eq a) (suc i) Pasi})
    , (λ {(si≤k , Qasi) → si≤k , ≡ᵒ-fro (eq a) (suc i) Qasi})
\end{code}

TODO

\begin{code}
wellfoundedᵖ : ∀{A} (f : Predᵒ A → Predᵒ A) → Set₁
wellfoundedᵖ f = ∀ a P k → ↓ᵒ (suc k) (f P a) ≡ᵒ ↓ᵒ (suc k) (f (↓ᵖ k P) a)
\end{code}


\begin{code}
iter : ∀ {ℓ} {A : Set ℓ} → ℕ → (A → A) → (A → A)
iter zero    f  =  id
iter (suc n) f  =  f ∘ iter n f
\end{code}

\begin{code}
iter-subtract : ∀{ℓ}{A : Set ℓ}{P : A} (F : A → A) (j k : ℕ)
  → j ≤ k
  → iter j F (iter (k ∸ j) F P) ≡ iter k F P
iter-subtract {A = A} {P} F .zero k z≤n = refl
iter-subtract {A = A} {P} F (suc j) (suc k) (s≤s j≤k)
  rewrite iter-subtract{A = A}{P} F j k j≤k = refl
\end{code}


\begin{code}
lemma15a : ∀ (j : ℕ) (f : Predᵒ A → Predᵒ A) (a : A)
  → wellfoundedᵖ f → congruentᵖ f
  → ↓ᵒ j (iter j f P a) ≡ᵒ ↓ᵒ j (iter j f Q a)
lemma15a zero f a wf-f cong-f = ↓ᵒ-zero
lemma15a {A}{P}{Q} (suc j) f a wf-f cong-f =
  ↓ᵒ (suc j) (f (iter j f P) a)         ⩦⟨ wf-f a (iter j f P) j ⟩ 
  ↓ᵒ (suc j) (f (↓ᵖ j (iter j f P)) a)  ⩦⟨ cong-↓ (cong-f λ a → lemma15a j f a wf-f cong-f) a ⟩
  ↓ᵒ (suc j) (f (↓ᵖ j (iter j f Q)) a)  ⩦⟨ ≡ᵒ-sym (wf-f a (iter j f Q) j) ⟩
  ↓ᵒ (suc j) (f (iter j f Q) a)         ∎
\end{code}

\begin{code}
lemma15b : ∀{A}{P : Predᵒ A}
   (k j : ℕ) (f : Predᵒ A → Predᵒ A) (a : A)
   → j ≤ k → wellfoundedᵖ f → congruentᵖ f
   → ↓ᵒ j (iter j f P a) ≡ᵒ ↓ᵒ j (iter k f P a)
lemma15b {A}{P} k j f a j≤k wf-f cong-f =
  ↓ᵒ j (iter j f P a)                     ⩦⟨ lemma15a j f a wf-f cong-f ⟩
  ↓ᵒ j (iter j f (iter (k ∸ j) f P) a)
                      ⩦⟨ cong-↓{A}{j}{iter j f (iter (k ∸ j) f P)}{iter k f P}
                              (λ a → ≡ᵖ-refl (iter-subtract f j k j≤k)) a ⟩
  ↓ᵒ j (iter k f P a)   ∎
\end{code}


\begin{code}
lemma17 : ∀{A}{P : Predᵒ A}{k}{a}
   → ↓ᵖ k (↓ᵖ (suc k) P) a ≡ᵒ ↓ᵖ k P a
lemma17 {A}{P}{k}{a} = ≡ᵒ-intro aux
  where
  aux : (i : ℕ) → # (↓ᵖ k (↓ᵖ (suc k) P) a) i ⇔ # (↓ᵖ k P a) i
  aux zero = (λ _ → tt) , (λ _ → tt)
  aux (suc i) = (λ {(x , (y , z)) → x , z})
              , (λ {(x , y) → x , (s≤s (<⇒≤ x) , y)})
\end{code}

%===============================================================================
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
\emph{environment functional}.

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
at $\laters(Γ)$ when $F$ is well typed at $Δ$. The recursive formula
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
\fbox{$Γ ⊢ F ⊣ Δ$}
\begin{gather*}
\inference{M : A & x : Γ ∋ A & \varnow(Γ,x) = Δ}{Γ ⊢ M ∈ x ⊣ Δ} \quad
\inference{Γ ⊢ F ⊣ Δ}{Γ ⊢ \, ▷ˢ F ⊣\, \laters(Γ)} \\[2ex]
\inference{Γ⊢ F ⊣ Δ₁  & Γ ⊢ G ⊣ Δ₂}{Γ ⊢ F →ˢ G ⊣ Δ₁ ∪ Δ₂} \quad
\inference{Γ ⊢ F ⊣ Δ₁ & Γ ⊢ G ⊣ Δ₂}{Γ ⊢ F ×ˢ G ⊣ Δ₁ ∪ Δ₂} \quad
\inference{Γ ⊢ F ⊣ Δ₁ & Γ ⊢ G ⊣ Δ₂}{Γ ⊢ F ⊎ˢ G ⊣ Δ₁ ∪ Δ₂} \\[2ex]
\inference{∀ a ∈ A.\, Γ ⊢ f a ⊣ Δ}{Γ ⊢ ∀ˢ f ⊣ Δ} \quad
\inference{∀ a ∈ A.\, Γ ⊢ f a ⊣ Δ}{Γ ⊢ ∃ˢ f ⊣ Δ} \quad
\inference{}{Γ ⊢ p ˢ ⊣ \laters(Δ)}\\[2ex]
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
μˢ : (A → Setˢ (A ∷ Γ) (cons Later Δ)) → (A → Setˢ Γ Δ)
\end{code}

\section{Semantic Definitions and Proofs}



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
nonexpansive-fun : (x : Γ ∋ A) → (RecEnv Γ → Setᵒ) → Set₁
nonexpansive-fun x f = ∀ δ j k → k ≤ j → ↓ᵒ k (f δ) ≡ᵒ ↓ᵒ k (f (↓ᵈ j x δ))

wellfounded-fun : (x : Γ ∋ A) → (RecEnv Γ → Setᵒ) → Set₁
wellfounded-fun x f = ∀ δ j k → k ≤ j → ↓ᵒ (suc k) (f δ) ≡ᵒ ↓ᵒ (suc k) (f (↓ᵈ j x δ))
\end{code}

We say that a functional $f$ is ``good'' with respect to variable $x$
at time $t$ if it is either \textsf{nonexpansive} (when $t = \Now$) or
\textsf{wellfounded} (when $t = \Later$).

\begin{code}
good-var : (x : Γ ∋ A) → Time → (RecEnv Γ → Setᵒ) → Set₁
good-var x Now f = nonexpansive-fun x f
good-var x Later f = wellfounded-fun x f
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


\subsection{Recursive Predicates}


Next we define an auxilliary function $μₒ$ that takes a function $f$
over step-indexed predicates and produces a raw step-indexed predicate
(without the proofs.) It iterates the function $k \plus 1$ times,
starting at the true formula.

\begin{code}
μₒ : ∀{A} → (Predᵒ A → Predᵒ A) → A → (ℕ → Set)
μₒ {A} f a k = #(iter{A = Predᵒ A} (suc k) f (λ a → ⊤ᵒ) a) k
\end{code}

Now, recall that the body $f$ of a $μˢ f$ has type
\[
    A → \mathsf{Set}ˢ (A ∷ Γ) (\mathsf{cons}\, \Later\, Δ))
\]
and not $\mathsf{Pred}ᵒ A → \mathsf{Pred}ᵒ A$.
So we define the following function to convert
from the former to the later.

\begin{code}
toFun : ∀{Γ}{ts : Times Γ}{A}
   → RecEnv Γ
   → (A → Setˢ (A ∷ Γ) (cons Later ts))
     ----------------------------------
   → (Predᵒ A → Predᵒ A)
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
  → (k : ℕ)
  → (j : ℕ)
  → (F : A → Setˢ (A ∷ Γ) (cons Later ts))
  → (a : A)
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
dc-iter : ∀(i : ℕ){A}
   → (F : Predᵒ A → Predᵒ A)
   → ∀ a → downClosed (#(iter i F ⊤ᵖ a))
dc-iter zero F = λ a n _ k _ → tt
dc-iter (suc i) F = λ a → down (F (iter i F ⊤ᵖ) a)
\end{code}

The $μₒ$ function is downward closed when applied to the
result of $\mathsf{toFun}$.
\begin{code}
down-μₒ : ∀{Γ}{ts : Times Γ}{A}{P : A → Setˢ (A ∷ Γ) (cons Later ts)}
    {a : A}{δ : RecEnv Γ}
  → downClosed (μₒ (toFun δ P) a)
down-μₒ {Γ}{ts}{A}{P}{a}{δ} k iterskPk zero j≤k = tz (toFun δ P (id ⊤ᵖ) a)
down-μₒ {Γ}{ts}{A}{P}{a}{δ} (suc k′) μPa (suc j′) (s≤s j′≤k′) =
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
      ↓-iter-ssj = ≡ᵒ-to (≡ᵒ-sym eq) (suc j′) ↓-iter-ssk in
  proj₂ ↓-iter-ssj
\end{code}

\begin{code}
muᵒ : ∀{Γ}{ts : Times Γ}{A}
   → (A → Setˢ (A ∷ Γ) (cons Later ts))
   → RecEnv Γ
     ----------------------------------
   → (A → Setᵒ)
muᵒ {Γ}{ts}{A} f δ a =
  record { # = μₒ (toFun δ f) a
         ; down = down-μₒ {Γ}{ts}{A}{f}{a}{δ}
         ; tz = tz ((toFun δ f) ⊤ᵖ a) }
\end{code}



\begin{code}
good-fun-mu : ∀{Γ}{Δ : Times Γ}{A}
   → (S : A → Setˢ (A ∷ Γ) (cons Later Δ))
   → (a : A)
   → good-fun Δ (λ δ → muᵒ S δ a)
\end{code}

\begin{code}
congruent-mu : ∀{Γ}{Δ : Times Γ}{A}
   (P : A → Setˢ (A ∷ Γ) (cons Later Δ))
   (a : A)
   → congruent (λ δ → muᵒ P δ a)
\end{code}

\begin{code}
μˢ {Γ}{Δ}{A} P a =
  record { ♯ = λ δ → muᵒ P δ a
         ; good = good-fun-mu P a
         ; congr = congruent-mu P a }
\end{code}


%===============================================================================
\section*{Appendix}

Step-indexed equality is an equivalence relation.

\begin{code}
abstract
  ≡ᵒ-refl refl i = (λ x → x) , (λ x → x)
  
  ≡ᵒ-sym PQ i = (proj₂ (PQ i)) , (proj₁ (PQ i))
  
  ≡ᵒ-trans PQ QR i = (λ z → proj₁ (QR i) (proj₁ (PQ i) z))
                   , (λ z → proj₂ (PQ i) (proj₂ (QR i) z))
\end{code}


\begin{code}
abstract
  lemma18a : ∀{Γ}{Δ : Times Γ}{A}
     → (k : ℕ)
     → (F : A → Setˢ (A ∷ Γ) (cons Later Δ))
     → (a : A)
     → (δ : RecEnv Γ)
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

lemma18b : ∀{Γ}{Δ : Times Γ}{A}
     → (j : ℕ)
     → (F : A → Setˢ (A ∷ Γ) (cons Later Δ))
     → (a : A)
     → (δ : RecEnv Γ)
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
       
lemma19a : ∀{Γ}{Δ : Times Γ}{A}
   (F : A → Setˢ (A ∷ Γ) (cons Later Δ))
   (a : A)
   (j : ℕ)
   (δ : RecEnv Γ)
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
good-now-mu {Γ} {Δ} {A} S a x time-x δ zero j k≤j =
    ↓ᵒ-zeroᵖ{A}{muᵒ S δ}{muᵒ S (↓ᵈ _ x δ)} a
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

congruent-mu{Γ}{Δ}{A} P a {δ}{δ′} δ=δ′ = ≡ᵒ-intro Goal
  where
  Goal : (k : ℕ) → μₒ (toFun δ P) a k ⇔ μₒ (toFun δ′ P) a k
  Goal k = ≡ᵒ⇒⇔ (cong-iter{A}{a} (suc k) (toFun δ P) (toFun δ′ P)
                    (cong-toFun P δ=δ′) ⊤ᵖ)
\end{code}

