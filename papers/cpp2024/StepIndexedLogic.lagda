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
downClosed S = ∀ n → S n → ∀ k → k ≤ n → S k
\end{code}

\noindent and here is the definition of the type for step-indexed propositions.
\begin{code}
record Setᵒ : Set₁ where
  field
    # : (ℕ → Set)
    down : downClosed #
    tz : # 0
open Setᵒ public
\end{code}

The false formula for SIL is embedded in Agda by defining an instance
of this record type, with the representation function mapping zero
to true and every other natural number to false. The proofs of
downward-closedness and true-at-zero are straightforward.
The embedding of the true formula into Agda is even more straightforward.
\begin{code}
⊥ᵒ : Setᵒ
⊥ᵒ = record { # = λ { zero → ⊤ ; (suc k) → ⊥}
            ; down = λ { zero x .zero z≤n → tt}
            ; tz = tt }

⊤ᵒ : Setᵒ
⊤ᵒ = record { # = λ k → ⊤
            ; down = λ n _ k _ → tt
            ; tz = tt }
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
▷ᵒ P = record
             { # = λ { zero → ⊤ ; (suc k) → # P k }
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

We define a step-indexed predicate over type $A$ to be a function from
$A$ to $Setᵒ$.

\begin{code}
Predᵒ : Set → Set₁
Predᵒ A = A → Setᵒ
\end{code}

\noindent The forall quantifier maps a step-indexed predicate to $Setᵒ$.

\begin{code}
∀ᵒ : ∀{A : Set} → Predᵒ A → Setᵒ
∀ᵒ{A} P = record { # = λ k → ∀ (a : A) → # (P a) k
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
obtain the true-at-zero property, we require that the type $A$ be
inhabited. We do not wish this requirement to clutter every use of the
exists quantifier, so we use Agda's support for instance arguments
(think type classes). So we define the following record type

\begin{code}
record Inhabited (A : Set) : Set where
  field
    elt : A
open Inhabited {{...}} public
\end{code}

\noindent and use it as an implicit instance argument in the
definition of exists, as follows.

\begin{code}
∃ᵒ : ∀{A : Set}{{_ : Inhabited A}} → Predᵒ A → Setᵒ
∃ᵒ{A} P = record { # = λ k → Σ[ a ∈ A ] # (P a) k
                     ; down = λ n (a , Pa) k k≤n → a , (down (P a) n Pa k k≤n)
                     ; tz = elt , tz (P elt) }

∃ᵒ-syntax = ∃ᵒ
infix 2 ∃ᵒ-syntax
syntax ∃ᵒ-syntax (λ x → P) = ∃ᵒ[ x ] P
\end{code}



