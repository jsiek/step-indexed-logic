\begin{comment}
\begin{code}
{-# OPTIONS --without-K #-}
open import Data.List using (List; []; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong₂)

module Variables where
\end{code}
\end{comment}

\subsection{Variables}
\label{sec:variables}

The SIL logic includes variables to refer to the recursive predicates
introduced by the μᵒ operator. These variables are represented using
de Bruijn indices. In particular, we use the following
intrinsically-typed representation that associates a type with each
variable (the domain of the predicate).

\begin{code}
Context : Set₁
Context = List Set

data _∋_ : Context → Set → Set₁ where
  zeroᵒ : ∀{Γ}{A} → (A ∷ Γ) ∋ A
  sucᵒ : ∀{Γ}{A}{B} → Γ ∋ B → (A ∷ Γ) ∋ B
\end{code}

\noindent In most uses of SIL, there is only one μᵒ operator in a
formula, so the only variable we need is the zero de Bruijn index.  So
here we define a more suggestive alias for a variable that refers to
the recursive predicate.

\begin{code}
recᵒ : ∀{Γ}{A} → (A ∷ Γ) ∋ A
recᵒ = zeroᵒ
\end{code}

As discussed in §\ref{sec:intro-recursive-predicates}, SIL ensures
that the definition of a recursive predicate is well formed by
tracking the time at which every variable is used (\textsf{Now} or
\textsf{Later}) and requiring that μᵒ is only applied to a formula in
which the zero variable (for itself) is used \textsf{Later}.
So we define a \textsf{Time} data type as follows.

\begin{code}
data Time : Set where
  Now : Time
  Later : Time
\end{code}

\noindent We shall need a \textsf{Time} for each in-scope variable, so
we define a list of times for a context.

\begin{code}
data Times : Context → Set₁ where
  [] : Times []
  _∷_ : ∀{Γ}{A} → Time → Times Γ → Times (A ∷ Γ)
\end{code}

A number of auxilliary operations regarding contexts and times are
needed to express the well-formedness rules of SIL, which we describe
next. The \textsf{laters} function constructs a list of times for a
given context, where all the times are \textsf{Later}. This function
is used for atomic formula that are not variables. So when a variable
is not used at all in a formula, the variable is categorized as
\textsf{Later}.

\begin{code}
laters : ∀ (Γ : Context) → Times Γ
laters [] = []
laters (A ∷ Γ) = Later ∷ (laters Γ)
\end{code}

The \textsf{var-now} function is used in a variable occurence,
categorizing that variable as being used \textsf{Now} and all other
variables as being used \textsf{Later}.

\begin{code}
var-now : ∀ (Γ : Context) → ∀{A} → (x : Γ ∋ A) → Times Γ
var-now (B ∷ Γ) zeroᵒ = Now ∷ (laters Γ)
var-now (B ∷ Γ) (sucᵒ x) = Later ∷ (var-now Γ x)
\end{code}

For formulas with multiple sub-formula, SIL needs a way to combine the
time information obtained from each sub-formula. The \textsf{choose}
function returns \textsf{Now} is at least one of its arguments is
\textsf{Now} and it returns \textsf{Later} if both arguments are
\textsf{Later}.

\begin{code}
choose : Time → Time → Time
choose Now Now = Now
choose Now Later = Now
choose Later Now = Now
choose Later Later = Later
\end{code}

\noindent The \textsf{combine} function applies \textsf{choose} to
each element of two lists of times, to produce a new list of times.

\begin{code}
combine : ∀{Γ} (Δ₁ Δ₂ : Times Γ) → Times Γ
combine {[]} Δ₁ Δ₂ = []
combine {A ∷ Γ} (x ∷ Δ₁) (y ∷ Δ₂) = (choose x y) ∷ (combine Δ₁ Δ₂)
\end{code}

\noindent The \textsf{timeof} function looks up the \textsf{Time} for
a given variable in a list of times.

\begin{code}
timeof : ∀{Γ}{A} → (x : Γ ∋ A) → Times Γ → Time
timeof {B ∷ Γ} zeroᵒ (t ∷ Δ) = t
timeof {B ∷ Γ} (sucᵒ x) (t ∷ Δ) = timeof x Δ
\end{code}

Applying \textsf{timeof} to the result of \textsf{laters} always
produces \textsf{Later}.

\begin{code}
timeof-later : ∀{Γ}{A} → (x : Γ ∋ A) → (timeof x (laters Γ)) ≡ Later
timeof-later {B ∷ Γ} zeroᵒ = refl
timeof-later {B ∷ Γ} (sucᵒ x) = timeof-later x
\end{code}

\noindent Applying \textsf{timeof} to the result of \textsf{combine}
is the same as first applying \textsf{timeof} to both lists and then
applying \textsf{choose}.

\begin{code}
timeof-combine : ∀{Γ}{Δ₁ Δ₂ : Times Γ}{A}{x : Γ ∋ A}
   → timeof x (combine Δ₁ Δ₂) ≡ choose (timeof x Δ₁) (timeof x Δ₂)
timeof-combine {B ∷ Γ} {s ∷ Δ₁} {t ∷ Δ₂} {.B} {zeroᵒ} = refl
timeof-combine {B ∷ Γ} {s ∷ Δ₁} {t ∷ Δ₂} {A} {sucᵒ x} =
  timeof-combine {Γ} {Δ₁} {Δ₂} {A} {x}
\end{code}

\noindent Applying \textsf{combine} to two lists produced by
\textsf{laters} is equivalent to simply applying \textsf{laters}.

\begin{code}
combine-laters : ∀{Γ} → combine (laters Γ) (laters Γ) ≡ laters Γ
combine-laters {[]} = refl
combine-laters {A ∷ Γ} = cong₂ _∷_ refl combine-laters
\end{code}


