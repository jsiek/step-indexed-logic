\begin{comment}
\begin{code}
{-# OPTIONS --without-K  --prop #-}

module Membership where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product
   using (_×_; _,_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym)

open import PropP
open import Variables
open import Env
open import RawSetO
open import Approx
open import SetO
open import EquivalenceRelationProp using (subst; ≐-sym; ≐-refl)

{---------------------- Membership in Recursive Predicate ---------------------}
\end{code}
\end{comment}

\subsection{Membership: Semantics and Lemmas}

The semantics of the SIL membership connective $\_∈\_$ is defined in
terms of the following \textsf{lookup} function, which finds the
predicate associated with a variable in a given environment.

\begin{code}
lookup : ∀{Γ}{A} → Γ ∋ A → RecEnv Γ → Predₒ A
lookup {B ∷ Γ} {.B} zeroᵒ (P , δ) = P
lookup {B ∷ Γ} {A} (sucᵒ x) (P , δ) = lookup{Γ}{A} x δ
\end{code}

The \textsf{lookup} function is downward closed.

\begin{code}
down-lookup : ∀{Γ}{A}{x}{a : A} → (δ : RecEnv Γ) → downClosedᵈ δ → downClosed (lookup x δ a)
down-lookup {x = zeroᵒ}{a} (P , δ) (dcP ,ₚ dcδ) = dcP a
down-lookup {x = sucᵒ x} (P , δ) (dcP ,ₚ dcδ) = down-lookup δ dcδ
\end{code}

Next we prove that \textsf{lookup} is semantically wellformed. That
is, it is nonexpansive or contractive with respect to every variable
in the environment depending on whether the variable is categorized as
\textsf{Now} or \textsf{Later}. For this purpose we prove the
following two support lemmas.

The \textsf{lookup} function applied to variable $x$ in environment δ
is $k$-equivalent to the \textsf{lookup} function applied to variable
$x$ in environment $↓ᵈ \; j \; y \;δ$, for any $j$ equal or larger
than $k$.

\begin{code}
↓-lookup : ∀{Γ}{A}{B}{a}{k}{j}{δ : RecEnv Γ} (x : Γ ∋ A) (y : Γ ∋ B)
   → k ≤ₚ j
   → (lookup{Γ}{A} x δ a) ≡ₒ[ k ] (lookup{Γ}{A} x (↓ᵈ j y δ) a)
↓-lookup {a = a}{k}{j}{P , δ} zeroᵒ zeroᵒ k≤j = ≡ₒ-sym (j≤k⇒↓kϕ≡[j]ϕ{j = k} (P a) k≤j)
↓-lookup zeroᵒ (sucᵒ y) k≤j = ≡ₒ-refl refl
↓-lookup (sucᵒ x) zeroᵒ k≤j = ≡ₒ-refl refl
↓-lookup {k = k} (sucᵒ x) (sucᵒ y) k≤j = ↓-lookup{k = k} x y k≤j
\end{code}

Given two different variables $x$ and $y$, applying \textsf{lookup} to $x$
in δ is equivalent to \textsf{lookup} of $x$ in the environment $↓ᵈ\; j\; y\; δ$
that applies a $j$-approximation to the entry for $y$ in δ.

\begin{code}
lookup-diff : ∀{Γ}{Δ : Times Γ}{A}{B}{δ : RecEnv Γ}{j} (x : Γ ∋ A) (y : Γ ∋ B)
   → timeof x Δ ≢ timeof y Δ
   → lookup{Γ}{A} x (↓ᵈ j y δ) ≡ lookup{Γ}{A} x δ
lookup-diff {C ∷ Γ} {t ∷ Δ} zeroᵒ zeroᵒ neq = ⊥-elim (neq refl)
lookup-diff {C ∷ Γ} {t ∷ Δ} zeroᵒ (sucᵒ y) neq = refl
lookup-diff {C ∷ Γ} {t ∷ Δ} (sucᵒ x) zeroᵒ neq = refl
lookup-diff {C ∷ Γ} {t ∷ Δ} (sucᵒ x) (sucᵒ y) neq = lookup-diff x y neq
\end{code}

The main event of this section is the following proof that
\textsf{lookup} is wellformed. That is, we need to show that
\textsf{lookup} of $x$ is wellformed with respect to every variable
$y$ that is in scope. We proceed by cases on whether the time for
$y$ is \textsf{Now} or \textsf{Later}. If the time is \textsf{Now},
we need to show that the \textsf{lookup} of $x$ is nonexpansive in $y$,
that is, \textsf{lookup x δ a ≡ₒ[ k ] lookup x (↓ᵈ j y δ′) a}.
That follows from the above lemma \textsf{↓-lookup}.
If the time for $y$ is \textsf{Later}, we need to show that the 
\textsf{lookup} of $x$ is contractive in $y$, that is,
\textsf{lookup x δ a ≡ₒ[ suc k ] lookup x (↓ᵈ j y δ) a}.
That follows from the above lemma \textsf{lookup-diff}.

\begin{code}
wellformed-lookup : ∀{Γ}{A}{a} → (x : Γ ∋ A) → wellformed-prop (var-now Γ x) (λ δ → lookup x δ a)
wellformed-lookup {Γ}{A}{a} x y
    with timeof y (var-now Γ x) in eq-y
... | Now = SNE where
    SNE : nonexpansive y (λ { δ → lookup x δ a})
    SNE δ j k k≤j = ↓-lookup{k = k} x y k≤j
... | Later = SC where
    timeof-diff : ∀{Γ}{Δ : Times Γ}{A}{B} (x : Γ ∋ A) (y : Γ ∋ B) → timeof x Δ ≡ Now → timeof y Δ ≡ Later
       → timeof x Δ ≢ timeof y Δ
    timeof-diff x y eq1 eq2 rewrite eq1 | eq2 = λ ()
    SC : contractive y (λ { δ → lookup x δ a})
    SC δ j k k≤j =
      let eq = (lookup-diff{Γ}{δ = δ}{j} x y (timeof-diff x y (timeof-var-now x) eq-y)) in
      subst (λ X → (lookup x δ a) ≡ₒ[ suc k ] (X a)) (≐-sym (≐-refl eq)) (≡ₒ-refl refl)
\end{code}

We finish this section with a straightforward proof that \textsf{lookup} is congruent.

\begin{code}
congruent-lookup : ∀{Γ}{A} (x : Γ ∋ A) (a : A) → congruent (λ δ → lookup x δ a)
congruent-lookup x a d=d′ = aux x a d=d′
  where
  aux : ∀{Γ}{A}{δ δ′ : RecEnv Γ} (x : Γ ∋ A) (a : A) → δ ≡ᵈ δ′ → lookup x δ a ≡ₒ lookup x δ′ a
  aux {B ∷ Γ} {.B}{P , δ}{P′ , δ′} zeroᵒ a (P=P′ ,ₚ d=d′) = P=P′ a
  aux {B ∷ Γ} {A}{P , δ}{P′ , δ′} (sucᵒ x) a (P=P′ ,ₚ d=d′) = aux x a d=d′
\end{code}
