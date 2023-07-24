\begin{comment}
\begin{code}
{-# OPTIONS --rewriting #-}

module July2024.STLCBind where

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
open import July2024.StepIndexedLogic
open import July2024.STLC
open import July2024.STLCDeterministic

\end{code}
\end{comment}

\subsection{Bind Lemma}
\label{sec:bind-lemma}

In the next subsection we prove a compatibility lemma for every term
constructor in the STLC. Many of those term constructors
(\textsf{suc}, application, and \textsf{case}) have subexpressions
that must reduce to a value prior to the reduction of the term.  The
reasoning about those subexpressions is repetative, so we take the
standard approach of proving the following ``bind'' lemma.
It says that if one wants to prove that some term $F ⟦ M ⟧$ is
well behaved, and if the subexpression $M$ is well-behaved,
then it suffices to show that $F ⟦ V ⟧$ is well-behaved
assuming that $M$ reduces to $V$ and $V$ is a well-behaved value.

\begin{code}
ℰ-bind : ∀{𝒫}{A}{B}{F}{M}
   → 𝒫 ⊢ᵒ ℰ⟦ B ⟧ M
   → 𝒫 ⊢ᵒ (∀ᵒ[ V ] (M —↠ V)ᵒ →ᵒ 𝒱⟦ B ⟧ V →ᵒ ℰ⟦ A ⟧ (F ⟦ V ⟧))
   → 𝒫 ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)
\end{code}

We shall need to refer to the second premise of the \textsf{ℰ-bind}
lemma many times, so we define the following shorthand for it.

\begin{code}
Prem2 : Type → Type → Frame → Term → Setᵒ
Prem2 A B F M = ∀ᵒ[ V ] (M —↠ V)ᵒ →ᵒ 𝒱⟦ B ⟧ V →ᵒ ℰ⟦ A ⟧ (F ⟦ V ⟧)
\end{code}

\noindent This property is preserved by reduction. 

\begin{code}
Prem2-reduction : ∀{𝒫}{A}{B}{F}{M}{M′} →  M —→ M′  →  𝒫 ⊢ᵒ Prem2 A B F M
   → 𝒫 ⊢ᵒ Prem2 A B F M′
Prem2-reduction {𝒫}{A}{B}{F}{M}{M′} M→M′ Prem2[M] =
   Λᵒ[ V ] →ᵒI (→ᵒI M′→V→ℰFV) where
   M′→V→ℰFV : ∀{V} → 𝒱⟦ B ⟧ V ∷ (M′ —↠ V)ᵒ ∷ 𝒫 ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ V ⟧)
   M′→V→ℰFV {V} = ⊢ᵒ-sucP (Sᵒ Zᵒ) λ M′→V → 
                  let M—↠V = constᵒI (M —→⟨ M→M′ ⟩ M′→V) in
                  let M→V→ℰFV = Sᵒ (Sᵒ (instᵒ Prem2[M] V)) in
                  appᵒ (appᵒ M→V→ℰFV M—↠V) Zᵒ
\end{code}

The \textsf{ℰ-bind} lemma is proved by \textsf{lobᵒ} induction which
requires us to reformulate the statement of the lemma entirely within
SIL. So we define the following \textsf{ℰ-bind-prop} and auxilliary
\textsf{ℰ-bind-M} shorthands for the statement of \textsf{ℰ-bind} in
SIL.

\begin{code}
ℰ-bind-M : Type → Type → Frame → Term → Setᵒ
ℰ-bind-M A B F M = ℰ⟦ B ⟧ M →ᵒ Prem2 A B F M →ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)

ℰ-bind-prop : Type → Type → Frame → Setᵒ
ℰ-bind-prop A B F = ∀ᵒ[ M ] ℰ-bind-M A B F M
\end{code}

Figure~\ref{fig:bind-lemma} shows the proof of \textsf{𝒫 ⊢ᵒ
ℰ-bind-prop A B F} and \textsf{ℰ-bind} as a corollary. Note that after
the use of \textsf{lobᵒ} induction, we obtain the premise \textsf{▷ᵒ
ℰ-bind-prop A B F} which serves as the induction hypothesis. We then
perform case analysis on the fact that $M$ is well-behaved and
therefore satisfies progress, so it is either a well-behaved value or
it can reduce. In the case $M$ is a value, we conclude immediately by
applying the second premise, noting that $M$ reduces in zero steps to
itself. In case $M$ reduces to some $M′$, we need to prove that $F ⟦ M ⟧$ satisfies
progress and preservation and is therefore well behaved. The progress
part is easy because $F ⟦ M ⟧$ reduces by rule $ξ$. Regarding preservation,
we may assume $F ⟦ M ⟧$ takes a step to some $N$ and need to prove that $▷ᵒ \,ℰ⟦ A ⟧ \, N$.
By the \textsf{frame-inv} lemma (in the Appendix), we have $N = F ⟦ M′ ⟧$.
So we need to show that $▷ᵒ \,ℰ⟦ A ⟧ \, F ⟦ M′ ⟧$.
We obtain this by the induction hypothesis instantiated on $M′$,
so we must satisfy its two premises.
From $ℰ⟦ B ⟧ \, M$ we have $▷ᵒ \, ℰ⟦ B ⟧ \, M′$ (by preservation)
and by \textsf{Prem2-reduction} and \textsf{monoᵒ}
we have $▷ᵒ\, (\textsf{Prem2}\, A\, B\, F\, M′)$.
Note that the application of the induction hypothesis requires several
uses of the distributive rules ▷→ and ▷∀ to push ▷ᵒ through those
other logical connectives.


\begin{figure}[tbp]
\small
\begin{code}
ℰ-bind-aux : ∀{𝒫}{A}{B}{F} → 𝒫 ⊢ᵒ ℰ-bind-prop A B F
ℰ-bind-aux {𝒫}{A}{B}{F} = lobᵒ (Λᵒ[ M ] →ᵒI (→ᵒI aux)) where
  aux : ∀{M} → (Prem2 A B F M) ∷ ℰ⟦ B ⟧ M ∷ ▷ᵒ ℰ-bind-prop A B F ∷ 𝒫 ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)
  aux {M} = caseᵒ (proj₁ᵒ (substᵒ ℰ-stmt (Sᵒ Zᵒ))) Mval Mred 
   where
   𝒫′ = (Prem2 A B F M) ∷ ℰ⟦ B ⟧ M ∷ ▷ᵒ ℰ-bind-prop A B F ∷ 𝒫

   Mval : 𝒱⟦ B ⟧ M ∷ 𝒫′ ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)
   Mval = let Prem2[M] = λ V → (M —↠ V)ᵒ →ᵒ 𝒱⟦ B ⟧ V →ᵒ ℰ⟦ A ⟧ (F ⟦ V ⟧) in
          appᵒ (appᵒ (instᵒ{ϕᵃ = Prem2[M]} (Sᵒ Zᵒ) M) (constᵒI (M END))) Zᵒ

   Mred : (reducible M)ᵒ ∷ 𝒫′ ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)
   Mred = ℰ-intro progressMred preservationMred
    where
    progressMred : (reducible M)ᵒ ∷ 𝒫′ ⊢ᵒ progress A (F ⟦ M ⟧)
    progressMred = inj₂ᵒ (constᵒE Zᵒ λ {(M′ , M→M′) → constᵒI (_ , (ξ F M→M′))})

    preservationMred : (reducible M)ᵒ ∷ 𝒫′ ⊢ᵒ preservation A (F ⟦ M ⟧)
    preservationMred = (constᵒE Zᵒ λ redM →
                Sᵒ (Λᵒ[ N ] →ᵒI (constᵒE Zᵒ λ FM→N → Sᵒ (redM⇒▷ℰN redM FM→N))))
     where
     redM⇒▷ℰN : ∀{N} → reducible M → (F ⟦ M ⟧ —→ N) → 𝒫′ ⊢ᵒ ▷ᵒ (ℰ⟦ A ⟧ N)
     redM⇒▷ℰN {N} rM FM→N
         with frame-inv{M}{N}{F} rM FM→N
     ... | M′ , M→M′ , N≡F[M′] =
      let ▷ℰM′ : 𝒫′ ⊢ᵒ ▷ᵒ ℰ⟦ B ⟧ M′
          ▷ℰM′ = appᵒ (instᵒ{ϕᵃ = λ N → (M —→ N)ᵒ →ᵒ ▷ᵒ (ℰ⟦ B ⟧ N)}
                        (proj₂ᵒ (substᵒ ℰ-stmt (Sᵒ Zᵒ))) M′) (constᵒI M→M′) in
      let ▷M′→V→𝒱V→ℰFV : 𝒫′ ⊢ᵒ ▷ᵒ (Prem2 A B F M′)
          ▷M′→V→𝒱V→ℰFV = monoᵒ (Prem2-reduction{𝒫′}{A}{B} M→M′ Zᵒ) in
      let IH : 𝒫′ ⊢ᵒ ▷ᵒ ℰ-bind-prop A B F
          IH = Sᵒ (Sᵒ Zᵒ) in
      let ▷ℰFM′ : 𝒫′ ⊢ᵒ ▷ᵒ (ℰ⟦ A ⟧ (F ⟦ M′ ⟧))
          ▷ℰFM′ = let ϕᵃ = λ M → ℰ-bind-M A B F M in
                  appᵒ(▷→ (appᵒ(▷→ (instᵒ(▷∀{ϕᵃ = ϕᵃ} IH) M′)) ▷ℰM′)) ▷M′→V→𝒱V→ℰFV in
      subst (λ N → 𝒫′ ⊢ᵒ ▷ᵒ ℰ⟦ A ⟧ N) (sym N≡F[M′]) ▷ℰFM′
\end{code}

\begin{code}
ℰ-bind {𝒫}{A}{B}{F}{M} ⊢ℰM ⊢𝒱V→ℰFV =
  appᵒ (appᵒ (instᵒ{ϕᵃ = λ M → ℰ-bind-M A B F M} ℰ-bind-aux M) ⊢ℰM) ⊢𝒱V→ℰFV
\end{code}
\caption{Proof of the \textsf{ℰ-bind} lemma.}
\label{fig:bind-lemma}
\end{figure}


\clearpage
