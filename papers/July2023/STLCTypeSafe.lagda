\begin{comment}
\begin{code}
{-# OPTIONS --rewriting --prop #-}

module July2023.STLCTypeSafe where

open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Nat.Induction
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List using (map)
open import Data.Nat.Properties
open import Data.Product using (_,_; proj₁; proj₂; Σ; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import StepIndexedLogic2
open import July2023.STLC2
open import July2023.LogRel2
open import July2023.STLCSafe2
open import PropP

\end{code}
\end{comment}


\subsection{Proof of Semantic Type Safety}
\label{sec:proof-sem-safety}

The type safety property, stated below, involves multi-step reduction,
whereas our logical relation merely says that a well-behaved term is
one that satisfies single-step progress and preservation.

\begin{code}
type-safety : ∀ {A} → [] ⊢ M ⦂ A → M —↠ N →  ⌊ Value N ⊎ (Σ[ N′ ∈ Term ] (N —→ N′)) ⌋
\end{code}

\noindent So we prove the following lemma, which states that if $M$ is
well behaved and multi-step reduces to $N$, then $N$ is well behaved.

\begin{code}
ℰ-multi-preserve : ∀ {A} → (r : M —↠ N) → [] ⊢ᵒ ℰ⟦ A ⟧ M  → [] ⊢ᵒ ℰ⟦ A ⟧ N
ℰ-multi-preserve {A = A} (_ END) ℰM = ℰM
ℰ-multi-preserve {A = A} (_—→⟨_⟩_ M {M′} M→M′ M′—↠N) ℰM =
  let pres = proj₂ᵒ (ℰ-elim ℰM) in
  let ▷ℰM′ = →ᵒE (∀ᵒE pres M′) (pureᵒI M→M′) in
  ℰ-multi-preserve M′—↠N (▷ϕ⇒ϕ ▷ℰM′)
\end{code}

\noindent The Type Safety theorem follows from the \textsf{fundamental} lemma
and \textsf{ℰ-multi-preserve}.

\begin{minipage}{\textwidth}
\begin{code}
type-safety {M}{N}{A} ⊢M M—↠N =
   let ℰM = fundamental ⊢M id in
   let ℰN = ℰ-multi-preserve M—↠N ℰM in
   let progᵒ = proj₁ᵒ (ℰ-elim ℰN) in
   let prog = caseᵒ progᵒ
               (pureᵒE (𝒱⇒Value A N Zᵒ) λ v → pureᵒI (inj₁ v))
               (pureᵒE Zᵒ λ (N′ , N→N′) → pureᵒI (inj₂ (N′ , N→N′))) in
   pureᵒE[] prog
\end{code}
\end{minipage}
