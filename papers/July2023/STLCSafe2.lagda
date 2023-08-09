\begin{comment}
\begin{code}
{-# OPTIONS --rewriting --prop #-}

module July2023.STLCSafe2 where

open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Nat.Induction
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List using (map)
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
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
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Sig
open import Var
open import StepIndexedLogic2 renaming (subst to substₚ)
open import July2023.STLC2
open import July2023.LogRel2
open import July2023.STLCDeterministic2
open import July2023.STLCBind2
open import PropLib using () renaming (_,_ to _,ₚ_)

\end{code}
\end{comment}

\subsection{Compatibility Lemmas}
\label{sec:compatibility-lemmas}

Each of the compatibility lemmas mimics one of the typing rules, but
replaces the well-typed relation with the well-behaved relation.
For example, for the typing rule
\[
   \inference{Γ ⊢ M ⦂ `ℕ}{Γ ⊢ \mathsf{`suc}\, M ⦂ `ℕ}
\]
we prove the following compatibility lemma
\[
   \inference{Γ ⊨ M ⦂ `ℕ}{Γ ⊨ \mathsf{`suc}\, M ⦂ `ℕ}
\]

We begin with the compatibility lemmas corresponding to the rules for
well-typed values. The literal for zero is trivially well behaved.

\begin{code}
compatible-zero : ∀{Γ} → Γ ⊨ⱽ `zero ⦂ `ℕ
compatible-zero {Γ} γ = substᵒ (≡ᵒ-sym 𝒱-zero) ttᵒ
\end{code}

The successor of a value is well-behaved as a direct result of the
lemma \textsf{𝒱-suc}.

\begin{code}
compatible-sucⱽ : ∀{Γ}{V} → Γ ⊨ⱽ V ⦂ `ℕ  →  Γ ⊨ⱽ `suc V ⦂ `ℕ
compatible-sucⱽ {Γ}{V} ⊨V γ = substᵒ (≡ᵒ-sym 𝒱-suc) (⊨V γ)
\end{code}

A lambda abstraction is well-behaved if it has a well-behaved body.
Here we make use of an important substitution lemma from the ABT library, that
\[
    (⟪ ext\, γ ⟫ N) [ W ] = ⟪ W • γ ⟫ N
\]

\begin{code}
compatible-λ : ∀{Γ}{A}{B}{N} → (A ∷ Γ) ⊨ N ⦂ B  →  Γ ⊨ⱽ (ƛ N) ⦂ (A ⇒ B)
compatible-λ {Γ}{A}{B}{N} ⊨N γ = substᵒ (≡ᵒ-sym 𝒱-fun) (Λᵒ[ W ] →ᵒI ▷𝓔N[W])
  where
  ▷𝓔N[W] : ∀{W} → ▷ᵒ (𝒱⟦ A ⟧ W) ∷ 𝓖⟦ Γ ⟧ γ  ⊢ᵒ  ▷ᵒ (ℰ⟦ B ⟧ ((⟪ ext γ ⟫ N) [ W ]))
  ▷𝓔N[W] {W} = →ᵒE (Sᵒ (▷→ (monoᵒ (→ᵒI (⊨N (W • γ)))))) Zᵒ
\end{code}

A fixpoint value is well-behaved if the underlying value is well-behaved.
The proof of this compatibility lemma is interesting because it goes by
\textsf{lobᵒ} induction. To prove that $𝒱⟦ A ⇒ B⟧ \, μ V'$ where $V' = ⟪ γ ⟫ V$,
we need to prove that $▷ᵒ 𝒱⟦ A ⇒ B ⟧ \, V'[ μ V' ]$. Again, using the
subtitution lemma from the ABT, this is equivalent to 
$▷ᵒ 𝒱⟦ A ⇒ B ⟧ \, ⟪ μ V' • γ ⟫ V$. The later we obtain by noting that
$V$ is well-behaved and that $μ V' • γ$ is a well-behaved substitution,
which follows from the fact that $μ V'$ is well behaved (by the induction hypothesis)
and that γ is well-behaved.

\begin{code}
compatible-μ : ∀{Γ}{A}{B}{V} → Value V  →  ((A ⇒ B) ∷ Γ) ⊨ⱽ V ⦂ (A ⇒ B)
   → Γ ⊨ⱽ (μ V) ⦂ (A ⇒ B)
compatible-μ {Γ}{A}{B}{V} v ⊨V γ =
  lobᵒ (substᵒ (≡ᵒ-sym 𝒱-μ) (pureᵒI (subst-preserves-value (ext γ) _ v) ,ᵒ ▷𝒱V))
  where
  V' = ⟪ ext γ ⟫ V
  ▷𝒱V : ▷ᵒ (𝒱⟦ A ⇒ B ⟧ (μ V')) ∷ 𝓖⟦ Γ ⟧ γ ⊢ᵒ ▷ᵒ (𝒱⟦ A ⇒ B ⟧ (⟪ μ V' • γ ⟫ V))
  ▷𝒱V = {!!} -- ▷→▷ Zᵒ (⊢ᵒI λ {n (𝒱μγVn , _ , 𝓖γn) → ⊢ᵒE (⊨V (μ V' • γ)) n (𝒱μγVn , 𝓖γn)})
\end{code}

That completes the compatibility lemmas for well-typed values, so we
turn to the compatibility lemmas for well-typed terms. A well-typed
variable is also a well-behaved variable. This is true because the
substitution γ is well-behaved and a well-behaved value is also a
well-behaved term.

\begin{code}
compatible-var : ∀ {Γ A x} → Γ ∋ x ⦂ A  →  Γ ⊨ ` x ⦂ A
compatible-var {Γ}{A}{x} ∋x γ rewrite sub-var γ x = 𝒱⇒ℰ (lookup-𝓖 Γ γ ∋x)
  where
  lookup-𝓖 : ∀ Γ γ →  ∀ {A}{y} → (Γ ∋ y ⦂ A)  →  𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝒱⟦ A ⟧ (γ y)
  lookup-𝓖 (B ∷ Γ) γ {A} {zero} refl = Zᵒ
  lookup-𝓖 (B ∷ Γ) γ {A} {suc y} ∋y = Sᵒ (lookup-𝓖 Γ (λ x → γ (suc x)) ∋y) 
\end{code}

The successor of a term $M$ is well-behaved if $M$ is well-behaved.
Here we use the \textsf{ℰ-bind} lemma to exhange $M$ for some
well-behaved value $V$ that it reduces to. We obtain
$𝒱⟦ `ℕ ⟧ (`suc \, V)$ from $𝒱⟦ `ℕ ⟧ V$ and then note again that a
well-behaved value is also a well-behaved term.

\begin{code}
compatible-suc : ∀{Γ}{M} → Γ ⊨ M ⦂ `ℕ  →  Γ ⊨ `suc M ⦂ `ℕ
compatible-suc {Γ}{M} ⊨M γ = ℰ-bind {F = suc□} (⊨M γ) (Λᵒ[ V ] →ᵒI (→ᵒI ⊢ℰsucV))
  where
  ⊢ℰsucV : ∀{V} → 𝒱⟦ `ℕ ⟧ V ∷ (⟪ γ ⟫ M —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ ⊢ᵒ ℰ⟦ `ℕ ⟧ (`suc V)
  ⊢ℰsucV {V} = 𝒱⇒ℰ (substᵒ (≡ᵒ-sym 𝒱-suc) Zᵒ)
\end{code}

The term \textsf{case L M N} is well-behaved when its subterms are.
The proof of this compatibility lemma is given in
Figure~\ref{fig:compatible-case}.  We apply the \textsf{ℰ-bind} lemma
to obtain a well-behaved value $V$ that $L$ reduces to. Using the
following inversion lemma, we splits our proof into two cases
where $V = \mathsf{zero}$ or $V = \mathsf{suc}\,V′$.

\begin{code}
{-
𝒱ℕ-inv : ∀{n}{Cont : Set} → #(𝒱⟦ `ℕ ⟧ V) (suc n) → (V ≡ `zero → Cont)
  → (∀ V′ → V ≡ `suc V′ → Cont) → Cont
𝒱ℕ-inv {`zero}{n}{Cont} 𝒱V contz conts = contz refl
𝒱ℕ-inv {`suc V′}{n}{Cont} 𝒱V contz conts = conts V′ refl
-}
\end{code}

The term \textsf{case zero M N} satisfies progress by rule \textsf{β-zero}.
It satisfies preservation because of the premise that $M$ is well behaved.
(The proof of \textsf{deterministic} is in the Appendix.)
The term \textsf{case (suc V′) M N} satisfies progress by rule \textsf{β-suc}
and it satisfies preservation because $N$ is well-behaved and so is $V′$.

\begin{figure}[tbp]
\small
\begin{code}
compatible-case : ∀{Γ L M N A} → Γ ⊨ L ⦂ `ℕ  →  Γ ⊨ M ⦂ A  →  `ℕ ∷ Γ ⊨ N ⦂ A  →  Γ ⊨ case L M N ⦂ A
compatible-case {Γ}{L}{M}{N}{A} ⊨L ⊨M ⊨N γ =
  ℰ-bind {F = case□ (⟪ γ ⟫ M) (⟪ ext γ ⟫ N)} (⊨L γ) (Λᵒ[ V ] →ᵒI (→ᵒI ⊢ℰcaseVMN))
   where
   𝒫₁ = λ V → 𝒱⟦ `ℕ ⟧ V ∷ (⟪ γ ⟫ L —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ
   ⊢ℰcaseVMN : ∀{V} → 𝒫₁ V ⊢ᵒ ℰ⟦ A ⟧ (case V (⟪ γ ⟫ M) (⟪ ext γ ⟫ N))
   ⊢ℰcaseVMN {V} = 𝒱-ℕ-case V Zᵒ
      {- Case V = zero -}
      (λ {refl →
        let prog : 𝒫₁ `zero ⊢ᵒ progress A (case `zero (⟪ γ ⟫ M) (⟪ ext γ ⟫ N))
            prog = inj₂ᵒ (pureᵒI (_ , β-zero)) in
        let pres : 𝒫₁ `zero ⊢ᵒ preservation A (case `zero (⟪ γ ⟫ M) (⟪ ext γ ⟫ N))
            pres = Λᵒ[ N ] (→ᵒI (pureᵒE Zᵒ λ {r →
              let N≡⟪γ⟫M = deterministic r β-zero in
              Sᵒ (substₚ (λ N → 𝒫₁ `zero ⊢ᵒ ▷ᵒ (ℰ⟦ A ⟧ N)) (≐-sym (≐-refl N≡⟪γ⟫M)) (monoᵒ (Sᵒ (Sᵒ (⊨M γ)))))})) in
        ℰ-intro prog pres})
      {- Case V = suc V′ -}
      (λ {V′ refl 𝒱V′ →
       pureᵒE (𝒱⇒Value `ℕ V′ 𝒱V′) λ v →
       let prog : 𝒫₁ (`suc V′) ⊢ᵒ progress A (case (`suc V′) (⟪ γ ⟫ M) (⟪ ext γ ⟫ N))
           prog = inj₂ᵒ (pureᵒI (_ , (β-suc v))) in
       let pres : 𝒫₁ (`suc V′) ⊢ᵒ preservation A (case (`suc V′) (⟪ γ ⟫ M) (⟪ ext γ ⟫ N))
           pres = Λᵒ[ L ] (→ᵒI (pureᵒE Zᵒ λ {r →
             let L≡⟪γ⟫N[V] = deterministic r (β-suc v) in
             let ▷ℰN[V′] : 𝒫₁ (`suc V′) ⊢ᵒ ▷ᵒ (ℰ⟦ A ⟧ (⟪ V′ • γ ⟫ N))
                 ▷ℰN[V′] =
                     let ℰ⟪V′•γ⟫N = ⊨N (V′ • γ) in
                     monoᵒ (weaken ℰ⟪V′•γ⟫N (𝒱-suc-E Zᵒ ,ₚ drop (drop ⊂-refl)) ) in
             Sᵒ (substₚ (λ L → 𝒫₁ (`suc V′) ⊢ᵒ ▷ᵒ (ℰ⟦ A ⟧ L)) (≐-sym (≐-refl L≡⟪γ⟫N[V])) ▷ℰN[V′])})) in
       ℰ-intro prog pres})
-- \end{code}
-- \caption{Compatibility lemma for the \textsf{case} expression.}
-- \label{fig:compatible-case}
-- \end{figure}

-- The proof of the compatibility lemma for application $L · M$ splits
-- into two cases, one for when $L$ reduces to a lambda abstraction and
-- another for when $L$ reduces to a fixpoint value. We prove a separate
-- lemma for each of these cases.

-- The first lemma (Figure~\ref{fig:apply-lambda}) handles the
-- application of a lambda abstraction $ƛ N′$. The term $ƛ N′ · W$
-- satisfies progress by rule β-ƛ.  It satisfies preservation because $ƛ
-- N′$ and $W$ are well-behaved values and so by lemma \textsf{𝒱-fun},
-- $N′ [ W ]$ is well behaved.

-- \begin{figure}[tbp]
-- \begin{code}
-- apply-λ : ∀{A}{B}{W}{N′}{𝒫} → 𝒫 ⊢ᵒ 𝒱⟦ A ⇒ B ⟧ (ƛ N′)  →  𝒫 ⊢ᵒ 𝒱⟦ A ⟧ W  →  Value W
--   → 𝒫 ⊢ᵒ ℰ⟦ B ⟧ (ƛ N′ · W)
-- apply-λ {A}{B}{W}{N′}{𝒫} ⊢𝒱V ⊢𝒱W w = 
--   let prog : 𝒫 ⊢ᵒ progress B (ƛ N′ · W)
--       prog = inj₂ᵒ (pureᵒI (_ , (β-ƛ w))) in
--   let pres : 𝒫 ⊢ᵒ preservation B (ƛ N′ · W)
--       pres = Λᵒ[ N ] →ᵒI (pureᵒE Zᵒ λ {r →
--                let ⊢▷ℰN′W : 𝒫 ⊢ᵒ ▷ᵒ (ℰ⟦ B ⟧ (N′ [ W ]))
--                    ⊢▷ℰN′W = →ᵒE (∀ᵒE (substᵒ 𝒱-fun ⊢𝒱V) W) (monoᵒ ⊢𝒱W) in
--                Sᵒ (subst (λ N → 𝒫 ⊢ᵒ ▷ᵒ (ℰ⟦ B ⟧ N)) (sym (deterministic r (β-ƛ w))) ⊢▷ℰN′W)}) in
--   ℰ-intro prog pres
-- \end{code}
-- \caption{Application of a well-behaved lambda abstraction.}
-- \label{fig:apply-lambda}
-- \end{figure}

-- The second lemma (Figure~\ref{fig:apply-mu}) handles the application
-- of a fixpoint value $μ V′$ to another value $W$.  For this case of the
-- proof we use \textsf{lobᵒ} induction, so we state the property that
-- we're trying to prove entirely in SIL:

-- \begin{code}
-- WBApp : Type → Type → Setᵒ
-- WBApp A B = ∀ᵒ[ V ] ∀ᵒ[ W ] (𝒱⟦ A ⇒ B ⟧ V →ᵒ 𝒱⟦ A ⟧ W →ᵒ ℰ⟦ B ⟧ (V · W))
-- \end{code}

-- \noindent We pass the induction hypothesis $▷ᵒ \,WBApp\, A\, B$ to this lemma.
-- The term $μ V′ · W$ satisfies progress by rule $β-μ$.
-- To prove preservation, we need to show that $V′ [ μ V′ ] · W$ is well behaved.
-- We apply the induction hypothesis, and we know that $W$ is well behaved,
-- so it suffices to show that $V′ [ μ V′ ]$ is well behaved.
-- This we prove using lemma 𝒱-μ and the premise that $μ V′$  is well behaved.

-- \begin{figure}[tbp]
-- \begin{code}
-- apply-μ : ∀{A}{B}{W}{V′}{𝒫} → 𝒫 ⊢ᵒ ▷ᵒ WBApp A B
--   → 𝒫 ⊢ᵒ 𝒱⟦ A ⇒ B ⟧ (μ V′)  →  Value (μ V′)
--   → 𝒫 ⊢ᵒ 𝒱⟦ A ⟧ W  →  Value W
--   → 𝒫 ⊢ᵒ ℰ⟦ B ⟧ (μ V′ · W)
-- apply-μ {A = A}{B}{W}{V′}{𝒫} IH ⊢𝒱V v ⊢𝒱W w = 
--   let prog : 𝒫 ⊢ᵒ progress B (μ V′ · W)
--       prog = inj₂ᵒ (pureᵒI (_ , β-μ (Value-μ-inv v) w)) in
--   let ▷ℰV[μV]·W : (μ V′ · W —→ (V′ [ μ V′ ]) · W) ᵒ ∷ 𝒫 ⊢ᵒ ▷ᵒ ℰ⟦ B ⟧ ((V′ [ μ V′ ]) · W)
--       ▷ℰV[μV]·W =
--         let ▷𝒱V[μV] = proj₂ᵒ (substᵒ 𝒱-μ (Sᵒ ⊢𝒱V)) in
--         let P = (λ V → ▷ᵒ (∀ᵒ[ W ] (𝒱⟦ A ⇒ B ⟧ V →ᵒ 𝒱⟦ A ⟧ W →ᵒ ℰ⟦ B ⟧ (V · W)))) in
--         →ᵒE (▷→ (→ᵒE (▷→ (∀ᵒE (▷∀ (∀ᵒE{ϕᵃ = P} (▷∀ (Sᵒ IH)) (V′ [ μ V′ ]))) W)) ▷𝒱V[μV]))
--              (monoᵒ (Sᵒ ⊢𝒱W)) in
--   let ▷ℰN : ∀ N → (μ V′ · W —→ N)ᵒ ∷ 𝒫 ⊢ᵒ ▷ᵒ (ℰ⟦ B ⟧ N)
--       ▷ℰN N = let-pureᵒ[ r ] Zᵒ within
--                subst (λ N → (μ V′ · W —→ N)ᵒ ∷ 𝒫 ⊢ᵒ ▷ᵒ (ℰ⟦ B ⟧ N))
--                      (sym (β-μ-inv (Value-μ-inv v) w r)) ▷ℰV[μV]·W in
--   let pres : 𝒫 ⊢ᵒ preservation B (μ V′ · W)
--       pres = Λᵒ[ N ] →ᵒI (▷ℰN N) in
--   ℰ-intro prog pres
-- \end{code}
-- \caption{Application of a well-behaved fixpoint value.}
-- \label{fig:apply-mu}
-- \end{figure}

-- With the above two lemmas complete, we turn to the proof of the
-- compatibility lemma for application (Figure~\ref{fig:compatible-app}).
-- The proof begins with two uses of the \textsf{ℰ-bind} lemma, for
-- subterms $L$ and $M$, which reduce to $V$ and $W$ respectively.
-- Now we need to prove $ℰ⟦ B ⟧ (V · W)$. We proceed by \textsf{lobᵒ} induction,
-- so we need to prove that \textsf{▷ᵒ WBApp A B} entails \textsf{WBApp A B}.
-- Because $V$ is well-behaved at function type, it must be either a
-- lambda abstraction or a fixpoint value. For the later case, we
-- use the lemma \textsf{apply-λ} , and in the former case, we
-- use \textsf{apply-μ}.

-- \begin{figure}[tbp]
-- \small
-- \begin{code}
-- compatible-app : ∀{Γ}{A}{B}{L}{M} →  Γ ⊨ L ⦂ (A ⇒ B)  →  Γ ⊨ M ⦂ A  →  Γ ⊨ L · M ⦂ B
-- compatible-app {Γ}{A}{B}{L}{M} ⊨L ⊨M γ = ℰ-bind {F = □· (⟪ γ ⟫ M)} (⊨L γ) (Λᵒ[ V ] →ᵒI (→ᵒI ⊢ℰVM))
--   where
--   ⊢ℰVM : ∀{V} → 𝒱⟦ A ⇒ B ⟧ V ∷ (⟪ γ ⟫ L —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ ⊢ᵒ ℰ⟦ B ⟧ (V · ⟪ γ ⟫ M)
--   ⊢ℰVM {V} = let-sucᵒ Zᵒ λ 𝒱Vsn → let v = 𝒱⇒Value (A ⇒ B) V 𝒱Vsn in
--     ℰ-bind {F = v ·□} (Sᵒ (Sᵒ (⊨M γ))) (Λᵒ[ V ] →ᵒI (→ᵒI ⊢ℰVW))
--     where
--     𝒫₂ = λ V W → 𝒱⟦ A ⟧ W ∷ (⟪ γ ⟫ M —↠ W)ᵒ ∷ 𝒱⟦ A ⇒ B ⟧ V ∷ (⟪ γ ⟫ L —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ
--     Gen-ℰVW : ∀{V′}{W′} → ▷ᵒ WBApp A B ∷ 𝒫₂ V′ W′ ⊢ᵒ WBApp A B
--     Gen-ℰVW {V′}{W′} = Λᵒ[ V ] Λᵒ[ W ] →ᵒI (→ᵒI aux) where
--       aux : ∀{V}{W} → 𝒱⟦ A ⟧ W ∷ 𝒱⟦ A ⇒ B ⟧ V ∷ ▷ᵒ WBApp A B ∷ 𝒫₂ V′ W′ ⊢ᵒ ℰ⟦ B ⟧ (V · W)
--       aux {V}{W} =
--         let ⊢𝒱V = Sᵒ Zᵒ in let ⊢𝒱W = Zᵒ in
--         let-sucᵒ ⊢𝒱V λ 𝒱Vsn → let-sucᵒ ⊢𝒱W λ 𝒱Wsn →
--         let v = 𝒱⇒Value (A ⇒ B) V 𝒱Vsn in let w = 𝒱⇒Value A W 𝒱Wsn in
--         𝒱-fun-case ⊢𝒱V (λ { N′ refl → apply-λ ⊢𝒱V ⊢𝒱W w })
--                         (λ { V′ refl → apply-μ (Sᵒ (Sᵒ Zᵒ)) ⊢𝒱V v ⊢𝒱W w })
--     ⊢ℰVW : ∀{V W} → 𝒫₂ V W ⊢ᵒ ℰ⟦ B ⟧ (V · W)
--     ⊢ℰVW {V}{W} = →ᵒE (→ᵒE (∀ᵒE (∀ᵒE (lobᵒ Gen-ℰVW) V) W) (Sᵒ (Sᵒ Zᵒ))) Zᵒ
-- \end{code}
-- \caption{Compatibility lemma for application.}
-- \label{fig:compatible-app}
-- \end{figure}

-- The last compatibility lemma shows that a well-behaved value is also a
-- well-behaved term, which is a corollary of the lemma 𝒱⇒ℰ.

-- \begin{code}
-- compatible-value : ∀{Γ V A} → Γ ⊨ⱽ V ⦂ A  →  Γ ⊨ V ⦂ A
-- compatible-value {Γ}{V}{A} ⊨V γ = 𝒱⇒ℰ (⊨V γ) 
-- \end{code}

-- \clearpage

-- \subsection{Fundamental Lemma}
-- \label{sec:fundamental}

-- The Fundamental Lemma(s) follow immediately from the compatibility
-- lemmas of the last section. So a well-typed value is also a
-- well-behaved value, and similarly for terms.

-- \begin{code}
-- fundamentalⱽ : ∀ {Γ W A} → (Γ ⊢ⱽ W ⦂ A) → (Γ ⊨ⱽ W ⦂ A)
-- fundamental : ∀ {Γ M A} → (Γ ⊢ M ⦂ A) → (Γ ⊨ M ⦂ A)

-- fundamentalⱽ {Γ} {.`zero} {.`ℕ} ⊢ⱽzero = compatible-zero
-- fundamentalⱽ {Γ} {`suc V} {.`ℕ} (⊢ⱽsuc ⊢V) = compatible-sucⱽ{V = V} (fundamentalⱽ ⊢V)
-- fundamentalⱽ {Γ} {ƛ N} {.(_ ⇒ _)} (⊢ⱽƛ ⊢N) = compatible-λ{N = N} (fundamental ⊢N)
-- fundamentalⱽ {Γ} {μ V} {.(_ ⇒ _)} (⊢ⱽμ ⊢V) =
--    compatible-μ{V = V} (⊢ⱽ⇒Value ⊢V) (fundamentalⱽ ⊢V)
   
-- fundamental {Γ} {.(` _)} {A} (⊢` x) = compatible-var x
-- fundamental {Γ} {`suc M} {.`ℕ} (⊢suc ⊢M) = compatible-suc{M = M} (fundamental ⊢M)
-- fundamental {Γ} {case L M N} {A} (⊢case ⊢L ⊢M ⊢N) =
--    compatible-case{L = L}{M}{N} (fundamental ⊢L) (fundamental ⊢M) (fundamental ⊢N)
-- fundamental {Γ} {L · M} {A} (⊢· ⊢L ⊢M) =
--    compatible-app{L = L}{M} (fundamental ⊢L) (fundamental ⊢M)
-- fundamental {Γ} {V} {A} (⊢val ⊢V) = compatible-value {V = V} (fundamentalⱽ ⊢V)
-- \end{code}

-- \subsection{Proof of Semantic Type Safety}
-- \label{sec:proof-sem-safety}

-- The type safety property, stated below, involves multi-step reduction,
-- whereas our logical relation merely says that a well-behaved term is
-- one that satisfies single-step progress and preservation.

-- \begin{code}
-- type-safety : ∀ {A} → [] ⊢ M ⦂ A → M —↠ N → Value N  ⊎ (∃[ N′ ] (N —→ N′))
-- \end{code}

-- \noindent So we prove the following lemma, which states that if $M$ is
-- well behaved and multi-step reduces to $N$, then $N$ is well behaved.

-- \begin{code}
-- ℰ-multi-preserve : ∀ {A} → (r : M —↠ N)  →  # (ℰ⟦ A ⟧ M) (suc (len r))  →  # (ℰ⟦ A ⟧ N) 1
-- ℰ-multi-preserve {A} (_ END) ℰM = ℰM
-- ℰ-multi-preserve {M}{N}{A} (_—→⟨_⟩_ .M {M′} M→M′ M′→N) (_ , pres) =
--     let ℰM′ : # (ℰ⟦ A ⟧ M′) (suc (len M′→N))
--         ℰM′ = pres M′ (suc (suc (len M′→N))) ≤-refl M→M′ in
--     ℰ-multi-preserve M′→N ℰM′
-- \end{code}

-- \noindent The Type Safety theorem follows from \textsf{fundamental}
-- followed by \textsf{ℰ-multi-preserve}.

-- \begin{code}
-- type-safety {A = A} ⊢M M—↠N
--     with ⊢ᵒE (fundamental ⊢M id) (suc (len M—↠N)) tt
-- ... | ℰM
--     with ℰ-multi-preserve M—↠N ℰM
-- ... | (inj₁ 𝒱N , _) = inj₁ (𝒱⇒Value A _ 𝒱N)
-- ... | (inj₂ N→ , _) = inj₂ N→
-- \end{code}
