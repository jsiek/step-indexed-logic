\begin{comment}
\begin{code}
{-# OPTIONS --rewriting #-}

module cpp2024.STLCSafe where

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
open import cpp2024.StepIndexedLogic
open import cpp2024.STLC
open import cpp2024.STLCDeterministic
open import cpp2024.STLCBind

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
compatible-zero {Γ} γ = ⊢ᵒ-intro λ {zero x → tt; (suc i) x → ttᵖ}
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
compatible-lambda : ∀{Γ}{A}{B}{N} → (A ∷ Γ) ⊨ N ⦂ B  →  Γ ⊨ⱽ (ƛ N) ⦂ (A ⇒ B)
compatible-lambda {Γ}{A}{B}{N} ⊨N γ = substᵒ (≡ᵒ-sym 𝒱-fun) (Λᵒ[ W ] →ᵒI ▷𝓔N[W])
  where
  ▷𝓔N[W] : ∀{W} → ▷ᵒ 𝒱⟦ A ⟧ W ∷ 𝓖⟦ Γ ⟧ γ  ⊢ᵒ  ▷ᵒ ℰ⟦ B ⟧ ((⟪ ext γ ⟫ N) [ W ])
  ▷𝓔N[W] {W} = appᵒ (Sᵒ (▷→ (monoᵒ (→ᵒI (⊨N (W • γ)))))) Zᵒ
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
  lobᵒ (substᵒ (≡ᵒ-sym 𝒱-μ) (constᵒI (subst-preserves-value (ext γ) _ v) ,ᵒ ▷𝒱V))
  where
  V' = ⟪ ext γ ⟫ V
  ▷𝒱V : ▷ᵒ (𝒱⟦ A ⇒ B ⟧ (μ V')) ∷ 𝓖⟦ Γ ⟧ γ ⊢ᵒ ▷ᵒ (𝒱⟦ A ⇒ B ⟧ (⟪ μ V' • γ ⟫ V))
  ▷𝒱V = ▷→▷ Zᵒ (⊢ᵒ-intro λ {n (𝒱μγVn , _ , 𝓖γn) → ⊢ᵒ-elim (⊨V (μ V' • γ)) n (𝒱μγVn , 𝓖γn)})
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


Figure~\ref{fig:compatible-case}

\begin{code}
𝒱ℕ-inv : ∀{n}{Cont : Set} → #(𝒱⟦ `ℕ ⟧ V) (suc n) → (V ≡ `zero → Cont)
  → (∀ V′ → V ≡ `suc V′ → Cont) → Cont
𝒱ℕ-inv {`zero}{n}{Cont} 𝒱V contz conts = contz refl
𝒱ℕ-inv {`suc V′}{n}{Cont} 𝒱V contz conts = conts V′ refl 
\end{code}

\begin{figure}[tbp]
\small
\begin{code}
compatible-case : ∀{Γ L M N A} → Γ ⊨ L ⦂ `ℕ  →  Γ ⊨ M ⦂ A  →  `ℕ ∷ Γ ⊨ N ⦂ A
  → Γ ⊨ case L M N ⦂ A
compatible-case {Γ}{L}{M}{N}{A} ⊨L ⊨M ⊨N γ = ⊢ℰcaseLMN
  where
  ⊢ℰcaseLMN : 𝓖⟦ Γ ⟧ γ ⊢ᵒ ℰ⟦ A ⟧ (⟪ γ ⟫ (case L M N))
  ⊢ℰcaseLMN = ℰ-bind {F = case□ (⟪ γ ⟫ M) (⟪ ext γ ⟫ N)} (⊨L γ) (Λᵒ[ V ] →ᵒI (→ᵒI ⊢ℰcaseVMN))
   where
   𝒫₁ = λ V → 𝒱⟦ `ℕ ⟧ V ∷ (⟪ γ ⟫ L —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ
   ⊢ℰcaseVMN : ∀{V} → 𝒫₁ V ⊢ᵒ ℰ⟦ A ⟧ (case V (⟪ γ ⟫ M) (⟪ ext γ ⟫ N))
   ⊢ℰcaseVMN {V} = ⊢ᵒ-sucP Zᵒ λ {n} 𝒱Vsn →
     𝒱ℕ-inv{V}{n = n}{𝒫₁ V ⊢ᵒ ℰ⟦ A ⟧ (case V (⟪ γ ⟫ M) (⟪ ext γ ⟫ N))} 𝒱Vsn
     (λ { refl →
       let prog : 𝒫₁ `zero ⊢ᵒ progress A (case `zero (⟪ γ ⟫ M) (⟪ ext γ ⟫ N))
           prog = inj₂ᵒ (constᵒI (_ , β-zero)) in
        let pres : 𝒫₁ `zero ⊢ᵒ preservation A (case `zero (⟪ γ ⟫ M) (⟪ ext γ ⟫ N))
            pres = Λᵒ[ N ] (→ᵒI (constᵒE Zᵒ λ {r →
             let ▷ℰM : 𝒫₁ `zero ⊢ᵒ (▷ᵒ ℰ⟦ A ⟧ (⟪ γ ⟫ M))
                 ▷ℰM = monoᵒ (Sᵒ (Sᵒ (⊨M γ))) in
             let N≡⟪γ⟫M = deterministic r β-zero in
             Sᵒ (subst (λ N → 𝒫₁ `zero ⊢ᵒ ▷ᵒ (ℰ⟦ A ⟧ N)) (sym N≡⟪γ⟫M) ▷ℰM)})) in
       ℰ-intro prog pres})
     (λ { V′ refl →
       let v = 𝒱⇒Value `ℕ V′ 𝒱Vsn in
       let prog : 𝒫₁ (`suc V′) ⊢ᵒ progress A (case (`suc V′) (⟪ γ ⟫ M) (⟪ ext γ ⟫ N))
           prog = inj₂ᵒ (constᵒI (_ , (β-suc v))) in
       let pres : 𝒫₁ (`suc V′) ⊢ᵒ preservation A (case (`suc V′) (⟪ γ ⟫ M) (⟪ ext γ ⟫ N))
           pres = Λᵒ[ L ] (→ᵒI (constᵒE Zᵒ λ {r →
             let L≡⟪γ⟫N[V] = deterministic r (β-suc v) in
             let ▷ℰN[V′] : 𝒫₁ (`suc V′) ⊢ᵒ ▷ᵒ ℰ⟦ A ⟧ (⟪ V′ • γ ⟫ N)
                 ▷ℰN[V′] = monoᵒ (⊢ᵒ-intro λ {k (a , b , c) → ⊢ᵒ-elim (⊨N (V′ • γ)) k (a , c)}) in
             Sᵒ (subst (λ L → 𝒫₁ (`suc V′) ⊢ᵒ ▷ᵒ (ℰ⟦ A ⟧ L)) (sym L≡⟪γ⟫N[V]) ▷ℰN[V′])})) in
       ℰ-intro prog pres})
\end{code}
\caption{Compatibility lemma for the \textsf{case} expression.}
\label{fig:compatible-case}
\end{figure}

\begin{code}
apply-lambda : ∀{A}{B}{W}{N′}{𝒫}
  → 𝒱⟦ A ⟧ W ∷ 𝒱⟦ A ⇒ B ⟧ (ƛ N′) ∷ 𝒫 ⊢ᵒ 𝒱⟦ A ⇒ B ⟧ (ƛ N′)
  → Value W
  → 𝒱⟦ A ⟧ W ∷ 𝒱⟦ A ⇒ B ⟧ (ƛ N′) ∷ 𝒫 ⊢ᵒ ℰ⟦ B ⟧ (ƛ N′ · W)
apply-lambda {A}{B}{W}{N′}{𝒫} ⊢𝒱V w = 
  let 𝒫₄ = 𝒱⟦ A ⟧ W ∷ 𝒱⟦ A ⇒ B ⟧ (ƛ N′) ∷ 𝒫 in
  let prog : 𝒫₄ ⊢ᵒ progress B (ƛ N′ · W)
      prog = inj₂ᵒ (constᵒI (_ , (β-ƛ w))) in
  let pres : 𝒫₄ ⊢ᵒ preservation B (ƛ N′ · W)
      pres = Λᵒ[ N ] →ᵒI (constᵒE Zᵒ λ {r →
               let ⊢▷ℰN′W : 𝒫₄ ⊢ᵒ ▷ᵒ (ℰ⟦ B ⟧ (N′ [ W ]))
                   ⊢▷ℰN′W = appᵒ (instᵒ (substᵒ 𝒱-fun ⊢𝒱V) W) (monoᵒ Zᵒ) in
               Sᵒ (subst (λ N → 𝒫₄ ⊢ᵒ ▷ᵒ (ℰ⟦ B ⟧ N)) (sym (deterministic r (β-ƛ w))) ⊢▷ℰN′W)}) in
  ℰ-intro prog pres
\end{code}

\begin{code}
GoodApp : Type → Type → Setᵒ
GoodApp A B = (∀ᵒ[ V ] ∀ᵒ[ W ] (𝒱⟦ A ⇒ B ⟧ V →ᵒ 𝒱⟦ A ⟧ W →ᵒ ℰ⟦ B ⟧ (V · W)))
\end{code}

\begin{code}
apply-mu : ∀{A}{B}{W}{V′₁}{𝒫}
  → 𝒱⟦ A ⟧ W ∷ 𝒱⟦ A ⇒ B ⟧ (μ V′₁) ∷ ▷ᵒ GoodApp A B ∷ 𝒫 ⊢ᵒ 𝒱⟦ A ⇒ B ⟧ (μ V′₁)
  → Value (μ V′₁)
  → Value W
  → 𝒱⟦ A ⟧ W ∷ 𝒱⟦ A ⇒ B ⟧ (μ V′₁) ∷ ▷ᵒ GoodApp A B ∷ 𝒫 ⊢ᵒ ℰ⟦ B ⟧ (μ V′₁ · W)
apply-mu {A = A}{B}{W}{V′₁}{𝒫} ⊢𝒱V v w = 
  let 𝒫₄ = 𝒱⟦ A ⟧ W ∷ 𝒱⟦ A ⇒ B ⟧ (μ V′₁) ∷ ▷ᵒ GoodApp A B ∷ 𝒫 in
  let 𝒫₅ = ((μ V′₁ · W —→ (V′₁ [ μ V′₁ ]) · W) ᵒ) ∷ 𝒫₄ in
  let prog : 𝒫₄ ⊢ᵒ progress B (μ V′₁ · W)
      prog = inj₂ᵒ (constᵒI (_ , β-μ (Value-μ-inv v) w)) in
  let IH : 𝒫₅ ⊢ᵒ ▷ᵒ (∀ᵒ[ V ] ∀ᵒ[ W ] (𝒱⟦ A ⇒ B ⟧ V →ᵒ 𝒱⟦ A ⟧ W →ᵒ ℰ⟦ B ⟧ (V · W)))
      IH = Sᵒ (Sᵒ (Sᵒ Zᵒ)) in
  let ▷ℰV[μV]·W : 𝒫₅ ⊢ᵒ ▷ᵒ ℰ⟦ B ⟧ ((V′₁ [ μ V′₁ ]) · W)
      ▷ℰV[μV]·W =
        let ▷𝒱V[μV] : 𝒫₅ ⊢ᵒ ▷ᵒ (𝒱⟦ A ⇒ B ⟧ (V′₁ [ μ V′₁ ]))
            ▷𝒱V[μV] = proj₂ᵒ (substᵒ 𝒱-μ (Sᵒ (Sᵒ Zᵒ))) in
        let ▷𝒱W : 𝒫₅ ⊢ᵒ ▷ᵒ (𝒱⟦ A ⟧ W)
            ▷𝒱W = monoᵒ (Sᵒ Zᵒ) in
        let P = (λ V → ▷ᵒ (∀ᵒ[ W ] (𝒱⟦ A ⇒ B ⟧ V →ᵒ 𝒱⟦ A ⟧ W →ᵒ ℰ⟦ B ⟧ (V · W)))) in
        appᵒ (▷→ (appᵒ (▷→ (instᵒ (▷∀ (instᵒ{ϕᵃ = P} (▷∀ IH) (V′₁ [ μ V′₁ ]))) W)) ▷𝒱V[μV])) ▷𝒱W in
  let ▷ℰN : ∀ N → (μ V′₁ · W —→ N)ᵒ ∷ 𝒫₄ ⊢ᵒ ▷ᵒ (ℰ⟦ B ⟧ N)
      ▷ℰN N = ⊢ᵒ-sucP Zᵒ λ r → subst (λ N → (μ V′₁ · W —→ N)ᵒ ∷ 𝒫₄ ⊢ᵒ ▷ᵒ (ℰ⟦ B ⟧ N))
                                     (sym (β-μ-inv (Value-μ-inv v) w r)) ▷ℰV[μV]·W in
  let pres : 𝒫₄ ⊢ᵒ preservation B (μ V′₁ · W)
      pres = Λᵒ[ N ] →ᵒI (▷ℰN N) in
  ℰ-intro prog pres
\end{code}

\begin{code}
compatible-app : ∀{Γ}{A}{B}{L}{M} →  Γ ⊨ L ⦂ (A ⇒ B)  →  Γ ⊨ M ⦂ A  →  Γ ⊨ L · M ⦂ B
compatible-app {Γ}{A}{B}{L}{M} ⊨L ⊨M γ = ℰ-bind {F = □· (⟪ γ ⟫ M)} (⊨L γ) (Λᵒ[ V ] →ᵒI (→ᵒI ⊢ℰVM))
  where
  𝒫₁ = λ V → 𝒱⟦ A ⇒ B ⟧ V ∷ (⟪ γ ⟫ L —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ
  ⊢ℰVM : ∀{V} → 𝒫₁ V ⊢ᵒ ℰ⟦ B ⟧ (V · ⟪ γ ⟫ M)
  ⊢ℰVM {V} = ⊢ᵒ-sucP Zᵒ λ 𝒱Vsn → let v = 𝒱⇒Value (A ⇒ B) V 𝒱Vsn in
    ℰ-bind {F = v ·□} (Sᵒ (Sᵒ (⊨M γ))) (Λᵒ[ V ] →ᵒI (→ᵒI ⊢ℰVW))
    where
    𝒫₂ = λ V W → 𝒱⟦ A ⟧ W ∷ (⟪ γ ⟫ M —↠ W)ᵒ ∷ 𝒱⟦ A ⇒ B ⟧ V ∷ (⟪ γ ⟫ L —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ
    𝒫₃ = λ V W → ▷ᵒ (∀ᵒ[ V ] ∀ᵒ[ W ] (𝒱⟦ A ⇒ B ⟧ V →ᵒ 𝒱⟦ A ⟧ W →ᵒ ℰ⟦ B ⟧ (V · W))) ∷ 𝒫₂ V W
    Gen-ℰVW : ∀{V′}{W′} → 𝒫₃ V′ W′ ⊢ᵒ ∀ᵒ[ V ] ∀ᵒ[ W ] (𝒱⟦ A ⇒ B ⟧ V →ᵒ 𝒱⟦ A ⟧ W →ᵒ ℰ⟦ B ⟧ (V · W))
    Gen-ℰVW {V′}{W′} = Λᵒ[ V ] Λᵒ[ W ] →ᵒI (→ᵒI aux)
      where
      aux : ∀{V}{W} → 𝒱⟦ A ⟧ W ∷ 𝒱⟦ A ⇒ B ⟧ V ∷ 𝒫₃ V′ W′ ⊢ᵒ ℰ⟦ B ⟧ (V · W)
      aux {V}{W} =
        let ⊢𝒱V = Sᵒ Zᵒ in let ⊢𝒱W = Zᵒ in
        ⊢ᵒ-sucP ⊢𝒱V λ 𝒱Vsn → ⊢ᵒ-sucP ⊢𝒱W λ 𝒱Wsn →
        let v = 𝒱⇒Value (A ⇒ B) V 𝒱Vsn in let w = 𝒱⇒Value A W 𝒱Wsn in
        𝒱-fun-case ⊢𝒱V (λ { N′ refl → apply-lambda ⊢𝒱V w }) (λ { V′₁ refl → apply-mu ⊢𝒱V v w })
    ⊢ℰVW : ∀{V W} → 𝒫₂ V W ⊢ᵒ ℰ⟦ B ⟧ (V · W)
    ⊢ℰVW {V}{W} = appᵒ (appᵒ (instᵒ (instᵒ (lobᵒ Gen-ℰVW) V) W) (Sᵒ (Sᵒ Zᵒ))) Zᵒ
\end{code}



\begin{code}
compatible-value : ∀{Γ V A} → Γ ⊨ⱽ V ⦂ A  →  Γ ⊨ V ⦂ A
compatible-value {Γ}{V}{A} ⊨V γ = 𝒱⇒ℰ (⊨V γ) 
\end{code}

\subsection{Fundamental Lemma}
\label{sec:fundamental}

\begin{code}
fundamentalⱽ : ∀ {Γ W A} → (Γ ⊢ⱽ W ⦂ A) → (Γ ⊨ⱽ W ⦂ A)
fundamental : ∀ {Γ M A} → (Γ ⊢ M ⦂ A) → (Γ ⊨ M ⦂ A)

fundamentalⱽ {Γ} {.`zero} {.`ℕ} ⊢ⱽzero = compatible-zero
fundamentalⱽ {Γ} {`suc V} {.`ℕ} (⊢ⱽsuc ⊢V) = compatible-sucⱽ{V = V} (fundamentalⱽ ⊢V)
fundamentalⱽ {Γ} {ƛ N} {.(_ ⇒ _)} (⊢ⱽƛ ⊢N) = compatible-lambda{N = N} (fundamental ⊢N)
fundamentalⱽ {Γ} {μ V} {.(_ ⇒ _)} (⊢ⱽμ ⊢V) =
   compatible-μ{V = V} (⊢ⱽ⇒Value ⊢V) (fundamentalⱽ ⊢V)
   
fundamental {Γ} {.(` _)} {A} (⊢` x) = compatible-var x
fundamental {Γ} {`suc M} {.`ℕ} (⊢suc ⊢M) = compatible-suc{M = M} (fundamental ⊢M)
fundamental {Γ} {case L M N} {A} (⊢case ⊢L ⊢M ⊢N) =
   compatible-case{L = L}{M}{N} (fundamental ⊢L) (fundamental ⊢M) (fundamental ⊢N)
fundamental {Γ} {L · M} {A} (⊢· ⊢L ⊢M) =
   compatible-app{L = L}{M} (fundamental ⊢L) (fundamental ⊢M)
fundamental {Γ} {V} {A} (⊢val ⊢V) = compatible-value {V = V} (fundamentalⱽ ⊢V)
\end{code}

\subsection{Proof of Semantic Type Safety}
\label{sec:proof-sem-safety}


\begin{code}
sem-type-safety : ∀ {A} → (M N : Term) → (r : M —↠ N) → # (ℰ⟦ A ⟧ M) (suc (len r))
  → Value N  ⊎  ∃[ N′ ] (N —→ N′)
sem-type-safety {A} M .M (.M END) (inj₁ 𝒱M , presM) = inj₁ (𝒱⇒Value A M 𝒱M)
sem-type-safety {A} M .M (.M END) (inj₂ r , presM) = inj₂ r
sem-type-safety {A} M N (_—→⟨_⟩_ .M {M′} M→M′ M′→N) (_ , pres) =
    let ℰM′ : # (ℰ⟦ A ⟧ M′) (suc (len M′→N))
        ℰM′ = pres M′ (suc (suc (len M′→N))) ≤-refl M→M′ in
    sem-type-safety M′ N M′→N ℰM′
\end{code}

\begin{code}
type-safety : ∀ {A} → (M N : Term) → [] ⊢ M ⦂ A → M —↠ N → Value N  ⊎ (∃[ N′ ] (N —→ N′))
type-safety M N ⊢M M—↠N =
  let ℰM = ⊢ᵒ-elim (fundamental ⊢M id) (suc (len M—↠N)) tt in
  sem-type-safety M N M—↠N ℰM 
\end{code}
