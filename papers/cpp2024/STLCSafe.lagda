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

\end{code}
\end{comment}

\subsection{Compatibility Lemmas}


\begin{code}
compatible-value : ∀{Γ V A}
   → Γ ⊨ⱽ V ⦂ A
     ----------
   → Γ ⊨ V ⦂ A
compatible-value {Γ}{V}{A} ⊨V γ = 𝒱⇒ℰ (⊨V γ) 
\end{code}

\begin{code}
compatible-zero : ∀{Γ}
     -----------------
   → Γ ⊨ⱽ `zero ⦂ `ℕ
compatible-zero {Γ} γ = ⊢ᵒ-intro λ {zero x → tt; (suc i) x → ttᵖ}
\end{code}


\begin{code}
compatible-suc : ∀{Γ}{M}
   → Γ ⊨ M ⦂ `ℕ
     ----------------
   → Γ ⊨ `suc M ⦂ `ℕ
compatible-suc {Γ}{M} ⊨M γ = ⊢ℰsM
 where
 ⊢ℰsM : 𝓖⟦ Γ ⟧ γ ⊢ᵒ ℰ⟦ `ℕ ⟧ (⟪ γ ⟫ (`suc M))
 ⊢ℰsM = ℰ-bind {F = suc□} (⊨M γ) (Λᵒ[ V ] →ᵒI (→ᵒI ⊢ℰsucV))
  where
  𝒫₁ = λ V → 𝒱⟦ `ℕ ⟧ V ∷ (⟪ γ ⟫ M —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ
  ⊢ℰsucV : ∀{V} → 𝒫₁ V ⊢ᵒ ℰ⟦ `ℕ ⟧ (`suc V)
  ⊢ℰsucV {V} = 𝒱⇒ℰ (substᵒ (≡ᵒ-sym 𝒱-suc) Zᵒ)
\end{code}

\begin{code}
compatible-sucⱽ : ∀{Γ}{V}
   → Γ ⊨ⱽ V ⦂ `ℕ
     ----------------
   → Γ ⊨ⱽ `suc V ⦂ `ℕ
compatible-sucⱽ {Γ}{V} ⊨V γ = substᵒ (≡ᵒ-sym 𝒱-suc) (⊨V γ)
\end{code}

\begin{code}
lookup-𝓖 : (Γ : List Type) → (γ : Subst)  →  ∀ {A}{y} → (Γ ∋ y ⦂ A)  →  𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝒱⟦ A ⟧ (γ y)
lookup-𝓖 (B ∷ Γ) γ {A} {zero} refl = Zᵒ
lookup-𝓖 (B ∷ Γ) γ {A} {suc y} ∋y = Sᵒ (lookup-𝓖 Γ (λ x → γ (suc x)) ∋y) 
\end{code}

\begin{code}
compatible-var : ∀ {Γ A x}
  → Γ ∋ x ⦂ A
    -----------
  → Γ ⊨ ` x ⦂ A
compatible-var {Γ}{A}{x} ∋x γ rewrite sub-var γ x = 𝒱⇒ℰ (lookup-𝓖 Γ γ ∋x)
\end{code}

\begin{code}
compatible-lambda : ∀{Γ}{A}{B}{N}
   → (A ∷ Γ) ⊨ N ⦂ B
     -------------------
   → Γ ⊨ⱽ (ƛ N) ⦂ (A ⇒ B)
compatible-lambda {Γ}{A}{B}{N} ⊨N γ = ⊢𝒱λN
 where
 ⊢𝒱λN : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝒱⟦ A ⇒ B ⟧ (ƛ (⟪ ext γ ⟫ N))
 ⊢𝒱λN = (substᵒ (≡ᵒ-sym 𝒱-fun) (Λᵒ[ W ] →ᵒI ▷𝓔N[W]))
  where
  ▷𝓔N[W] : ∀{W} → ▷ᵒ 𝒱⟦ A ⟧ W ∷ 𝓖⟦ Γ ⟧ γ  ⊢ᵒ  ▷ᵒ ℰ⟦ B ⟧ ((⟪ ext γ ⟫ N) [ W ])
  ▷𝓔N[W] {W} = appᵒ (Sᵒ (▷→ (monoᵒ (→ᵒI (⊨N (W • γ)))))) Zᵒ
\end{code}

\begin{code}
compatible-app : ∀{Γ}{A}{B}{L}{M}
   → Γ ⊨ L ⦂ (A ⇒ B)
   → Γ ⊨ M ⦂ A
     -------------------
   → Γ ⊨ L · M ⦂ B
compatible-app {Γ}{A}{B}{L}{M} ⊨L ⊨M γ = ⊢ℰLM
 where
 ⊢ℰLM : 𝓖⟦ Γ ⟧ γ ⊢ᵒ ℰ⟦ B ⟧ (⟪ γ ⟫ (L · M))
 ⊢ℰLM = ℰ-bind {F = □· (⟪ γ ⟫ M)} (⊨L γ) (Λᵒ[ V ] →ᵒI (→ᵒI ⊢ℰVM))
  where
  𝒫₁ = λ V → 𝒱⟦ A ⇒ B ⟧ V ∷ (⟪ γ ⟫ L —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ
  ⊢ℰVM : ∀{V} → 𝒫₁ V ⊢ᵒ ℰ⟦ B ⟧ (V · ⟪ γ ⟫ M)
  ⊢ℰVM {V} = ⊢ᵒ-sucP Zᵒ λ 𝒱Vsn →
       let v = 𝒱⇒Value (A ⇒ B) V 𝒱Vsn in
       let 𝒫₁⊢ℰM : 𝒫₁ V ⊢ᵒ ℰ⟦ A ⟧ (⟪ γ ⟫ M)
           𝒫₁⊢ℰM = Sᵒ (Sᵒ (⊨M γ)) in
       ℰ-bind {F = v ·□} 𝒫₁⊢ℰM (Λᵒ[ V ] →ᵒI (→ᵒI ⊢ℰVW))
   where
   𝒫₂ = λ V W → 𝒱⟦ A ⟧ W ∷ (⟪ γ ⟫ M —↠ W)ᵒ ∷ 𝒱⟦ A ⇒ B ⟧ V ∷ (⟪ γ ⟫ L —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ
   𝒫₃ = λ V W → ▷ᵒ (∀ᵒ[ V ] ∀ᵒ[ W ] (𝒱⟦ A ⇒ B ⟧ V →ᵒ 𝒱⟦ A ⟧ W →ᵒ ℰ⟦ B ⟧ (V · W))) ∷ 𝒫₂ V W


   Gen-ℰVW′ : ∀{V′}{W′} → 𝒫₃ V′ W′ ⊢ᵒ ∀ᵒ[ V ] ∀ᵒ[ W ] (𝒱⟦ A ⇒ B ⟧ V →ᵒ 𝒱⟦ A ⟧ W →ᵒ ℰ⟦ B ⟧ (V · W))
   Gen-ℰVW′ {V′}{W′} = Λᵒ[ V ] Λᵒ[ W ] →ᵒI (→ᵒI aux)
    where
    aux : ∀{V}{W} → 𝒱⟦ A ⟧ W ∷ 𝒱⟦ A ⇒ B ⟧ V ∷ 𝒫₃ V′ W′ ⊢ᵒ ℰ⟦ B ⟧ (V · W)
    aux {V}{W} =
     let ⊢𝒱V : 𝒱⟦ A ⟧ W ∷ 𝒱⟦ A ⇒ B ⟧ V ∷ 𝒫₃ V′ W′ ⊢ᵒ 𝒱⟦ A ⇒ B ⟧ V
         ⊢𝒱V = Sᵒ Zᵒ in
     let ⊢𝒱W : 𝒱⟦ A ⟧ W ∷ 𝒱⟦ A ⇒ B ⟧ V ∷ 𝒫₃ V′ W′ ⊢ᵒ 𝒱⟦ A ⟧ W
         ⊢𝒱W = Zᵒ in
     ⊢ᵒ-sucP ⊢𝒱V λ 𝒱Vsn →
     ⊢ᵒ-sucP ⊢𝒱W λ 𝒱Wsn →
     let v = 𝒱⇒Value (A ⇒ B) V 𝒱Vsn in
     let w = 𝒱⇒Value A W 𝒱Wsn in
     let Case-λ = λ {N′ refl 𝒱W→ℰNW →
                   let 𝒫₄ = 𝒱⟦ A ⟧ W ∷ 𝒱⟦ A ⇒ B ⟧ (ƛ N′) ∷ 𝒫₃ V′ W′ in
                   let prog : 𝒫₄ ⊢ᵒ progress B (ƛ N′ · W)
                       prog = inj₂ᵒ (constᵒI (_ , (β-ƛ w))) in
                     let pres : 𝒫₄ ⊢ᵒ preservation B (ƛ N′ · W)
                         pres = Λᵒ[ N ] →ᵒI (constᵒE Zᵒ λ {r →
                                let ⊢▷ℰN′W : 𝒫₄ ⊢ᵒ ▷ᵒ (ℰ⟦ B ⟧ (N′ [ W ]))
                                    ⊢▷ℰN′W = appᵒ 𝒱W→ℰNW (monoᵒ ⊢𝒱W) in
                                let eq = deterministic r (β-ƛ w) in
                                Sᵒ (subst (λ N → 𝒫₄ ⊢ᵒ ▷ᵒ (ℰ⟦ B ⟧ N)) (sym eq) ⊢▷ℰN′W)}) in
                   ℰ-intro prog pres} in
     let Case-μ = λ {V′₁ refl ▷𝒱V′[V] →
                  let 𝒫₄ = 𝒱⟦ A ⟧ W ∷ 𝒱⟦ A ⇒ B ⟧ (μ V′₁) ∷ 𝒫₃ V′ W′ in
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
                        appᵒ (▷→ (appᵒ (▷→ (instᵒ (▷∀ (instᵒ-new P (▷∀ IH) (V′₁ [ μ V′₁ ]))) W)) ▷𝒱V[μV])) ▷𝒱W in
                  let ▷ℰN : ∀ N → (μ V′₁ · W —→ N)ᵒ ∷ 𝒫₄ ⊢ᵒ ▷ᵒ (ℰ⟦ B ⟧ N)
                      ▷ℰN N = ⊢ᵒ-sucP Zᵒ λ r → subst (λ N → (μ V′₁ · W —→ N)ᵒ ∷ 𝒫₄ ⊢ᵒ ▷ᵒ (ℰ⟦ B ⟧ N))
                                                     (sym (β-μ-inv (Value-μ-inv v) w r)) ▷ℰV[μV]·W in
                  let pres : 𝒫₄ ⊢ᵒ preservation B (μ V′₁ · W)
                      pres = Λᵒ[ N ] →ᵒI (▷ℰN N) in
                  ℰ-intro prog pres } in
     𝒱-fun-elim ⊢𝒱V Case-λ Case-μ

   Gen-ℰVW : ∀{V}{W} → 𝒫₂ V W ⊢ᵒ ∀ᵒ[ V ] ∀ᵒ[ W ] (𝒱⟦ A ⇒ B ⟧ V →ᵒ 𝒱⟦ A ⟧ W →ᵒ ℰ⟦ B ⟧ (V · W))
   Gen-ℰVW = lobᵒ Gen-ℰVW′
                 
   ⊢ℰVW : ∀{V W} → 𝒫₂ V W ⊢ᵒ ℰ⟦ B ⟧ (V · W)
   ⊢ℰVW {V}{W} = appᵒ (appᵒ (instᵒ (instᵒ Gen-ℰVW V) W) (Sᵒ (Sᵒ Zᵒ))) Zᵒ
\end{code}

\begin{code}
subst-preserves-value : ∀ σ V → Value V → Value (⟪ σ ⟫ V)
subst-preserves-value σ .(ƛ _) V-ƛ = V-ƛ
subst-preserves-value σ .`zero V-zero = V-zero
subst-preserves-value σ (`suc V) (V-suc v) = V-suc (subst-preserves-value σ V v)
subst-preserves-value σ (μ V) (V-μ v) = V-μ (subst-preserves-value (ext σ) V v)
\end{code}

\begin{code}
value-ℰ⇒𝒱 : ∀{V}{A}{n} → Value V → # (ℰ⟦ A ⟧ V) (suc n) → # (𝒱⟦ A ⟧ V) (suc n)
value-ℰ⇒𝒱 v (inj₁ 𝒱V , pres) = 𝒱V
value-ℰ⇒𝒱 v (inj₂ (_ , r) , pres) = ⊥-elim (value-irreducible v r)
\end{code}

\begin{code}
compatible-μ : ∀{Γ}{A}{B}{V}
   → Value V
   → ((A ⇒ B) ∷ Γ) ⊨ⱽ V ⦂ (A ⇒ B)
     --------------------
   → Γ ⊨ⱽ (μ V) ⦂ (A ⇒ B)
compatible-μ {Γ}{A}{B}{V} v ⊨V γ = 𝒱μ
 where
 μγV = μ (⟪ ext γ ⟫ V)
 
 𝒱μV⇒𝒱V : 𝒱⟦ A ⇒ B ⟧ μγV  ∷  ▷ᵒ 𝒱⟦ A ⇒ B ⟧ μγV  ∷  𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝒱⟦ A ⇒ B ⟧ (⟪ μγV • γ ⟫ V)
 𝒱μV⇒𝒱V = ⊢ᵒ-intro λ {n (𝒱μγVn , _ , 𝓖γn) → ⊢ᵒ-elim (⊨V (μγV • γ)) n (𝒱μγVn , 𝓖γn)}
      
 ▷𝒱V : ▷ᵒ (𝒱⟦ A ⇒ B ⟧ μγV) ∷ 𝓖⟦ Γ ⟧ γ ⊢ᵒ ▷ᵒ (𝒱⟦ A ⇒ B ⟧ (⟪ μγV • γ ⟫ V))
 ▷𝒱V = ▷→▷ Zᵒ 𝒱μV⇒𝒱V

 𝒱μ : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝒱⟦ A ⇒ B ⟧ μγV
 𝒱μ = lobᵒ (substᵒ (≡ᵒ-sym 𝒱-μ) (constᵒI (subst-preserves-value (ext γ) _ v) ,ᵒ ▷𝒱V))
\end{code}

\begin{code}
𝒱ℕ-inv : ∀{n}{Cont : Set} → #(𝒱⟦ `ℕ ⟧ V) (suc n) → (V ≡ `zero → Cont) → (∀ V′ → V ≡ `suc V′ → Cont) → Cont
𝒱ℕ-inv {`zero}{n}{Cont} 𝒱V contz conts = contz refl
𝒱ℕ-inv {`suc V′}{n}{Cont} 𝒱V contz conts = conts V′ refl 
\end{code}

\begin{code}
compatible-case : ∀{Γ L M N A}
  → Γ ⊨ L ⦂ `ℕ
  → Γ ⊨ M ⦂ A
  → `ℕ ∷ Γ ⊨ N ⦂ A
    ------------------
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


\subsection{Fundamental Lemma}

\begin{code}
fundamental : ∀ {Γ M A} → (Γ ⊢ M ⦂ A) → (Γ ⊨ M ⦂ A)
fundamentalⱽ : ∀ {Γ W A} → (Γ ⊢ⱽ W ⦂ A) → (Γ ⊨ⱽ W ⦂ A)
fundamental {Γ} {.(` _)} {A} (⊢` x) = compatible-var x
fundamental {Γ} {`suc M} {.`ℕ} (⊢suc ⊢M) = compatible-suc{M = M} (fundamental ⊢M)
fundamental {Γ} {case L M N} {A} (⊢case ⊢L ⊢M ⊢N) =
   compatible-case{L = L}{M}{N} (fundamental ⊢L) (fundamental ⊢M) (fundamental ⊢N)
fundamental {Γ} {L · M} {A} (⊢· ⊢L ⊢M) = compatible-app{L = L}{M} (fundamental ⊢L) (fundamental ⊢M)
fundamental {Γ} {V} {A} (⊢val ⊢V) = compatible-value {V = V} (fundamentalⱽ ⊢V)
fundamentalⱽ {Γ} {.`zero} {.`ℕ} ⊢ⱽzero = compatible-zero
fundamentalⱽ {Γ} {`suc V} {.`ℕ} (⊢ⱽsuc ⊢V) = compatible-sucⱽ{V = V} (fundamentalⱽ ⊢V)
fundamentalⱽ {Γ} {ƛ N} {.(_ ⇒ _)} (⊢ⱽƛ ⊢N) = compatible-lambda{N = N} (fundamental ⊢N)
fundamentalⱽ {Γ} {μ V} {.(_ ⇒ _)} (⊢ⱽμ ⊢V) = compatible-μ{V = V} (⊢ⱽ⇒Value ⊢V) (fundamentalⱽ ⊢V)
\end{code}
