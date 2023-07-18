\begin{comment}
\begin{code}
{-# OPTIONS --rewriting #-}

module cpp2024.STLCBind where

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

\end{code}
\end{comment}

\subsection{Bind Lemma}

\begin{code}
𝒱V→ℰF[V] : Type → Type → Frame → Term → Setᵒ
𝒱V→ℰF[V] A B F M = ∀ᵒ[ V ] (M —↠ V)ᵒ →ᵒ 𝒱⟦ B ⟧ V →ᵒ ℰ⟦ A ⟧ (F ⟦ V ⟧)

ℰ-bind-M : Type → Type → Frame → Term → Setᵒ
ℰ-bind-M A B F M = ℰ⟦ B ⟧ M →ᵒ 𝒱V→ℰF[V] A B F M →ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)

ℰ-bind-prop : Type → Type → Frame → Setᵒ
ℰ-bind-prop A B F = ∀ᵒ[ M ] ℰ-bind-M A B F M

𝒱V→ℰF[V]-expansion : ∀{𝒫}{A}{B}{F}{M}{M′}
   → M —→ M′
   → 𝒫 ⊢ᵒ 𝒱V→ℰF[V] A B F M
     -----------------------
   → 𝒫 ⊢ᵒ 𝒱V→ℰF[V] A B F M′
𝒱V→ℰF[V]-expansion {𝒫}{A}{B}{F}{M}{M′} M→M′ 𝒱V→ℰF[V][M] =
   Λᵒ[ V ]
    let M′→V→ℰFV : 𝒱⟦ B ⟧ V ∷ (M′ —↠ V)ᵒ ∷ 𝒫 ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ V ⟧)
        M′→V→ℰFV = ⊢ᵒ-sucP (Sᵒ Zᵒ) λ M′→V → 
                     let M—↠V = constᵒI (M —→⟨ M→M′ ⟩ M′→V) in
                     let M→V→ℰFV = Sᵒ(Sᵒ(instᵒ 𝒱V→ℰF[V][M] V)) in
                     appᵒ (appᵒ M→V→ℰFV M—↠V) Zᵒ in
    →ᵒI (→ᵒI M′→V→ℰFV)
\end{code}


\begin{code}
ℰ-bind-aux : ∀{𝒫}{A}{B}{F} → 𝒫 ⊢ᵒ ℰ-bind-prop A B F
ℰ-bind-aux {𝒫}{A}{B}{F} = lobᵒ (Λᵒ[ M ] →ᵒI (→ᵒI Goal))
  where
  Goal : ∀{M} → (𝒱V→ℰF[V] A B F M) ∷ ℰ⟦ B ⟧ M ∷ ▷ᵒ ℰ-bind-prop A B F ∷ 𝒫
                 ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)
  Goal{M} =
   caseᵒ (ℰ-progress (Sᵒ Zᵒ)) Mval Mred 
   where
   𝒫′ = (𝒱V→ℰF[V] A B F M) ∷ ℰ⟦ B ⟧ M ∷ ▷ᵒ ℰ-bind-prop A B F ∷ 𝒫

   Mval : 𝒱⟦ B ⟧ M ∷ 𝒫′ ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)
   Mval =
     let 𝒱V→ℰF[V][M] = λ V → (M —↠ V)ᵒ →ᵒ 𝒱⟦ B ⟧ V →ᵒ ℰ⟦ A ⟧ (F ⟦ V ⟧) in
     appᵒ (appᵒ (instᵒ{ϕ = 𝒱V→ℰF[V][M]} (Sᵒ Zᵒ) M) (constᵒI (M END))) Zᵒ

   Mred : (reducible M)ᵒ ∷ 𝒫′ ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)
   Mred = ℰ-intro progressMred preservationMred
    where
    progressMred : (reducible M)ᵒ ∷ 𝒫′ ⊢ᵒ progress A (F ⟦ M ⟧)
    progressMred = inj₂ᵒ (constᵒE Zᵒ λ {(M′ , M→M′) → constᵒI (_ , (ξ F M→M′))})

    preservationMred : (reducible M)ᵒ ∷ 𝒫′ ⊢ᵒ preservation A (F ⟦ M ⟧)
    preservationMred = (constᵒE Zᵒ λ redM →
                Sᵒ (Λᵒ[ N ] →ᵒI (constᵒE Zᵒ λ FM→N →
                                          Sᵒ (redM⇒▷ℰN redM FM→N))))
     where
     redM⇒▷ℰN : ∀{N} → reducible M → (F ⟦ M ⟧ —→ N) → 𝒫′ ⊢ᵒ ▷ᵒ (ℰ⟦ A ⟧ N)
     redM⇒▷ℰN {N} rM FM→N =
      let finv = frame-inv2{M}{N}{F} rM FM→N in
      let M′ = proj₁ finv in
      let M→M′ = proj₁ (proj₂ finv) in
      let N≡ = proj₂ (proj₂ finv) in
      let ▷ℰM′ : 𝒫′ ⊢ᵒ ▷ᵒ ℰ⟦ B ⟧ M′
          ▷ℰM′ = appᵒ (instᵒ{ϕ = λ N → (M —→ N)ᵒ →ᵒ ▷ᵒ (ℰ⟦ B ⟧ N)}
                        (ℰ-preservation (Sᵒ Zᵒ)) M′)
                      (constᵒI M→M′) in
      let ▷M′→V→𝒱V→ℰFV : 𝒫′ ⊢ᵒ ▷ᵒ (𝒱V→ℰF[V] A B F M′)
          ▷M′→V→𝒱V→ℰFV = monoᵒ (𝒱V→ℰF[V]-expansion{𝒫′}{A}{B} M→M′ Zᵒ) in
      let IH : 𝒫′ ⊢ᵒ ▷ᵒ ℰ-bind-prop A B F
          IH = Sᵒ (Sᵒ Zᵒ) in
      let ▷ℰFM′ : 𝒫′ ⊢ᵒ ▷ᵒ (ℰ⟦ A ⟧ (F ⟦ M′ ⟧))
          ▷ℰFM′ = frame-prop-lemma IH ▷ℰM′ ▷M′→V→𝒱V→ℰFV in
      subst (λ N → 𝒫′ ⊢ᵒ ▷ᵒ ℰ⟦ A ⟧ N) (sym N≡) ▷ℰFM′
      where
      frame-prop-lemma : ∀{𝒫}{A}{B}{M}{F}
         → 𝒫 ⊢ᵒ ▷ᵒ ℰ-bind-prop A B F  →  𝒫 ⊢ᵒ ▷ᵒ ℰ⟦ B ⟧ M
         → 𝒫 ⊢ᵒ ▷ᵒ 𝒱V→ℰF[V] A B F M   →  𝒫 ⊢ᵒ ▷ᵒ (ℰ⟦ A ⟧ (F ⟦ M ⟧))
      frame-prop-lemma{𝒫}{A}{B}{M}{F} IH ℰM V→FV =
       appᵒ(▷→ (appᵒ(▷→ (instᵒ(▷∀{ϕᵃ = λ M → ℰ-bind-M A B F M} IH) M)) ℰM)) V→FV

ℰ-bind : ∀{𝒫}{A}{B}{F}{M}
   → 𝒫 ⊢ᵒ ℰ⟦ B ⟧ M
   → 𝒫 ⊢ᵒ (∀ᵒ[ V ] (M —↠ V)ᵒ →ᵒ 𝒱⟦ B ⟧ V →ᵒ ℰ⟦ A ⟧ (F ⟦ V ⟧))
     ----------------------------------------------------------
   → 𝒫 ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)
ℰ-bind {𝒫}{A}{B}{F}{M} ⊢ℰM ⊢𝒱V→ℰFV =
  appᵒ (appᵒ (instᵒ{𝒫}{ϕ = λ M → ℰ-bind-M A B F M} ℰ-bind-aux M) ⊢ℰM) ⊢𝒱V→ℰFV
\end{code}

