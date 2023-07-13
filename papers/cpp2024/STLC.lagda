\begin{comment}
\begin{code}
{-# OPTIONS --rewriting #-}

module cpp2024.STLC where

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

\end{code}
\end{comment}

\section{Semantic Safety of the STLC with Recursion}



\begin{code}
data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ  : Type
\end{code}


\begin{code}
data Op : Set where
  op-lam : Op
  op-app : Op
  op-zero : Op
  op-suc : Op
  op-case : Op
  op-rec : Op
\end{code}

\begin{code}
sig : Op → List Sig
sig op-lam = (ν ■) ∷ []
sig op-app = ■ ∷ ■ ∷ []
sig op-zero = []
sig op-suc = ■ ∷ []
sig op-case = ■ ∷ ■ ∷ (ν ■) ∷ []
sig op-rec = (ν ■) ∷ []
\end{code}

\begin{code}
open import rewriting.AbstractBindingTree Op sig renaming (ABT to Term) public

variable L L′ M M′ N N′ V V′ W W′ : Term

pattern ƛ N  = op-lam ⦅ cons (bind (ast N)) nil ⦆

infixl 7  _·_
pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆

pattern `zero = op-zero ⦅ nil ⦆
pattern `suc M = op-suc ⦅ cons (ast M) nil ⦆

pattern case L M N = op-case ⦅ cons (ast L) (cons (ast M) (cons (bind (ast N)) nil)) ⦆

pattern μ N = op-rec ⦅ cons (bind (ast N)) nil ⦆
\end{code}


\subsection{Dynamic Semantics of STLC}

\begin{code}
data Value : Term → Set where
  V-ƛ : Value (ƛ N)
  V-zero : Value `zero
  V-suc : Value V → Value (`suc V)
  V-μ : Value V → Value (μ V)
\end{code}

\begin{code}
value : ∀{V} → Value V → Term
value {V} v = V
\end{code}

\begin{code}
infix  6 □·_
infix  6 _·□

data Frame : Set where

  □·_ : 
      Term
      -----
    → Frame

  _·□ : 
      Value V
      -------
    → Frame

  suc□ : Frame

{- Plug an expression into a frame. -}

_⟦_⟧ : Frame → Term → Term
(□· M) ⟦ L ⟧        =  L · M
(v ·□) ⟦ M ⟧        =  value v · M
suc□ ⟦ M ⟧          = `suc M

{- Possibly-empty Frame -}

data PEFrame : Set where
  `_ : Frame → PEFrame
  □ : PEFrame

_⦉_⦊ : PEFrame → Term → Term
(` F) ⦉ M ⦊ = F ⟦ M ⟧
□ ⦉ M ⦊ = M

{- Reduction -}

infix 2 _—→_
data _—→_ : Term → Term → Set where

  ξξ : ∀ {M N : Term} {M′ N′ : Term}
    → (F : Frame)
    → M′ ≡ F ⟦ M ⟧
    → N′ ≡ F ⟦ N ⟧
    → M —→ N
      --------
    → M′ —→ N′

  β-ƛ : 
      Value W
      --------------------
    → (ƛ N) · W —→ N [ W ]

  β-zero : 
      -------------------
      case `zero M N —→ M

  β-suc : 
      Value V
      ----------------------------
    → case (`suc V) M N —→ N [ V ]

  β-μ :
      Value V
    → Value W
      ---------------------------
    → (μ V) · W —→ V [ μ V ] · W
\end{code}

\begin{code}
pattern ξ F M—→N = ξξ F refl refl M—→N

ξ′ : ∀ {M N : Term} {M′ N′ : Term}
    → (F : PEFrame)
    → M′ ≡ F ⦉ M ⦊
    → N′ ≡ F ⦉ N ⦊
    → M —→ N
      --------
    → M′ —→ N′
ξ′ (` F) refl refl M→N = ξ F M→N
ξ′ □ refl refl M→N = M→N

{- Reflexive and transitive closure of reduction -}

infixr 1 _++_
infix  2 _—↠_
infixr 2 _—→⟨_⟩_
infixr 2 _—↠⟨_⟩_
infix  3 _END

data _—↠_ : Term → Term → Set where
  _END : (M : Term)
      ---------
    → M —↠ M

  _—→⟨_⟩_ : (L : Term) {M N : Term}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N

{- Convenience function to build a sequence of length one. -}

unit : ∀ {M N : Term} → (M —→ N) → (M —↠ N)
unit {M = M} {N = N} M—→N  =  M —→⟨ M—→N ⟩ (N END)

{- Apply ξ to each element of a sequence -}

ξ* : ∀ {M N : Term} → (F : Frame) → M —↠ N → F ⟦ M ⟧ —↠ F ⟦ N ⟧
ξ* F (M END) = F ⟦ M ⟧ END
ξ* F (L —→⟨ L—→M ⟩ M—↠N) = (F ⟦ L ⟧ —→⟨ ξ F L—→M ⟩ ξ* F M—↠N)

ξ′* : ∀{M N} → (F : PEFrame) → M —↠ N → F ⦉ M ⦊ —↠ F ⦉ N ⦊
ξ′* {M} {N} (` F) M→N = ξ* F M→N
ξ′* {M} {N} □ M→N = M→N

{- Concatenate two sequences. -}

_++_ : ∀ {L M N : Term} → L —↠ M → M —↠ N → L —↠ N
(M END) ++ M—↠N                =  M—↠N
(L —→⟨ L—→M ⟩ M—↠N) ++ N—↠P  =  L —→⟨ L—→M ⟩ (M—↠N ++ N—↠P)

{- Alternative notation for sequence concatenation. -}

_—↠⟨_⟩_ : (L : Term) {M N : Term}
  → L —↠ M
  → M —↠ N
    ---------
  → L —↠ N
L —↠⟨ L—↠M ⟩ M—↠N  =  L—↠M ++ M—↠N

reducible : (M : Term) → Set
reducible M = ∃[ N ] (M —→ N)

irred : (M : Term) → Set
irred M = ¬ reducible M

len : ∀{M N : Term} → (M→N : M —↠ N) → ℕ
len (_ END) = 0
len (_ —→⟨ x ⟩ red) = suc (len red)

len-concat : ∀ {L}{M}{N} (s : L —↠ M) (r : M —↠ N)
  → len (s ++ r) ≡ len s + len r
len-concat (_ END) r = refl
len-concat (_ —→⟨ x ⟩ s) r rewrite len-concat s r = refl

_⇓ : Term → Set
M ⇓ = ∃[ V ] (M —↠ V) × Value V

_⇑ : Term → Set
M ⇑ = ∀ k → ∃[ N ] Σ[ r ∈ M —↠ N ] k ≡ len r

value-irreducible : ∀ {V M : Term} → Value V → ¬ (V —→ M)
value-irreducible v V—→M = {!!}


postulate deterministic : ∀{M N N′} → M —→ N → M —→ N′ → N ≡ N′

postulate frame-inv2 : ∀{L N : Term}{F} → reducible L → F ⟦ L ⟧ —→ N → ∃[ L′ ] ((L —→ L′) × (N ≡ F ⟦ L′ ⟧))

\end{code}

\subsection{Type System of STLC}

\begin{code}
infix 3 _⊢_⦂_
data _⊢_⦂_ : List Type → Term → Type → Set

infix 3 _⊢ⱽ_⦂_
data _⊢ⱽ_⦂_ : List Type → Term → Type → Set

data _⊢ⱽ_⦂_ where

  ⊢ⱽzero : ∀ {Γ}
      --------------
    → Γ ⊢ⱽ `zero ⦂ `ℕ

  ⊢ⱽsuc : ∀ {Γ V}
    → Γ ⊢ⱽ V ⦂ `ℕ
      ---------------
    → Γ ⊢ⱽ `suc V ⦂ `ℕ

  ⊢ⱽƛ : ∀ {Γ N A B}
    → (A ∷ Γ) ⊢ N ⦂ B
      -----------------
    → Γ ⊢ⱽ ƛ N ⦂ (A ⇒ B)

  ⊢ⱽμ : ∀ {Γ V A B}
    → (A ⇒ B ∷ Γ) ⊢ⱽ V ⦂ A ⇒ B
      ------------------------
    → Γ ⊢ⱽ μ V ⦂ A ⇒ B

data _⊢_⦂_ where

  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ⦂ A

  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ⦂ `ℕ
      ---------------
    → Γ ⊢ `suc M ⦂ `ℕ
    
  ⊢case : ∀{Γ L M N A}
    → Γ ⊢ L ⦂ `ℕ
    → Γ ⊢ M ⦂ A
    → `ℕ ∷ Γ ⊢ N ⦂ A
      ------------------
    → Γ ⊢ case L M N ⦂ A

  ⊢· : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ (A ⇒ B)
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B

  ⊢val : ∀ {Γ V A}
    → Γ ⊢ⱽ V ⦂ A
      ----------
    → Γ ⊢ V ⦂ A
\end{code}

\begin{code}
⊢ⱽ⇒Value : ∀{Γ V A} → Γ ⊢ⱽ V ⦂ A → Value V
⊢ⱽ⇒Value ⊢ⱽzero = V-zero
⊢ⱽ⇒Value (⊢ⱽsuc ⊢V) = V-suc (⊢ⱽ⇒Value ⊢V)
⊢ⱽ⇒Value (⊢ⱽƛ ⊢N) = V-ƛ
⊢ⱽ⇒Value (⊢ⱽμ ⊢V) = V-μ (⊢ⱽ⇒Value ⊢V)
\end{code}

\subsection{Definition of the Logical Relation}

\begin{code}
ℰ⊎𝒱-type : Set
ℰ⊎𝒱-type = (Type × Term) ⊎ (Type × Term)

ℰ⊎𝒱-ctx : Context
ℰ⊎𝒱-ctx = ℰ⊎𝒱-type ∷ []
\end{code}



\begin{code}
ℰˢ⟦_⟧ : Type → Term → Setˢ ℰ⊎𝒱-ctx (cons Now ∅)
ℰˢ⟦ A ⟧ M = (inj₂ (A , M)) ∈ zeroˢ

𝒱ˢ⟦_⟧ : Type → Term → Setˢ ℰ⊎𝒱-ctx (cons Now ∅)
𝒱ˢ⟦ A ⟧ V = (inj₁ (A , V)) ∈ zeroˢ
\end{code}

\begin{code}
pre-ℰ : Type → Term → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)
pre-𝒱 : Type → Term → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)

pre-ℰ A M = (pre-𝒱 A M ⊎ˢ (reducible M)ˢ) ×ˢ (∀ˢ[ N ] (M —→ N)ˢ →ˢ ▷ˢ (ℰˢ⟦ A ⟧ N))

pre-𝒱 `ℕ `zero       = topᵖ ˢ
pre-𝒱 `ℕ (`suc V)    = pre-𝒱 `ℕ V
pre-𝒱 (A ⇒ B) (ƛ N)  = ∀ˢ[ W ] ▷ˢ (𝒱ˢ⟦ A ⟧ W) →ˢ ▷ˢ (ℰˢ⟦ B ⟧ (N [ W ]))
pre-𝒱 (A ⇒ B) (μ V)  = (Value V)ˢ ×ˢ (▷ˢ (𝒱ˢ⟦ A ⇒ B ⟧ (V [ μ V ])))
pre-𝒱 A M            = ⊥ ˢ
\end{code}

\begin{code}
pre-ℰ⊎𝒱 : ℰ⊎𝒱-type → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)
pre-ℰ⊎𝒱 (inj₁ (A , V)) = pre-𝒱 A V
pre-ℰ⊎𝒱 (inj₂ (A , M)) = pre-ℰ A M

ℰ⊎𝒱 : ℰ⊎𝒱-type → Setᵒ
ℰ⊎𝒱 X = μᵒ pre-ℰ⊎𝒱 X
\end{code}

\begin{code}
ℰ⟦_⟧ : Type → Term → Setᵒ
ℰ⟦ A ⟧ M = ℰ⊎𝒱 (inj₂ (A , M))

𝒱⟦_⟧ : Type → Term → Setᵒ
𝒱⟦ A ⟧ V = ℰ⊎𝒱 (inj₁ (A , V))
\end{code}


\begin{code}
progress : Type → Term → Setᵒ
progress A M = 𝒱⟦ A ⟧ M ⊎ᵒ (reducible M)ᵒ

preservation : Type → Term → Setᵒ
preservation A M = ∀ᵒ[ N ] ((M —→ N)ᵒ →ᵒ ▷ᵒ (ℰ⟦ A ⟧ N))
\end{code}

\begin{code}
open import EquivalenceRelation public
\end{code}

\begin{code}
ℰ-stmt : ∀{A}{M} → ℰ⟦ A ⟧ M ≡ᵒ progress A M ×ᵒ preservation A M
ℰ-stmt {A}{M} =
  ℰ⟦ A ⟧ M                                 ⩦⟨ ≡ᵒ-refl refl ⟩
  μᵒ pre-ℰ⊎𝒱 (inj₂ (A , M))               ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 (inj₂ (A , M)) ⟩
  ♯ (pre-ℰ⊎𝒱 (inj₂ (A , M))) (ℰ⊎𝒱 , ttᵖ) ⩦⟨ cong-×ᵒ (cong-⊎ᵒ (≡ᵒ-sym (fixpointᵒ pre-ℰ⊎𝒱 (inj₁ (A , M))))
                                                  (≡ᵒ-refl refl)) (≡ᵒ-refl refl) ⟩
  progress A M ×ᵒ preservation A M         ∎
\end{code}

\begin{code}
ℰ-intro : ∀ {𝒫}{A}{M} → 𝒫 ⊢ᵒ progress A M → 𝒫 ⊢ᵒ preservation A M → 𝒫 ⊢ᵒ ℰ⟦ A ⟧ M
ℰ-intro 𝒫⊢prog 𝒫⊢pres = substᵒ (≡ᵒ-sym ℰ-stmt) (𝒫⊢prog ,ᵒ 𝒫⊢pres)

ℰ-progress : ∀ {𝒫}{A}{M} → 𝒫 ⊢ᵒ ℰ⟦ A ⟧ M → 𝒫 ⊢ᵒ progress A M
ℰ-progress 𝒫⊢ℰM = proj₁ᵒ (substᵒ ℰ-stmt 𝒫⊢ℰM )

ℰ-preservation : ∀ {𝒫}{A}{M} → 𝒫 ⊢ᵒ ℰ⟦ A ⟧ M → 𝒫 ⊢ᵒ preservation A M
ℰ-preservation 𝒫⊢ℰM = proj₂ᵒ (substᵒ ℰ-stmt 𝒫⊢ℰM )
\end{code}

\begin{code}
𝒱-suc : ∀{M} → 𝒱⟦ `ℕ ⟧ (`suc M) ≡ᵒ 𝒱⟦ `ℕ ⟧ M
𝒱-suc {M} = let X = inj₁ (`ℕ , `suc M) in
  𝒱⟦ `ℕ ⟧ (`suc M)              ⩦⟨ ≡ᵒ-refl refl ⟩
  ℰ⊎𝒱 X                         ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X ⟩
  ♯ (pre-ℰ⊎𝒱 X) (ℰ⊎𝒱 , ttᵖ)     ⩦⟨ ≡ᵒ-sym (fixpointᵒ pre-ℰ⊎𝒱 (inj₁ (`ℕ , M))) ⟩ 
  𝒱⟦ `ℕ ⟧ M                     ∎
\end{code}

\begin{code}
𝒱-fun : ∀{A B}{N} → 𝒱⟦ A ⇒ B ⟧ (ƛ N) ≡ᵒ (∀ᵒ[ W ] ((▷ᵒ (𝒱⟦ A ⟧ W)) →ᵒ (▷ᵒ (ℰ⟦ B ⟧ (N [ W ])))))
𝒱-fun {A}{B}{N} =
   let X = (inj₁ (A ⇒ B , ƛ N)) in
   𝒱⟦ A ⇒ B ⟧ (ƛ N)                                         ⩦⟨ ≡ᵒ-refl refl ⟩
   ℰ⊎𝒱 X                                                    ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X ⟩
   ♯ (pre-ℰ⊎𝒱 X) (ℰ⊎𝒱 , ttᵖ)                               ⩦⟨ ≡ᵒ-refl refl ⟩ 
   (∀ᵒ[ W ] ((▷ᵒ (𝒱⟦ A ⟧ W)) →ᵒ (▷ᵒ (ℰ⟦ B ⟧ (N [ W ])))))   ∎
\end{code}

\begin{code}
𝒱-μ : ∀{A B}{V} → 𝒱⟦ A ⇒ B ⟧ (μ V) ≡ᵒ (Value V)ᵒ ×ᵒ (▷ᵒ (𝒱⟦ A ⇒ B ⟧ (V [ μ V ])))
𝒱-μ {A}{B}{V} =
   let X = (inj₁ (A ⇒ B , μ V)) in
   𝒱⟦ A ⇒ B ⟧ (μ V)                                         ⩦⟨ ≡ᵒ-refl refl ⟩
   ℰ⊎𝒱 X                                                    ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X ⟩
   ♯ (pre-ℰ⊎𝒱 X) (ℰ⊎𝒱 , ttᵖ)                               ⩦⟨ ≡ᵒ-refl refl ⟩ 
   (Value V)ᵒ ×ᵒ (▷ᵒ (𝒱⟦ A ⇒ B ⟧ (V [ μ V ])))              ∎
\end{code}

\begin{code}
safe-body : List Setᵒ → Term → Type → Type → Set
safe-body 𝒫 N A B = ∀{W} → 𝒫 ⊢ᵒ (▷ᵒ (𝒱⟦ A ⟧ W)) →ᵒ (▷ᵒ (ℰ⟦ B ⟧ (N [ W ])))

𝒱-fun-elim : ∀{𝒫}{A}{B}{V}{R}
   → 𝒫 ⊢ᵒ 𝒱⟦ A ⇒ B ⟧ V
   → (∀ N → V ≡ ƛ N → safe-body 𝒫 N A B → 𝒫 ⊢ᵒ R)
   → (∀ V′ → V ≡ μ V′ → 𝒫 ⊢ᵒ ▷ᵒ (𝒱⟦ A ⇒ B ⟧ (V′ [ V ])) → 𝒫 ⊢ᵒ R)
    ---------------------------------------------------------------
   → 𝒫 ⊢ᵒ R
𝒱-fun-elim {𝒫}{A}{B}{V}{R} ⊢𝒱V contλ contμ =
  ⊢ᵒ-sucP ⊢𝒱V λ { 𝒱Vsn → aux {V} 𝒱Vsn ⊢𝒱V contλ contμ}
  where
  aux : ∀{V}{n}
     → # (𝒱⟦ A ⇒ B ⟧ V) (suc n)
     → 𝒫 ⊢ᵒ 𝒱⟦ A ⇒ B ⟧ V
     → (∀ N → V ≡ ƛ N → safe-body 𝒫 N A B → 𝒫 ⊢ᵒ R)
     → (∀ V′ → V ≡ μ V′ → 𝒫 ⊢ᵒ ▷ᵒ (𝒱⟦ A ⇒ B ⟧ (V′ [ V ])) → 𝒫 ⊢ᵒ R)
     → 𝒫 ⊢ᵒ R
  aux{ƛ N}{n} 𝒱V ⊢𝒱V contλ contμ = contλ N refl λ {W} →
      instᵒ{P = λ W → (▷ᵒ (𝒱⟦ A ⟧ W)) →ᵒ (▷ᵒ (ℰ⟦ B ⟧ (N [ W ])))}
                 (substᵒ 𝒱-fun ⊢𝒱V) W
  aux{μ V}{n} 𝒱V ⊢𝒱V contλ contμ = contμ V refl (⊢ᵒ-intro
     λ { zero 𝒫k → tt
       ; (suc k) → λ 𝒫sk → let (v , 𝒱V[μV]) = ⊢ᵒ-elim ⊢𝒱V (suc k) 𝒫sk in  𝒱V[μV]})
\end{code}

\begin{code}
𝒱⇒Value : ∀ {k} A M → # (𝒱⟦ A ⟧ M) (suc k) → Value M
𝒱⇒Value `ℕ `zero 𝒱M = V-zero
𝒱⇒Value `ℕ (`suc M) 𝒱M = V-suc (𝒱⇒Value `ℕ M 𝒱M)
𝒱⇒Value (A ⇒ B) (ƛ N) 𝒱M = V-ƛ
𝒱⇒Value (A ⇒ B) (μ V) (v , ▷𝒱V[μV]) = V-μ v
\end{code}

\begin{code}
𝒱⇒ℰ : ∀{A}{𝒫}{V}
   → 𝒫 ⊢ᵒ 𝒱⟦ A ⟧ V
     ---------------
   → 𝒫 ⊢ᵒ ℰ⟦ A ⟧ V
𝒱⇒ℰ {A}{𝒫}{V} 𝒫⊢𝒱V = ℰ-intro prog pres
    where
    prog = inj₁ᵒ 𝒫⊢𝒱V
    pres = Λᵒ[ N ] →ᵒI (constᵒE Zᵒ λ V—→N →
             ⊢ᵒ-sucP (Sᵒ 𝒫⊢𝒱V) λ 𝒱V →
                ⊥-elim (value-irreducible (𝒱⇒Value A V 𝒱V ) V—→N))
\end{code}

\subsection{Semantic Type Safety for Open Terms}


\begin{code}
𝓖⟦_⟧ : (Γ : List Type) → Subst → List Setᵒ
𝓖⟦ [] ⟧ σ = []
𝓖⟦ A ∷ Γ ⟧ σ = (𝒱⟦ A ⟧ (σ 0)) ∷ 𝓖⟦ Γ ⟧ (λ x → σ (suc x))
\end{code}

\begin{code}
infix 3 _⊨_⦂_
_⊨_⦂_ : List Type → Term → Type → Set
Γ ⊨ M ⦂ A = ∀ (γ : Subst) → 𝓖⟦ Γ ⟧ γ ⊢ᵒ ℰ⟦ A ⟧ (⟪ γ ⟫ M)
\end{code}

\begin{code}
infix 3 _⊨ⱽ_⦂_
_⊨ⱽ_⦂_ : List Type → Term → Type → Set
Γ ⊨ⱽ V ⦂ A = ∀ (γ : Subst) → 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝒱⟦ A ⟧ (⟪ γ ⟫ V)
\end{code}


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
     appᵒ (appᵒ (instᵒ{P = 𝒱V→ℰF[V][M]} (Sᵒ Zᵒ) M) (constᵒI (M END))) Zᵒ

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
          ▷ℰM′ = appᵒ (instᵒ{P = λ N → (M —→ N)ᵒ →ᵒ ▷ᵒ (ℰ⟦ B ⟧ N)}
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
       appᵒ(▷→ (appᵒ(▷→ (instᵒ(▷∀{P = λ M → ℰ-bind-M A B F M} IH) M)) ℰM)) V→FV

ℰ-bind : ∀{𝒫}{A}{B}{F}{M}
   → 𝒫 ⊢ᵒ ℰ⟦ B ⟧ M
   → 𝒫 ⊢ᵒ (∀ᵒ[ V ] (M —↠ V)ᵒ →ᵒ 𝒱⟦ B ⟧ V →ᵒ ℰ⟦ A ⟧ (F ⟦ V ⟧))
     ----------------------------------------------------------
   → 𝒫 ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)
ℰ-bind {𝒫}{A}{B}{F}{M} ⊢ℰM ⊢𝒱V→ℰFV =
  appᵒ (appᵒ (instᵒ{𝒫}{P = λ M → ℰ-bind-M A B F M} ℰ-bind-aux M) ⊢ℰM) ⊢𝒱V→ℰFV
\end{code}

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
compatible-sucⱽ {Γ}{V} ⊨V γ = {!!}
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
   𝒫₂ = λ V W → 𝒱⟦ A ⟧ W ∷ (⟪ γ ⟫ M —↠ W)ᵒ ∷ 𝒱⟦ A ⇒ B ⟧ V ∷ (⟪ γ ⟫ L —↠ V)ᵒ
                 ∷ 𝓖⟦ Γ ⟧ γ
   ⊢ℰVW : ∀{V W} → 𝒫₂ V W ⊢ᵒ ℰ⟦ B ⟧ (V · W)
   ⊢ℰVW {V}{W} =
     let ⊢𝒱V : 𝒫₂ V W ⊢ᵒ 𝒱⟦ A ⇒ B ⟧ V
         ⊢𝒱V = Sᵒ (Sᵒ Zᵒ) in
     let ⊢𝒱W : 𝒫₂ V W ⊢ᵒ 𝒱⟦ A ⟧ W
         ⊢𝒱W = Zᵒ in
     ⊢ᵒ-sucP ⊢𝒱W λ 𝒱Wsn →
     let w = 𝒱⇒Value A W 𝒱Wsn in
     let Case-λ = λ {N′ refl 𝒱W→ℰNW →
                     let prog : 𝒫₂ (ƛ N′) W ⊢ᵒ progress B (ƛ N′ · W)
                         prog = (inj₂ᵒ (constᵒI (_ , (β-ƛ w)))) in
                     let pres : 𝒫₂ (ƛ N′) W ⊢ᵒ preservation B (ƛ N′ · W)
                         pres = Λᵒ[ N ] →ᵒI (constᵒE Zᵒ λ {r →
                                let ⊢▷ℰN′W = appᵒ 𝒱W→ℰNW (monoᵒ ⊢𝒱W) in
                                let eq = deterministic r (β-ƛ w) in
                                Sᵒ (subst (λ N → 𝒫₂ (ƛ N′) W ⊢ᵒ ▷ᵒ ℰ⟦ B ⟧ N) (sym eq) ⊢▷ℰN′W)}) in
                     ℰ-intro prog pres } in
     𝒱-fun-elim ⊢𝒱V Case-λ {!!}
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
   → ((A ⇒ B) ∷ Γ) ⊨ⱽ V ⦂ (A ⇒ B)
     -------------------
   → Γ ⊨ⱽ (μ V) ⦂ (A ⇒ B)
compatible-μ {Γ}{A}{B}{V} ⊨V γ = {!!}

\end{code}


\subsection{Fundamental Lemma}

\begin{code}
fundamental : ∀ {Γ M A}
  → (Γ ⊢ M ⦂ A)
  → (Γ ⊨ M ⦂ A)
fundamentalⱽ : ∀ {Γ W A}
  → (Γ ⊢ⱽ W ⦂ A)
  → (Γ ⊨ⱽ W ⦂ A)

fundamental {Γ} {.(` _)} {A} (⊢` x) = compatible-var x
fundamental {Γ} {`suc M} {.`ℕ} (⊢suc ⊢M) = compatible-suc{M = M} (fundamental ⊢M)
fundamental {Γ} {case L M N} {A} (⊢case ⊢L ⊢M ⊢N) = {!!}
fundamental {Γ} {L · M} {A} (⊢· ⊢L ⊢M) = compatible-app{L = L}{M} (fundamental ⊢L) (fundamental ⊢M)
fundamental {Γ} {V} {A} (⊢val ⊢V) = compatible-value {V = V} (fundamentalⱽ ⊢V)

fundamentalⱽ {Γ} {.`zero} {.`ℕ} ⊢ⱽzero = compatible-zero
fundamentalⱽ {Γ} {`suc V} {.`ℕ} (⊢ⱽsuc ⊢V) = compatible-sucⱽ{V = V} (fundamentalⱽ ⊢V)
fundamentalⱽ {Γ} {ƛ N} {.(_ ⇒ _)} (⊢ⱽƛ ⊢N) = compatible-lambda{N = N} (fundamental ⊢N)
fundamentalⱽ {Γ} {μ V} {.(_ ⇒ _)} (⊢ⱽμ ⊢V) = compatible-μ{V = V} (fundamentalⱽ ⊢V)
\end{code}
