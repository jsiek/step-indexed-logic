\begin{comment}
\begin{code}
module July2024.OFE where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat
   using (ℕ; zero; suc; _≤_; _<_; _+_; _∸_; z≤n; s≤s; _≤′_; ≤′-step)
open import Data.Nat.Properties
   using (≤-refl; ≤-antisym; ≤-trans; ≤-step; ≤⇒≤′; ≤′⇒≤; n≤1+n; <⇒≤; s≤′s)
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
open import July2024.StepIndexedLogic

postulate ex-mid : ∀ (P : Set) → P ⊎ ¬ P

\end{code}
\end{comment}

\begin{code}
_≡[_]_ : Setᵒ → ℕ → Setᵒ → Set
ϕ ≡[ n ] ψ = ∀ m → m ≤ n → # ϕ m ⇔ # ψ m
\end{code}

\begin{code}
OFE-approx-equiv : ∀{n : ℕ} → (↓ᵒ (suc n) ϕ ≡ᵒ ↓ᵒ (suc n) ψ ) ⇔ (ϕ ≡[ n ] ψ)
OFE-approx-equiv {ϕ}{ψ}{n} = to , from
  where to : ↓ᵒ (suc n) ϕ ≡ᵒ ↓ᵒ (suc n) ψ  →  ϕ ≡[ n ] ψ
        to ↓nϕ=↓nψ zero m≤n = (λ _ → tz ψ) , λ _ → tz ϕ
        to ↓nϕ=↓nψ (suc m) m≤n = toto , tofrom
         where
         toto : # ϕ (suc m) → # ψ (suc m)
         toto ϕsm = proj₂ (proj₁ (≡ᵒ-elim{k = suc m} ↓nϕ=↓nψ) ((s≤s m≤n) , ϕsm))
         tofrom : # ψ (suc m) → # ϕ (suc m)
         tofrom ψsm = proj₂ (proj₂ (≡ᵒ-elim{k = suc m} ↓nϕ=↓nψ) ((s≤s m≤n) , ψsm))
         
        from : ϕ ≡[ n ] ψ → ↓ᵒ (suc n) ϕ ≡ᵒ ↓ᵒ (suc n) ψ
        from ϕ=nψ = ≡ᵒ-intro aux
         where
         aux : (k : ℕ) → ↓ (suc n) (# ϕ) k ⇔ ↓ (suc n) (# ψ) k
         aux zero = (λ _ → tt) , λ _ → tt
         aux (suc k) = fromto , fromfrom
          where
          fromto : ↓ (suc n) (# ϕ) (suc k) → ↓ (suc n) (# ψ) (suc k)
          fromto (s≤s k<n , ϕsk) = (s≤s k<n) , (proj₁ (ϕ=nψ (suc k) k<n) ϕsk)
          fromfrom : ↓ (suc n) (# ψ) (suc k) → ↓ (suc n) (# ϕ) (suc k)
          fromfrom (s≤s k<n , ψsk) = (s≤s k<n) , (proj₂ (ϕ=nψ (suc k) k<n) ψsk)
\end{code}


\begin{code}
abstract
  _≡ᵒ[_]_ : Setᵒ → ℕ → Setᵒ → Set
  ϕ ≡ᵒ[ n ] ψ = ↓ᵒ n ϕ ≡ᵒ ↓ᵒ n ψ 
\end{code}

≡ᵒ[] is an equivalence relation.

\begin{code}
abstract
  ≡ᵒ[]-refl : ∀{n} → ϕ ≡ᵒ[ n ] ϕ
  ≡ᵒ[]-refl = ≡ᵒ-refl refl

  ≡ᵒ[]-sym : ∀{n} → ϕ ≡ᵒ[ n ] ψ → ψ ≡ᵒ[ n ] ϕ
  ≡ᵒ[]-sym ϕ=ψ = ≡ᵒ-sym ϕ=ψ

  ≡ᵒ[]-trans : ∀{n} → ϕ ≡ᵒ[ n ] ψ → ψ ≡ᵒ[ n ] þ → ϕ ≡ᵒ[ n ] þ
  ≡ᵒ[]-trans ϕ=ψ ψ=þ = ≡ᵒ-trans ϕ=ψ ψ=þ
\end{code}

\begin{code}
abstract
  ≡ᵒ[]-mono : ∀ n m → m ≤ n → ϕ ≡ᵒ[ n ] ψ → ϕ ≡ᵒ[ m ] ψ
  ≡ᵒ[]-mono {ϕ}{ψ} n m m≤n ϕ=[n]ψ =
    let xx : ↓ᵒ n ϕ ≡ᵒ ↓ᵒ n ψ
        xx = ϕ=[n]ψ in
    let yy : ↓ᵒ m ϕ ≡ᵒ ↓ᵒ m ψ
        yy = ≡ᵒ-intro λ k → (λ ↓mϕk → {!!}) , {!!} in
    yy
\end{code}
