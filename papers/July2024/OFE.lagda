\begin{comment}
\begin{code}
module July2024.OFE where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat
   using (ℕ; zero; suc; _≤_; _<_; _+_; _∸_; z≤n; s≤s; _≤′_; ≤′-step; ≤-pred)
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

The step-indexed equality a la Ordered Families of Equalities (OFE) that is used in Iris.
\begin{code}
_≡[_]_ : Setᵒ → ℕ → Setᵒ → Set
ϕ ≡[ n ] ψ = ∀ m → m ≤ n → # ϕ m ⇔ # ψ m
\end{code}

\begin{code}
kapprox-equiv-OFE : ∀{n} → (↓ᵒ (suc n) ϕ ≡ᵒ ↓ᵒ (suc n) ψ )  ⇔  (ϕ ≡[ n ] ψ)
kapprox-equiv-OFE {ϕ}{ψ}{n} = to , from
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
nonexpansive : (Predᵒ A → Predᵒ B) → Set₁
nonexpansive f = ∀ P k j → k ≤ j → ∀ b → ↓ᵒ k (f P b) ≡ᵒ ↓ᵒ k (f (↓ᵖ j P) b)
\end{code}

\begin{code}
nonexpansive′ : (Predᵒ A → Predᵒ B) → Set₁
nonexpansive′ f = ∀ P Q k → (∀ a → P a ≡[ k ] Q a) → ∀ b → (f P b) ≡[ k ] (f Q b)
\end{code}


\begin{code}
NE⇒NE′ : ∀{A}{B}{f : Predᵒ A → Predᵒ B}
  → congruentᵖ f
  → nonexpansive f → nonexpansive′ f
NE⇒NE′ {A}{B}{f} cong-f nef P Q k P=kQ b m m≤k = to m m≤k , fro m m≤k
  where
  to : ∀ m → m ≤ k → # (f P b) m → # (f Q b) m
  to zero m≤k fPz = tz (f Q b)
  to (suc m) sm≤k fPsm =
      let ↓fP≡↓f↓P = nef P (2 + m) (2 + m) ≤-refl b in
      let ↓fQ≡↓f↓Q = nef Q (2 + m) (2 + m) ≤-refl b in
      let ↓P=↓Q = λ a → proj₂ (kapprox-equiv-OFE {ϕ = P a}{ψ = Q a}{n = suc m})
                     λ n n≤sm → P=kQ a n (≤-trans n≤sm sm≤k) in
      let f↓Psm = proj₂ (proj₁ (≡ᵒ-elim{k = suc m} ↓fP≡↓f↓P) (≤-refl , fPsm)) in
      let f↓Qsm = proj₁ (≡ᵒ-elim{k = suc m} (cong-f ↓P=↓Q b)) f↓Psm in
      let fQsm = proj₂ (proj₂ (≡ᵒ-elim{k = suc m} ↓fQ≡↓f↓Q) (≤-refl , f↓Qsm)) in
      fQsm
  fro : ∀ m → m ≤ k → # (f Q b) m → # (f P b) m
  fro zero m≤k fQz = tz (f P b)
  fro (suc m) sm≤k fQsm =
      let ↓fP≡↓f↓P = nef P (2 + m) (2 + m) ≤-refl b in
      let ↓fQ≡↓f↓Q = nef Q (2 + m) (2 + m) ≤-refl b in
      let ↓P=↓Q = λ a → proj₂ (kapprox-equiv-OFE {ϕ = P a}{ψ = Q a}{n = suc m})
                     λ n n≤sm → P=kQ a n (≤-trans n≤sm sm≤k) in
      let f↓Qsm = proj₂ (proj₁ (≡ᵒ-elim{k = suc m} ↓fQ≡↓f↓Q) (≤-refl , fQsm)) in
      let f↓Psm = proj₂ (≡ᵒ-elim{k = suc m} (cong-f ↓P=↓Q b)) f↓Qsm in
      let fPsm = proj₂ (proj₂ (≡ᵒ-elim{k = suc m} ↓fP≡↓f↓P) (≤-refl , f↓Psm)) in
      fPsm
\end{code}

\begin{code}
NE′⇒NE : ∀{A}{B}{f : Predᵒ A → Predᵒ B}
  → congruentᵖ f
  → nonexpansive′ f → nonexpansive f
NE′⇒NE {A} {B} {f} cong-f nef P .zero zero z≤n b = ↓ᵒ-zero
NE′⇒NE {A} {B} {f} cong-f nef P k (suc j) k≤j b = ≡ᵒ-intro aux
  where
  aux : ∀ i → ↓ k (# (f P b)) i ⇔ ↓ k (# (f (↓ᵖ (suc j) P) b)) i
  aux zero = (λ _ → tt) , λ _ → tt
  aux (suc i) = to , fro
    where
    P=[j]=↓sjP : (a : A) → P a ≡[ j ] ↓ᵖ (suc j) P a
    P=[j]=↓sjP a zero m≤j = (λ _ → tt) , λ _ → tz (P a)
    P=[j]=↓sjP a (suc m) sm≤j = (λ Psm → s≤s sm≤j , Psm) , proj₂
    
    to : ↓ k (# (f P b)) (suc i) → ↓ k (# (f (↓ᵖ (suc j) P) b)) (suc i)
    to (si<k , fPsi) =
      si<k , proj₁ (nef P (↓ᵖ (suc j) P) j P=[j]=↓sjP b (suc i) (≤-pred (≤-trans si<k k≤j))) fPsi
      
    fro : ↓ k (# (f (↓ᵖ (suc j) P) b)) (suc i) → ↓ k (# (f P b)) (suc i)
    fro (si<k , f↓sjPsi) =
        si<k , proj₂ (nef P (↓ᵖ (suc j) P) j P=[j]=↓sjP b (suc i) (≤-pred (≤-trans si<k k≤j))) f↓sjPsi
\end{code}
