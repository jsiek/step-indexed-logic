\begin{comment}
\begin{code}
{-# OPTIONS --without-K #-}

module EquivalenceRelation where

open import Data.Product
   using (_×_; _,_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Unit using (tt; ⊤)
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

\end{code}
\end{comment}

\begin{code}
record EquivalenceRelation {ℓ ℓ′ : Level} (A : Set ℓ) : Set (ℓ ⊔ lsuc ℓ′) where
  field
    _⩦_ : A → A → Set ℓ′
    ⩦-refl : ∀{a b : A} → a ≡ b → a ⩦ b
    ⩦-sym : ∀{a b : A} → a ⩦ b → b ⩦ a
    ⩦-trans : ∀{a b c : A} → a ⩦ b → b ⩦ c → a ⩦ c

open EquivalenceRelation {{...}} public

infixr 0 _⩦⟨_⟩_
infix  1 _∎
  
_⩦⟨_⟩_ : ∀{ℓ ℓ′}{A : Set ℓ}{{_ : EquivalenceRelation{ℓ}{ℓ′} A}}
     (P : A)
     {Q : A} → P ⩦ Q
   → {R : A} → Q ⩦ R
   → P ⩦ R
P ⩦⟨ P⩦Q ⟩ Q⩦R = ⩦-trans P⩦Q Q⩦R

_∎ : ∀{ℓ ℓ′}{A : Set ℓ}{{_ : EquivalenceRelation{ℓ}{ℓ′} A}}
    (P : A)
   → P ⩦ P
P ∎ = ⩦-refl refl

data _≐_ {ℓ} {A : Set ℓ} (x : A) : A → Set ℓ where
  ≐-refl : x ≐ x

instance
  SetEq : ∀{A : Set} → EquivalenceRelation {lzero}{lzero} A
  SetEq {A} = record { _⩦_ = _≐_
                      ; ⩦-refl = λ {refl → ≐-refl}
                      ; ⩦-sym = λ {≐-refl → ≐-refl}
                      ; ⩦-trans = λ {≐-refl ≐-refl → ≐-refl}
                      }

infixr 2 _⇔_
_⇔_ : ∀{ℓ} → Set ℓ → Set ℓ → Set ℓ
P ⇔ Q = (P → Q) × (Q → P)

⇔-intro : ∀{ℓ}{P Q : Set ℓ}
  → (P → Q)
  → (Q → P)
    -------
  → P ⇔ Q
⇔-intro PQ QP = PQ , QP

⇔-elim : ∀{ℓ}{P Q : Set ℓ}
  → P ⇔ Q
    -----------------
  → (P → Q) × (Q → P)
⇔-elim PQ = PQ

⇔-to : ∀{ℓ}{P Q : Set ℓ}
  → P ⇔ Q
    -------
  → (P → Q)
⇔-to PQ = proj₁ PQ

⇔-fro : ∀{ℓ}{P Q : Set ℓ}
  → P ⇔ Q
    -------
  → (Q → P)
⇔-fro PQ = proj₂ PQ

⇔-refl : ∀{ℓ}{P Q : Set ℓ}
  → P ≡ Q
  → P ⇔ Q
⇔-refl refl = (λ x → x) , (λ x → x)

⇔-sym : ∀{ℓ}{P Q : Set ℓ}
  → P ⇔ Q
  → Q ⇔ P
⇔-sym = λ {(ab , ba) → ba , ab}

⇔-trans : ∀{ℓ}{P Q R : Set ℓ}
  → P ⇔ Q
  → Q ⇔ R
  → P ⇔ R
⇔-trans = λ {(ab , ba) (bc , cb) → (λ x → bc (ab x)) , (λ x → ba (cb x))}

instance
  IffEq : ∀{ℓ} → EquivalenceRelation (Set ℓ)
  IffEq = record { _⩦_ = λ P Q → P ⇔ Q
                 ; ⩦-refl = ⇔-refl
                 ; ⩦-sym = ⇔-sym
                 ; ⩦-trans = ⇔-trans
                 }

module Examples where

  open import Data.Nat
  
  X₁ : (1 + 1 + 1) ⩦ 3
  X₁ = 1 + (1 + 1) ⩦⟨ ≐-refl ⟩
       1 + 2       ⩦⟨ ≐-refl ⟩  
       3           ∎

  X₂ : ⊤ ⇔ ⊤ × ⊤ × ⊤
  X₂ = ⊤              ⩦⟨ (λ _ → tt , tt) , (λ _ → tt) ⟩
       ⊤ × ⊤          ⩦⟨ (λ _ → tt , tt , tt) , (λ _ → tt , tt) ⟩
       ⊤ × ⊤ × ⊤      ∎

\end{code}
