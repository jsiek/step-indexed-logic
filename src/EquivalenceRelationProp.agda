{-# OPTIONS --without-K --prop #-}

module EquivalenceRelationProp where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import PropLib

record EquivalenceRelation {ℓ ℓ′ : Level} (A : Set ℓ) : Set (ℓ ⊔ lsuc ℓ′) where
  field
    _⩦_ : A → A → Prop ℓ′
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

data _≐_ {ℓ} {A : Set ℓ} (x : A) : A → Prop ℓ where
  refl : x ≐ x

≐-refl : ∀{ℓ}{A : Set ℓ}{a b : A} → a ≡ b → a ≐ b
≐-refl {a}{b} refl = refl

≐-sym : ∀{ℓ}{A : Set ℓ}{a b : A} → a ≐ b → b ≐ a
≐-sym {a}{b} refl = refl

subst : ∀ {ℓ}{ℓ′}{A : Set ℓ} {x y : A} (P : A → Prop ℓ′)
  → x ≐ y
    ---------
  → P x → P y
subst P refl px = px

instance
  PropEq : ∀{A : Set} → EquivalenceRelation {lzero}{lzero} A
  PropEq {A} = record { _⩦_ = _≐_
                      ; ⩦-refl = ≐-refl
                      ; ⩦-sym = ≐-sym
                      ; ⩦-trans = λ {refl refl → refl}
                      }

infixr 2 _⇔_
_⇔_ : ∀{ℓ} → Prop ℓ → Prop ℓ → Prop ℓ
P ⇔ Q = (P → Q) × (Q → P)

⇔-intro : ∀{ℓ}{P Q : Prop ℓ}
  → (P → Q)
  → (Q → P)
    -------
  → P ⇔ Q
⇔-intro PQ QP = PQ , QP

⇔-elim : ∀{ℓ}{P Q : Prop ℓ}
  → P ⇔ Q
    -----------------
  → (P → Q) × (Q → P)
⇔-elim PQ = PQ

⇔-to : ∀{ℓ}{P Q : Prop ℓ}
  → P ⇔ Q
    -------
  → (P → Q)
⇔-to PQ = proj₁ PQ

⇔-fro : ∀{ℓ}{P Q : Prop ℓ}
  → P ⇔ Q
    -------
  → (Q → P)
⇔-fro PQ = proj₂ PQ

⇔-refl : ∀{ℓ}{P Q : Prop ℓ}
  → P ≡ Q
  → P ⇔ Q
⇔-refl refl = (λ x → x) , (λ x → x)

⇔-sym : ∀{ℓ}{P Q : Prop ℓ}
  → P ⇔ Q
  → Q ⇔ P
⇔-sym = λ {(ab , ba) → ba , ab}

instance
  IffEq : ∀{ℓ} → EquivalenceRelation (Prop ℓ)
  IffEq = record { _⩦_ = λ P Q → P ⇔ Q
                 ; ⩦-refl = ⇔-refl
                 ; ⩦-sym = ⇔-sym
                 ; ⩦-trans = λ {(ab , ba) (bc , cb) →
                               (λ x → bc (ab x)) , (λ x → ba (cb x))}
                 }

module Examples where

  open import Data.Nat
  
  X₁ : (1 + 1 + 1) ⩦ 3
  X₁ = 1 + (1 + 1) ⩦⟨ refl ⟩
       1 + 2       ⩦⟨ refl ⟩  
       3           ∎

  X₂ : (⊤{lzero}) ⇔ ⊤ × ⊤ × ⊤
  X₂ = ⊤              ⩦⟨ (λ _ → tt , tt) , (λ _ → tt) ⟩
       ⊤ × ⊤          ⩦⟨ (λ _ → tt , tt , tt) , (λ _ → tt , tt) ⟩
       ⊤ × ⊤ × ⊤      ∎

