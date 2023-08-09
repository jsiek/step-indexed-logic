{-# OPTIONS --without-K --prop #-}

open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Data.Nat using (ℕ; zero; suc)
import Relation.Binary.PropositionalEquality as Eq
open import Data.Empty renaming (⊥ to ⊥ₐ; ⊥-elim to ⊥-elimₐ)
open Eq using (_≡_; refl)

module PropLib where

data Squash {ℓ} (A : Set ℓ) : Prop ℓ where
  squash : A → Squash A

infix 10 ⌊_⌋
⌊_⌋ : ∀{ℓ} (A : Set ℓ) → Prop ℓ
⌊ A ⌋ = Squash A

squash-elim : ∀ {ℓ₁ ℓ₂} (A : Set ℓ₁) (P : Prop ℓ₂) → (A → P) → Squash A → P
squash-elim A P f (squash x) = f x

data ⊥ {ℓ} : Prop ℓ where

⊥-elim : ∀{ℓ}{A : Prop ℓ} → ⊥{ℓ} → A
⊥-elim {A} ()

⊥-elimₛ : ∀{ℓ}{A : Prop ℓ} → ⊥ₐ → A
⊥-elimₛ {A} ()

data ⊤ {ℓ} : Prop ℓ where
  tt : ⊤

infixr 2 _×_
infixr 4 _,_
data _×_ {ℓ} (A B : Prop ℓ) : Prop ℓ where
  _,_ : A → B → A × B

proj₁ : ∀{ℓ}{A B : Prop ℓ} → A × B → A
proj₁ (a , b) = a

proj₂ : ∀{ℓ}{A B : Prop ℓ} → A × B → B
proj₂ (a , b) = b

data _⊎_ {ℓ} (A B : Prop ℓ) : Prop ℓ where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

data Σ {a b} (A : Set a) (B : A → Prop b) : Prop (a ⊔ b) where
  _,_ : (fst : A) → B fst → Σ A B
open Σ public

infix 2 Σ-syntaxₚ
Σ-syntaxₚ : ∀{a b} → (A : Set a) → (A → Prop b) → Prop (a ⊔ b)
Σ-syntaxₚ = Σ

syntax Σ-syntaxₚ A (λ x → B) = Σ[ x ∈ A ] B

match : ∀{ℓ ℓ′}{A : Set ℓ}{B : A → Prop ℓ′}{C : Prop ℓ′} → Σ[ x ∈ A ] (B x) → ((a : A) → B a → C) → C
match (a , Ba) cont = cont a Ba

_ : ∀{A B C : Prop} → (A → C) → (B → C) → (A ⊎ B) → C
_ = f where
  f : ∀{A B C : Prop} → (A → C) → (B → C) → (A ⊎ B) → C
  f ac bc (inj₁ a) = ac a
  f ac bc (inj₂ b) = bc b

_≤_ : ℕ → ℕ → Prop
zero  ≤ y     = ⊤
suc x ≤ zero  = ⊥
suc x ≤ suc y = x ≤ y

_<_ : ℕ → ℕ → Prop
m < n = suc m ≤ n

z≤s : ∀{m} → zero ≤ suc m
z≤s {m} = tt

s≤s : ∀{n m} → n ≤ m → suc n ≤ suc m
s≤s {zero} {m} n≤m = tt
s≤s {suc n} {suc m} n≤m = n≤m

n≤1+n : (n : ℕ) → n ≤ suc n
n≤1+n zero = tt
n≤1+n (suc n) = n≤1+n n

≤-refl : ∀{a} → a ≤ a
≤-refl {zero} = tt
≤-refl {suc a} = ≤-refl{a}

≤-reflexive : ∀{a}{b} → a ≡ b → a ≤ b
≤-reflexive {a}{b} refl = ≤-refl{a}

≤-trans : ∀{a b c : ℕ} → a ≤ b → b ≤ c → a ≤ c
≤-trans {zero} {b} {c} ab bc = tt
≤-trans {suc a} {suc b} {suc c} ab bc = ≤-trans{a}{b}{c} ab bc

n≮0 : ∀ {n ℓ} → n < 0 → ⊥{ℓ}
n≮0 {n} ()

≤-pred : ∀ {m n} → suc m ≤ suc n → m ≤ n
≤-pred {m}{n} m≤n = m≤n

¬_ : ∀{ℓ} → Prop ℓ → Prop ℓ
¬_ {ℓ} A = A → ⊥{ℓ}
