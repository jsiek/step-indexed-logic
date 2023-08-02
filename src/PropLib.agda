{-# OPTIONS --without-K --prop #-}

open import Agda.Primitive using (lzero; lsuc)
open import Data.Nat using (ℕ; zero; suc)

module PropLib where

data ⊥ {ℓ} : Prop ℓ where

⊥-elim : ∀{ℓ}{A : Prop ℓ} → ⊥{ℓ} → A
⊥-elim {A} ()

⊤ : ∀{ℓ} → Prop (lsuc ℓ)
⊤ {ℓ} = ∀ (P : Prop ℓ) → P → P

tt : ∀{ℓ} → ⊤{ℓ}
tt = λ P x → x

infixr 2 _×_
infixr 2 _,_
data _×_ {ℓ} (A B : Prop ℓ) : Prop ℓ where
  _,_ : A → B → A × B

proj₁ : ∀{ℓ}{A B : Prop ℓ} → A × B → A
proj₁ (a , b) = a

proj₂ : ∀{ℓ}{A B : Prop ℓ} → A × B → B
proj₂ (a , b) = b

data _⊎_ {ℓ} (A B : Prop ℓ) : Prop ℓ where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

_ : ∀{A B C : Prop} → (A → C) → (B → C) → (A ⊎ B) → C
_ = f where
  f : ∀{A B C : Prop} → (A → C) → (B → C) → (A ⊎ B) → C
  f ac bc (inj₁ a) = ac a
  f ac bc (inj₂ b) = bc b

_≤_ : ℕ → ℕ → Prop₁
zero  ≤ y     = ⊤
suc x ≤ zero  = ⊥
suc x ≤ suc y = x ≤ y

_<_ : ℕ → ℕ → Prop₁
m < n = suc m ≤ n

s≤s : ∀{n m} → n ≤ m → suc n ≤ suc m
s≤s {zero} {m} n≤m = tt
s≤s {suc n} {suc m} n≤m = n≤m

n≤1+n : (n : ℕ) → n ≤ suc n
n≤1+n zero = tt
n≤1+n (suc n) = n≤1+n n

≤-refl : ∀{a} → a ≤ a
≤-refl {zero} = tt
≤-refl {suc a} = ≤-refl{a}

≤-trans : ∀{a b c : ℕ} → a ≤ b → b ≤ c → a ≤ c
≤-trans {zero} {b} {c} ab bc = tt
≤-trans {suc a} {suc b} {suc c} ab bc = ≤-trans{a}{b}{c} ab bc

n≮0 : ∀ {n ℓ} → n < 0 → ⊥{ℓ}
n≮0 {n} ()
