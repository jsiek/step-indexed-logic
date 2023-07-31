{-# OPTIONS --without-K #-}
open import Data.List using (List; []; _∷_)

module Variables where

Context : Set₁
Context = List Set

data _∋_ : Context → Set → Set₁ where
  zeroᵒ : ∀{Γ}{A} → (A ∷ Γ) ∋ A
  sucᵒ : ∀{Γ}{A}{B} → Γ ∋ B → (A ∷ Γ) ∋ B

data Time : Set where
  Now : Time
  Later : Time

-- Phil: would prefer if this were a list
data Times : Context → Set₁ where
  [] : Times []
  _∷_ : ∀{Γ}{A} → Time → Times Γ → Times (A ∷ Γ)

