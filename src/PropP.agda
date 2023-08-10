{-# OPTIONS --without-K --prop #-}

{-

This renames everything in PropP, adding a subscript "p".

-}

module PropP where

open import Agda.Primitive using (lzero; lsuc; _⊔_)

open import PropLib
  using (Squash; squash; ⌊_⌋; ⊥-elimₛ; match)
  renaming (⊤ to ⊤ₚ; tt to ttₚ; ⊥ to ⊥ₚ;
            _×_ to _×ₚ_; proj₁ to proj₁ₚ; proj₂ to proj₂ₚ; Σ to Σₚ; _,_ to _,ₚ_;
            _⊎_ to _⊎ₚ_; inj₁ to inj₁ₚ; inj₂ to inj₂ₚ;
            ⊥-elim to ⊥-elimₚ;
            _≤_ to _≤ₚ_; _<_ to _<ₚ_; s≤s to s≤sₚ; 
            ≤-refl to ≤-reflₚ; ≤-trans to ≤-transₚ; n≤1+n to n≤1+nₚ; ≤-pred to ≤-predₚ;
            n≮0 to n≮0ₚ) public

infix 2 Σ-syntaxₚ
Σ-syntaxₚ : ∀{a b} → (A : Set a) → (A → Prop b) → Prop (a ⊔ b)
Σ-syntaxₚ = Σₚ

syntax Σ-syntaxₚ A (λ x → B) = Σₚ[ x ∈ A ] B

