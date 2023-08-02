{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

{-

  Experimenting with a flat organization.

-}

{-
 Authors: Siek, Thiemann, and Wadler

 Based on "Logical Step-Indexed Logical Relations"
 by Dreyer, Ahmed, and Birkedal.

 Based on the Agda development of Logical Step-Indexed Logical Relations
 by Philip Wadler (June 1, 2022)

 The proof of the fixpoint theorem is based on "An Indexed Model of
 Recursive Types" by Appel and McAllester.

-}
module StepIndexedLogic2 where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat
   using (ℕ; zero; suc; _≤_; _<_; _+_; _∸_; z≤n; s≤s; _≤′_; ≤′-step)
open import Data.Nat.Properties
   using (≤-refl; ≤-antisym; ≤-trans; ≤-step; ≤⇒≤′; ≤′⇒≤; n≤1+n; <⇒≤; ≤-pred)
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

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import EquivalenceRelation public

open import StrongInduction
open import Variables public
open import RawSetO
open import Approx
open import Iteration
open import SetO public
open import Fixpoint
open import Membership

record Inhabited (A : Set) : Set where
  field
    elt : A
open Inhabited {{...}} public

instance
  ℕ-Inhabited : Inhabited ℕ
  ℕ-Inhabited = record { elt = zero }

choose : Time → Time → Time
choose Now Now = Now
choose Now Later = Now
choose Later Now = Now
choose Later Later = Later

combine : ∀{Γ} (Δ₁ Δ₂ : Times Γ) → Times Γ
combine {[]} Δ₁ Δ₂ = []
combine {A ∷ Γ} (x ∷ Δ₁) (y ∷ Δ₂) = (choose x y) ∷ (combine Δ₁ Δ₂)

module Later where
  ▷ : ∀{Γ} → (RecEnv Γ → ℕ → Set) → (RecEnv Γ → ℕ → Set)
  ▷ ϕ δ k = ∀ j → j < k → ϕ δ j

  down-▷ : ∀{Γ}{Δ : Times Γ} (ϕ : Setᵒ Γ Δ)
    → ∀ δ → downClosedᵈ δ → downClosed (▷ (# ϕ) δ)
  down-▷ {Γ}{Δ} ϕ δ down-δ n ▷ϕn k k≤n j j<k = ▷ϕn j (≤-trans j<k k≤n)

open Later

module RecPred where

  down-mu : ∀{Γ}{Δ}{A}(Sᵃ : A → Setᵒ (A ∷ Γ) (Later ∷ Δ)) (a : A) (δ : RecEnv Γ) → downClosedᵈ δ → downClosed (mu Sᵃ δ a)
  down-mu Sᵃ a δ dc-δ = {!!}

open RecPred


module _ where
 abstract

 {---------------------- Membership in Recursive Predicate ---------------------}

  _∈_ : ∀{Γ}{A} → A → (x : Γ ∋ A) → Setᵒ Γ (var-now Γ x)
  a ∈ x = record { # = λ δ → (lookup x δ) a 
                 ; down = down-lookup }
{-
           ; tz = tz-lookup
           ; good = good-lookup x
           ; congr = congruent-lookup x a
           }
           -}

  #∈≡ : ∀{Γ}{A} → (a : A) → (x : Γ ∋ A) → # (a ∈ x) ≡ λ δ → (lookup x δ) a
  #∈≡ a x = refl
  
{---------------------- Later Operator ---------------------}

  ▷ᵒ : ∀{Γ}{Δ : Times Γ}
     → Setᵒ Γ Δ
       -----------------
     → Setᵒ Γ (laters Γ)
  ▷ᵒ {Γ}{Δ} S = record { # = λ δ k → ▷ (# S) δ k 
                ; down = down-▷ S
                }
{-
                ; tz = {!!}
                ; good = {!!}
                ; congr = {!!}
                }
                -}

  #▷ᵒ≡ : ∀{Γ}{Δ}{ϕ : Setᵒ Γ Δ} → # (▷ᵒ ϕ) ≡ ▷ (# ϕ)
  #▷ᵒ≡ {Γ}{Δ}{ϕ} = let x = # (▷ᵒ ϕ) in refl

  ▷sk : ∀{Γ}{Δ}{ϕ : Setᵒ Γ Δ}{δ : RecEnv Γ}{k}
     → downClosedᵈ δ
     → ▷ (# ϕ) δ (suc k) ⇔ (# ϕ) δ k
  ▷sk {Γ}{Δ}{ϕ}{δ}{k} down-δ =
     (λ ▷ϕsk → ▷ϕsk k ≤-refl) , λ ϕk j j<sk → down ϕ δ down-δ k ϕk j (≤-pred j<sk)




{---------------------- Recursive Predicate -----------------------------------}

abstract
  μᵒ : ∀{Γ}{Δ : Times Γ}{A}
     → (A → Setᵒ (A ∷ Γ) (Later ∷ Δ))
     → (A → Setᵒ Γ Δ)
  μᵒ {Γ}{Δ}{A} Sᵃ a =
    record { # = λ δ → mu Sᵃ δ a 
           ; down = down-mu Sᵃ a
           }
{-    
           ; tz = {!!}
           ; good = {!!}
           ; congr = {!!}
           }
-}

  #μᵒ≡ : ∀{Γ}{Δ : Times Γ}{A} (Sᵃ : A → Setᵒ (A ∷ Γ) (Later ∷ Δ)) (a : A) → ∀ δ k
     → # (μᵒ Sᵃ a) δ k ≡ mu Sᵃ δ a k
  #μᵒ≡ Sᵃ a δ k = refl

{---------------------- Forall -----------------------------------------}

  ∀ᵒ : ∀{Γ}{Δ : Times Γ}{A : Set}
     → (A → Setᵒ Γ Δ)
     → Setᵒ Γ Δ
  ∀ᵒ{Γ}{Δ}{A} P =
    record { # = λ δ k → ∀ (a : A) → # (P a) δ k 
           ; down = {!!}
           }
{-    
           ; tz = {!!}
           ; good = {!!}
           ; congr = {!!}
           }
           -}

  #∀ᵒ≡ : ∀{Γ}{Δ : Times Γ}{A : Set}{{_ : Inhabited A}}{Sᵃ : A → Setᵒ Γ Δ}{δ}{k}
     → (# (∀ᵒ Sᵃ) δ k) ≡ ∀ (a : A) → # (Sᵃ a) δ k
  #∀ᵒ≡ = refl
  
{---------------------- Exists -----------------------------------------}

  ∃ᵒ : ∀{Γ}{Δ : Times Γ}{A : Set}{{_ : Inhabited A}}
     → (A → Setᵒ Γ Δ)
     → Setᵒ Γ Δ
  ∃ᵒ{Γ}{Δ}{A} P =
    record { # = λ δ k → Σ[ a ∈ A ] # (P a) δ k 
           ; down = {!!}
           }
{-    
           ; tz = {!!}
           ; good = {!!}
           ; congr = {!!}
           -}

  #∃ᵒ≡ : ∀{Γ}{Δ : Times Γ}{A : Set}{{_ : Inhabited A}}{Sᵃ : A → Setᵒ Γ Δ}{δ}{k}
     → (# (∃ᵒ Sᵃ) δ k) ≡ (Σ[ a ∈ A ] (# (Sᵃ a) δ k))
  #∃ᵒ≡ = refl
  
  

{---------------------- Pure -----------------------------------------}

  _ᵒ : ∀{Γ} → Set → Setᵒ Γ (laters Γ)
  p ᵒ = record { # = λ δ k → p 
               ; down = {!!}
               }
{-  
               ; tz = {!!}
               ; good = {!!}
               ; congr = {!!}
-}               
  #pureᵒ≡ : ∀{p}{Γ}{δ : RecEnv Γ}{k} → # (p ᵒ) δ (suc k) ≡ p
  #pureᵒ≡ = refl

{---------------------- False -----------------------------------------}

  ⊥ᵒ : ∀{Γ} → Setᵒ Γ (laters Γ)
  ⊥ᵒ = ⊥ ᵒ

{---------------------- True -----------------------------------------}

  ⊤ᵒ : ∀{Γ} → Setᵒ Γ (laters Γ)
  ⊤ᵒ = record { # = λ δ k → ⊤
               ; down = {!!}
               }
{-  
               ; tz = {!!}
               ; good = {!!}
               ; congr = {!!}
 -}

  #⊤ᵒ≡⊤ : ∀{Γ}{δ : RecEnv Γ}{k} → # ⊤ᵒ δ k ≡ ⊤
  #⊤ᵒ≡⊤ = refl

{---------------------- Conjunction -----------------------------------------}

  infixr 7 _×ᵒ_
  _×ᵒ_ : ∀{Γ}{Δ₁ Δ₂ : Times Γ}
     → Setᵒ Γ Δ₁
     → Setᵒ Γ Δ₂
       ------------------------
     → Setᵒ Γ (combine Δ₁ Δ₂)
  S ×ᵒ T = record { # = λ δ k → # S δ k × # T δ k 
                  ; down = {!!}
                  }
{-  
                  ; tz = {!!}
                  ; good = {!!}
                  ; congr = {!!}
-}                  
  #×ᵒ≡ : ∀{Γ}{Δ₁ Δ₂ : Times Γ}{ϕ : Setᵒ Γ Δ₁}{ψ : Setᵒ Γ Δ₂}{δ}{k}
       → (# (ϕ ×ᵒ ψ) δ k) ≡ (# ϕ δ k × # ψ δ k)
  #×ᵒ≡ {Γ}{Δ₁}{Δ₂}{ϕ}{ψ}{δ}{k} = refl

  cong-×ᵒ : ∀{Γ}{Δ}{ϕ ϕ′ ψ ψ′ : Setᵒ Γ Δ} → ϕ ≡ᵒ ϕ′ → ψ ≡ᵒ ψ′ → ϕ ×ᵒ ψ ≡ᵒ ϕ′ ×ᵒ ψ′
  cong-×ᵒ {Γ}{Δ}{ϕ}{ϕ′}{ψ}{ψ′} ϕ=ϕ′ ψ=ψ′ = ≡ᵒ-intro (λ δ k → ⇔-intro to fro)
    where
    to : ∀{δ}{k} → # (ϕ ×ᵒ ψ) δ k → # (ϕ′ ×ᵒ ψ′) δ k
    to {δ}{k} (ϕk , ψk) = (⇔-to (≡ᵒ-elim ϕ=ϕ′) ϕk) , (⇔-to (≡ᵒ-elim ψ=ψ′) ψk)
    fro  : ∀{k}{δ} → # (ϕ′ ×ᵒ ψ′) δ k → #(ϕ ×ᵒ ψ) δ k
    fro {δ}{k} (ϕ′k , ψ′k) = (⇔-fro (≡ᵒ-elim ϕ=ϕ′) ϕ′k) , (⇔-fro (≡ᵒ-elim ψ=ψ′) ψ′k)


{---------------------- Disjunction -----------------------------------------}

  infixr 7 _⊎ᵒ_
  _⊎ᵒ_ : ∀{Γ}{Δ₁ Δ₂ : Times Γ}
     → Setᵒ Γ Δ₁
     → Setᵒ Γ Δ₂
       ------------------------
     → Setᵒ Γ (combine Δ₁ Δ₂)
  S ⊎ᵒ T = record { # = λ δ k → # S δ k ⊎ # T δ k
                  ; down = {!!}
                  }
{-  
                  ; tz = {!!}
                  ; good = {!!}
                  ; congr = {!!}
                  -}

  #⊎ᵒ≡ : ∀{Γ}{Δ₁ Δ₂ : Times Γ}{ϕ : Setᵒ Γ Δ₁}{ψ : Setᵒ Γ Δ₂}{δ}{k}
       → (# (ϕ ⊎ᵒ ψ) δ k) ≡ (# ϕ δ k ⊎ # ψ δ k)
  #⊎ᵒ≡ {Γ}{Δ₁}{Δ₂}{ϕ}{ψ}{δ}{k} = refl

  cong-⊎ᵒ : ∀{Γ}{Δ}{ϕ ϕ′ ψ ψ′ : Setᵒ Γ Δ} → ϕ ≡ᵒ ϕ′ → ψ ≡ᵒ ψ′ → ϕ ⊎ᵒ ψ ≡ᵒ ϕ′ ⊎ᵒ ψ′
  cong-⊎ᵒ {Γ}{Δ}{ϕ}{ϕ′}{ψ}{ψ′} ϕ=ϕ′ ψ=ψ′ = ≡ᵒ-intro (λ δ k → ⇔-intro to fro)
    where
    to : ∀{δ}{k} → # (ϕ ⊎ᵒ ψ) δ k → # (ϕ′ ⊎ᵒ ψ′) δ k
    to (inj₁ x) = inj₁ (proj₁ (≡ᵒ-elim ϕ=ϕ′) x)
    to (inj₂ y) = inj₂ (proj₁ (≡ᵒ-elim ψ=ψ′) y)
    fro  : ∀{δ}{k} → #(ϕ′ ⊎ᵒ ψ′) δ k → #(ϕ ⊎ᵒ ψ) δ k
    fro (inj₁ x) = inj₁ (proj₂ (≡ᵒ-elim ϕ=ϕ′) x)
    fro (inj₂ y) = inj₂ (proj₂ (≡ᵒ-elim ψ=ψ′) y)

{---------------------- Implication -----------------------------------------}

  infixr 6 _→ᵒ_
  _→ᵒ_ : ∀{Γ}{Δ₁ Δ₂ : Times Γ}
     → Setᵒ Γ Δ₁
     → Setᵒ Γ Δ₂
       ------------------------
     → Setᵒ Γ (combine Δ₁ Δ₂)
  S →ᵒ T = record { # = λ δ k → ∀ j → j ≤ k → # S δ j → # T δ j 
                  ; down = {!!}
                  }
{-  
                  ; tz = {!!}
                  ; good = {!!}
                  ; congr = {!!}
-}                  
  #→ᵒ≡ : ∀{Γ}{Δ₁ Δ₂ : Times Γ}{ϕ : Setᵒ Γ Δ₁}{ψ : Setᵒ Γ Δ₂}{δ}{k}
       → (# (ϕ →ᵒ ψ) δ k) ≡ (∀ j → j ≤ k → # ϕ δ j → # ψ δ j)
  #→ᵒ≡ {Γ}{Δ₁}{Δ₂}{ϕ}{ψ}{δ}{k} = refl

{---------------------- Let for Predicates -----------------------------------------}

  letᵒ : ∀{A}{Γ}{t}{Δ} → (A → Setᵒ Γ Δ) → Setᵒ (A ∷ Γ) (t ∷ Δ) → Setᵒ Γ Δ   
  letᵒ Sᵃ T = record { # = λ δ k →  # T ((λ a k → # (Sᵃ a) δ k) , δ) k
                     ; down = {!!}
                     }
{-  
                     ; tz = {!!}
                     ; good = {!!}
                     ; congr = {!!}
-}
  #letᵒ≡ : ∀{A}{Γ}{Δ}{t} (P : A → Setᵒ Γ Δ) (ϕ : Setᵒ (A ∷ Γ) (t ∷ Δ)) → ∀ δ k
     → (# (letᵒ P ϕ) δ k) ≡ (# ϕ ((λ a k → # (P a) δ k) , δ) k)
  #letᵒ≡ {A}{Γ}{Δ}{t} P ϕ d k = refl
  
  let-▷ᵒ : ∀{A}{t}{P : A → Setᵒ [] []}{ϕ : Setᵒ (A ∷ []) (t ∷ [])}
     → letᵒ P (▷ᵒ ϕ) ≡ ▷ᵒ (letᵒ P ϕ)
  let-▷ᵒ {A} {t} {P} {ϕ} = refl
  
  let-∈ : ∀{A}{P : A → Setᵒ [] []}{a : A}
     → letᵒ P (a ∈ zeroᵒ) ≡ (P a)
  let-∈ {A}{P}{a} = refl
  
  let-pureᵒ : ∀{A}{P : A → Setᵒ [] []}{p : Set}
     → letᵒ P (p ᵒ) ≡ p ᵒ
  let-pureᵒ = refl

  let-⊥ᵒ : ∀{A}{P : A → Setᵒ [] []}
     → letᵒ P ⊥ᵒ ≡ ⊥ᵒ
  let-⊥ᵒ = refl

  let-⊤ᵒ : ∀{A}{P : A → Setᵒ [] []}
     → letᵒ P ⊤ᵒ ≡ ⊤ᵒ
  let-⊤ᵒ = refl

  let-×ᵒ : ∀{A}{P : A → Setᵒ [] []}{ϕ ψ : Setᵒ (A ∷ []) (Later ∷ [])}
     → letᵒ P (ϕ ×ᵒ ψ) ≡ (letᵒ P ϕ) ×ᵒ (letᵒ P ψ)
  let-×ᵒ = refl

  let-⊎ᵒ : ∀{A}{P : A → Setᵒ [] []}{ϕ ψ : Setᵒ (A ∷ []) (Later ∷ [])}
     → letᵒ P (ϕ ⊎ᵒ ψ) ≡ (letᵒ P ϕ) ⊎ᵒ (letᵒ P ψ)
  let-⊎ᵒ {A}{P}{ϕ}{ψ} = refl

  let-→ᵒ : ∀{A}{P : A → Setᵒ [] []}{ϕ ψ : Setᵒ (A ∷ []) (Later ∷ [])}
     → letᵒ P (ϕ →ᵒ ψ) ≡ (letᵒ P ϕ) →ᵒ (letᵒ P ψ)
  let-→ᵒ = refl

  let-∀ᵒ : ∀{A}{B}{P : A → Setᵒ [] []}{ϕᵇ  : B → Setᵒ (A ∷ []) (Later ∷ [])}
     → letᵒ P (∀ᵒ ϕᵇ) ≡ ∀ᵒ λ b →  (letᵒ P (ϕᵇ b))
  let-∀ᵒ {A}{B}{P}{ϕᵇ} = refl

  let-∃ᵒ : ∀{A}{B}{{_ : Inhabited B}}{P : A → Setᵒ [] []}{ϕᵇ  : B → Setᵒ (A ∷ []) (Later ∷ [])}
     → letᵒ P (∃ᵒ ϕᵇ) ≡ ∃ᵒ λ b →  (letᵒ P (ϕᵇ b))
  let-∃ᵒ {A}{B}{P}{ϕᵇ} = refl

  {-# REWRITE let-⊥ᵒ #-}
  {-# REWRITE let-⊤ᵒ #-}
  {-# REWRITE let-▷ᵒ #-}
  {-# REWRITE let-∈ #-}
  {-# REWRITE let-pureᵒ #-}
  {-# REWRITE let-×ᵒ #-}
  {-# REWRITE let-⊎ᵒ #-}
  {-# REWRITE let-→ᵒ #-}
  {-# REWRITE let-∀ᵒ #-}
  {-# REWRITE let-∃ᵒ #-}


{---------------------- Fixpoint Theorem --------------------------------------}

Setᵏ : Set₁
Setᵏ = Setᵒ [] []

private variable ϕ ϕ′ ψ ψ′ þ : Setᵏ
private variable 𝒫 : List Setᵏ
private variable p : Set
private variable A B C : Set
private variable Γ : Context
private variable Δ Δ₁ Δ₂ : Times Γ

abstract
  fixpointᵒ : ∀{Γ}{Δ : Times Γ}{A} (Sᵃ : A → Setᵒ (A ∷ Γ) (Later ∷ Δ)) (a : A)
     → μᵒ Sᵃ a ≡ᵒ letᵒ (μᵒ Sᵃ) (Sᵃ a)
  fixpointᵒ{Γ}{Δ}{A} Sᵃ a = ≡ₒ⇒≡ᵒ{Γ}{Δ} aux
    where
    aux : ∀ δ → # (μᵒ Sᵃ a) δ ≡ₒ # (letᵒ (μᵒ Sᵃ) (Sᵃ a)) δ
    aux δ =
        # (μᵒ Sᵃ a) δ 
      ⩦⟨ ≡ₒ-refl refl ⟩
        mu Sᵃ δ a
      ⩦⟨ equiv-approx (lemma19a Sᵃ a δ) ⟩
        # (Sᵃ a) ((λ a k → mu Sᵃ δ a k) , δ) 
      ⩦⟨ ≡ₒ-refl refl ⟩
        # (Sᵃ a) ((λ a k → # (μᵒ Sᵃ a) δ k) , δ)
      ⩦⟨ ≡ₒ-refl refl ⟩
        # (letᵒ (μᵒ Sᵃ) (Sᵃ a)) δ
      ∎

{---------------------- Proof Theory for Step Indexed Logic -------------------}



Πᵏ : List Setᵏ → Setᵏ
Πᵏ [] = ⊤ᵒ
Πᵏ (P ∷ 𝒫) = P ×ᵒ Πᵏ 𝒫 

abstract
  infix 1 _⊢ᵒ_
  _⊢ᵒ_ : List Setᵏ → Setᵏ → Set
  𝒫 ⊢ᵒ P = ∀ n → # (Πᵏ 𝒫) ttᵖ n → # P ttᵖ n

  ⊢ᵒI : ∀{𝒫}{P}
     → (∀ n → # (Πᵏ 𝒫) ttᵖ n → # P ttᵖ n)
     → 𝒫 ⊢ᵒ P
  ⊢ᵒI 𝒫→P = 𝒫→P

  ⊢ᵒE : ∀{𝒫}{P}
     → 𝒫 ⊢ᵒ P
     → (∀ n → # (Πᵏ 𝒫) ttᵖ n → # P ttᵖ n)
  ⊢ᵒE 𝒫⊢P = 𝒫⊢P

abstract
  ttᵒ : 𝒫 ⊢ᵒ ⊤ᵒ
  ttᵒ n _ = tt

abstract
  ⊥-elimᵒ : 𝒫 ⊢ᵒ ⊥ᵒ → (ϕ : Setᵏ) → 𝒫 ⊢ᵒ ϕ
  ⊥-elimᵒ ⊢⊥ ϕ n ⊨𝒫sn = ⊥-elim (⊢⊥ n ⊨𝒫sn)

  ⊥⇒⊥ᵒ : ⊥ → 𝒫 ⊢ᵒ ⊥ᵒ
  ⊥⇒⊥ᵒ ()

  ⊥ᵒ⇒⊥ : [] ⊢ᵒ ⊥ᵒ → ⊥
  ⊥ᵒ⇒⊥ ⊢⊥ = ⊢ᵒE{[]}{⊥ᵒ} ⊢⊥ 1 tt

abstract
  pureᵒI : ∀{p : Set} → p → 𝒫 ⊢ᵒ p ᵒ
  pureᵒI s n ⊨𝒫n = s

  pureᵒE : 𝒫 ⊢ᵒ p ᵒ  →  (p → 𝒫 ⊢ᵒ þ)  →  𝒫 ⊢ᵒ þ
  pureᵒE {𝒫} {p} {R} ⊢p p→⊢R n 𝒫n = p→⊢R (⊢p n 𝒫n) n 𝒫n

pureᵒE-syntax = pureᵒE
infix 1 pureᵒE-syntax
syntax pureᵒE-syntax pᵒ (λ p → ⊢þ) = let-pureᵒ[ p ] pᵒ within ⊢þ

abstract
  _,ᵒ_ : 𝒫 ⊢ᵒ ϕ  →  𝒫 ⊢ᵒ ψ  →  𝒫 ⊢ᵒ ϕ ×ᵒ ψ
  (𝒫⊢ϕ ,ᵒ 𝒫⊢ψ) n ⊨𝒫n = 𝒫⊢ϕ n ⊨𝒫n , 𝒫⊢ψ n ⊨𝒫n

  proj₁ᵒ : ∀{𝒫 : List Setᵏ }{P Q : Setᵏ}
    → 𝒫 ⊢ᵒ P ×ᵒ Q
      ------------
    → 𝒫 ⊢ᵒ P
  proj₁ᵒ 𝒫⊢P×Q n ⊨𝒫n = proj₁ (𝒫⊢P×Q n ⊨𝒫n)

  proj₂ᵒ : 𝒫 ⊢ᵒ ϕ ×ᵒ ψ  →  𝒫 ⊢ᵒ ψ
  proj₂ᵒ 𝒫⊢ϕ×ψ n ⊨𝒫n = proj₂ (𝒫⊢ϕ×ψ n ⊨𝒫n)

abstract
  inj₁ᵒ : 𝒫 ⊢ᵒ ϕ → 𝒫 ⊢ᵒ ϕ ⊎ᵒ ψ
  inj₁ᵒ 𝒫⊢ϕ n ⊨𝒫n = inj₁ (𝒫⊢ϕ n ⊨𝒫n)

  inj₂ᵒ : 𝒫 ⊢ᵒ ψ → 𝒫 ⊢ᵒ ϕ ⊎ᵒ ψ
  inj₂ᵒ 𝒫⊢ψ n ⊨𝒫n = inj₂ (𝒫⊢ψ n ⊨𝒫n)

  caseᵒ : 𝒫 ⊢ᵒ ϕ ⊎ᵒ ψ  →  ϕ ∷ 𝒫 ⊢ᵒ þ  →  ψ ∷ 𝒫 ⊢ᵒ þ  →  𝒫 ⊢ᵒ þ
  caseᵒ 𝒫⊢ϕ⊎ψ ϕ∷𝒫⊢þ ψ∷𝒫⊢þ n ⊨𝒫n
      with 𝒫⊢ϕ⊎ψ n ⊨𝒫n
  ... | inj₁ ϕn = ϕ∷𝒫⊢þ n (ϕn , ⊨𝒫n)
  ... | inj₂ ψn = ψ∷𝒫⊢þ n (ψn , ⊨𝒫n)

abstract
  downClosed-Πᵏ : (𝒫 : List Setᵏ) → downClosed (# (Πᵏ 𝒫) ttᵖ)
  downClosed-Πᵏ [] = λ n _ k _ → tt
  downClosed-Πᵏ (ϕ ∷ 𝒫) n (ϕn , ⊨𝒫n) k k≤n =
    down ϕ ttᵖ tt n ϕn k k≤n , (downClosed-Πᵏ 𝒫 n ⊨𝒫n k k≤n) -- 

abstract
  →ᵒI : ϕ ∷ 𝒫 ⊢ᵒ ψ  →  𝒫 ⊢ᵒ ϕ →ᵒ ψ
  →ᵒI {𝒫 = 𝒫} ϕ∷𝒫⊢ψ n ⊨𝒫n j j≤n ϕj = ϕ∷𝒫⊢ψ j (ϕj , downClosed-Πᵏ 𝒫 n ⊨𝒫n j j≤n)

  →ᵒE : 𝒫 ⊢ᵒ ϕ →ᵒ ψ  →  𝒫 ⊢ᵒ ϕ  →  𝒫 ⊢ᵒ ψ
  →ᵒE {𝒫} 𝒫⊢ϕ→ψ 𝒫⊢ϕ n ⊨𝒫n = let ϕn = 𝒫⊢ϕ n ⊨𝒫n in 𝒫⊢ϕ→ψ n ⊨𝒫n n ≤-refl ϕn

abstract
  monoᵒ : 𝒫 ⊢ᵒ ϕ  →  𝒫 ⊢ᵒ  ▷ᵒ ϕ
  monoᵒ {𝒫} ⊢ϕ k ⊨𝒫k j j<k =
        ⊢ϕ j (downClosed-Πᵏ 𝒫 k ⊨𝒫k j (≤-trans (n≤1+n j) j<k)) 

{-
  monoᵒ {𝒫}{ϕ} ⊢ϕ zero ⊨𝒫n = tt
  monoᵒ {𝒫}{ϕ} ⊢ϕ (suc n) ⊨𝒫n = ⊢ϕ n (downClosed-Πᵏ 𝒫 (suc n) ⊨𝒫n n (n≤1+n n))
-}

abstract
  lobᵒ : (▷ᵒ ϕ) ∷ 𝒫 ⊢ᵒ ϕ  →  𝒫 ⊢ᵒ ϕ
  lobᵒ {ϕ}{𝒫} step k ⊨𝒫k = aux k step ⊨𝒫k
    where
    aux : ∀ k → ▷ᵒ ϕ ∷ 𝒫 ⊢ᵒ ϕ → # (Πᵏ 𝒫) ttᵖ k → # ϕ ttᵖ k
    aux = strong-induction si
     where
      si : ∀ n → (∀ i → i < n → ▷ᵒ ϕ ∷ 𝒫 ⊢ᵒ ϕ → # (Πᵏ 𝒫) ttᵖ i → # ϕ ttᵖ i)
         →  ▷ᵒ ϕ ∷ 𝒫 ⊢ᵒ ϕ  →  # (Πᵏ 𝒫) ttᵖ n → # ϕ ttᵖ n
      si n IH step Pn =
        let ⊨𝒫n = downClosed-Πᵏ 𝒫 n Pn n ≤-refl in
        step n ((λ j j<sucn → IH j j<sucn step (downClosed-Πᵏ 𝒫 n Pn j (≤-trans (n≤1+n j) j<sucn))) , Pn)

abstract
  substᵒ : ϕ ≡ᵒ ψ  →  𝒫 ⊢ᵒ ϕ  →  𝒫 ⊢ᵒ ψ
  substᵒ ϕ=ψ 𝒫⊢ϕ n ⊨𝒫n = ⇔-to ((≡ᵒ⇒≡ₒ ϕ=ψ) n) (𝒫⊢ϕ n ⊨𝒫n)

abstract
  Λᵒ : {ϕᵃ : A → Setᵏ} → (∀ a → 𝒫 ⊢ᵒ ϕᵃ a)  →  𝒫 ⊢ᵒ ∀ᵒ ϕᵃ
  Λᵒ ∀ϕᵃa n ⊨𝒫n a = ∀ϕᵃa a n ⊨𝒫n

Λᵒ-syntax = Λᵒ
infix 1 Λᵒ-syntax
syntax Λᵒ-syntax (λ a → ⊢ϕᵃa) = Λᵒ[ a ] ⊢ϕᵃa

abstract
  ∀ᵒE : ∀{ϕᵃ : A → Setᵏ} → 𝒫 ⊢ᵒ ∀ᵒ ϕᵃ  →  (a : A)  →  𝒫 ⊢ᵒ ϕᵃ a
  ∀ᵒE ⊢∀ϕᵃ a n ⊨𝒫n = ⊢∀ϕᵃ n ⊨𝒫n a

  ∃ᵒI : ∀{ϕᵃ : A → Setᵏ}{{_ : Inhabited A}} → (a : A)  →  𝒫 ⊢ᵒ ϕᵃ a  →  𝒫 ⊢ᵒ ∃ᵒ ϕᵃ
  ∃ᵒI a ⊢ϕᵃa n ⊨𝒫n = a , (⊢ϕᵃa n ⊨𝒫n)

  ∃ᵒE : ∀{ϕᵃ : A → Setᵏ}{þ : Setᵏ}{{_ : Inhabited A}}
     → 𝒫 ⊢ᵒ ∃ᵒ ϕᵃ  →  (∀ a → ϕᵃ a ∷ 𝒫 ⊢ᵒ þ)  →  𝒫 ⊢ᵒ þ
  ∃ᵒE ⊢∃ϕᵃ cont n ⊨𝒫n
      with ⊢∃ϕᵃ n ⊨𝒫n
  ... | (a , ϕᵃasn) = cont a n (ϕᵃasn , ⊨𝒫n)

abstract
  Zᵒ : ϕ ∷ 𝒫 ⊢ᵒ ϕ
  Zᵒ n (ϕn , ⊨𝒫n) = ϕn

abstract
  Sᵒ : 𝒫 ⊢ᵒ ψ  →  ϕ ∷ 𝒫 ⊢ᵒ ψ
  Sᵒ 𝒫⊢ψ n (ϕn , ⊨𝒫n) = 𝒫⊢ψ n ⊨𝒫n


λᵒ : ∀ ϕ → (ϕ ∷ 𝒫 ⊢ᵒ ϕ → ϕ ∷ 𝒫 ⊢ᵒ ψ) → 𝒫 ⊢ᵒ ϕ →ᵒ ψ
λᵒ ϕ f = →ᵒI{ϕ = ϕ} (f Zᵒ)

λᵒ-syntax = λᵒ
infix 1 λᵒ-syntax
syntax λᵒ-syntax ϕ (λ ⊢ϕ → ⊢ψ) = λᵒ[ ⊢ϕ ⦂ ϕ ] ⊢ψ

unpackᵒ : ∀{ϕᵃ : A → Setᵏ}{þ : Setᵏ}{{_ : Inhabited A}}
     → 𝒫 ⊢ᵒ ∃ᵒ ϕᵃ  →  (∀ a → ϕᵃ a ∷ 𝒫 ⊢ᵒ ϕᵃ a → ϕᵃ a ∷ 𝒫 ⊢ᵒ þ)  →  𝒫 ⊢ᵒ þ
unpackᵒ ∃ϕ cont = ∃ᵒE ∃ϕ λ a → cont a Zᵒ

foldᵒ : ∀{𝒫} (Sᵃ : A → Setᵒ (A ∷ []) (Later ∷ [])) (a : A) →  𝒫 ⊢ᵒ letᵒ (μᵒ Sᵃ) (Sᵃ a)  →  𝒫 ⊢ᵒ μᵒ Sᵃ a
foldᵒ Sᵃ a Sᵃ[μSᵃ] = substᵒ (≡ᵒ-sym (fixpointᵒ Sᵃ a)) Sᵃ[μSᵃ]

unfoldᵒ : ∀{𝒫} (Sᵃ : A → Setᵒ (A ∷ []) (Later ∷ [])) (a : A) →  𝒫 ⊢ᵒ μᵒ Sᵃ a  →  𝒫 ⊢ᵒ letᵒ (μᵒ Sᵃ) (Sᵃ a)
unfoldᵒ Sᵃ a μSᵃ = substᵒ (fixpointᵒ Sᵃ a) μSᵃ

abstract
  ▷× : 𝒫 ⊢ᵒ (▷ᵒ (ϕ ×ᵒ ψ))  →  𝒫 ⊢ᵒ (▷ᵒ ϕ) ×ᵒ (▷ᵒ ψ)
  ▷× ▷ϕ×ψ n 𝒫n = (λ j j<n → proj₁ (▷ϕ×ψ n 𝒫n j j<n))
                , (λ j j<n → proj₂ (▷ϕ×ψ n 𝒫n j j<n))

  ▷⊎ : 𝒫 ⊢ᵒ (▷ᵒ (ϕ ⊎ᵒ ψ))  →  𝒫 ⊢ᵒ (▷ᵒ ϕ) ⊎ᵒ (▷ᵒ ψ)
  ▷⊎ ▷ϕ⊎ψ zero 𝒫n = inj₁ λ j ()
  ▷⊎ {𝒫}{ϕ}{ψ} ▷ϕ⊎ψ (suc n) 𝒫n 
      with ▷ϕ⊎ψ (suc n) 𝒫n n ≤-refl
  ... | inj₁ ϕn = inj₁ λ { j (s≤s j≤n) → down ϕ ttᵖ tt n ϕn j j≤n }
  ... | inj₂ ψn = inj₂ λ { j (s≤s j≤n) → down ψ ttᵖ tt n ψn j j≤n }

  
  ▷→ : 𝒫 ⊢ᵒ (▷ᵒ (ϕ →ᵒ ψ))  →  𝒫 ⊢ᵒ (▷ᵒ ϕ) →ᵒ (▷ᵒ ψ)
  ▷→ ▷ϕ→ψ n ⊨𝒫n i i≤n ▷ϕi j j<si = 
     let ϕj→ψj = ▷ϕ→ψ n ⊨𝒫n j (≤-trans j<si i≤n) j ≤-refl in
     ϕj→ψj (▷ϕi j j<si)

  ▷∀ : ∀{ϕᵃ : A → Setᵏ} → 𝒫 ⊢ᵒ ▷ᵒ (∀ᵒ ϕᵃ)  →  𝒫 ⊢ᵒ (∀ᵒ λ a → ▷ᵒ (ϕᵃ a))
  ▷∀ 𝒫⊢▷∀ϕᵃ n ⊨𝒫sn a j j< = 𝒫⊢▷∀ϕᵃ n ⊨𝒫sn j j< a

  ▷∃ : ∀{ϕᵃ : A → Setᵏ}{{_ : Inhabited A}} → 𝒫 ⊢ᵒ ▷ᵒ (∃ᵒ ϕᵃ)  →  𝒫 ⊢ᵒ (∃ᵒ λ a → ▷ᵒ (ϕᵃ a))
  ▷∃ 𝒫⊢▷∃ϕᵃ zero ⊨𝒫k = elt , (λ j ())
  ▷∃ {ϕᵃ = ϕᵃ} 𝒫⊢▷∃ϕᵃ (suc k) ⊨𝒫sk 
      with 𝒫⊢▷∃ϕᵃ (suc k) ⊨𝒫sk k ≤-refl
  ... | a , ϕk =
      a , λ {j (s≤s j≤k) →
             let ϕj = down (ϕᵃ a) ttᵖ tt k ϕk j j≤k in
             down (ϕᵃ a) ttᵖ tt j ϕj j ≤-refl}

  ▷pureᵒ : [] ⊢ᵒ ▷ᵒ (p ᵒ) → [] ⊢ᵒ p ᵒ
  ▷pureᵒ ⊢▷ k ttᵖ = ⊢▷ (suc k) tt k (s≤s ≤-refl) 

  ▷→▷ : ∀{𝒫}{P Q : Setᵏ}
     → 𝒫 ⊢ᵒ ▷ᵒ P
     → P ∷ 𝒫 ⊢ᵒ Q
       ------------
     → 𝒫 ⊢ᵒ ▷ᵒ Q
  ▷→▷ {𝒫}{P}{Q} ▷P P⊢Q n ⊨𝒫n =
    let ▷Q = →ᵒE{𝒫}{▷ᵒ P}{▷ᵒ Q}
                (▷→{𝒫}{P}{Q}
                    (monoᵒ{𝒫}{P →ᵒ Q} (→ᵒI{P}{𝒫}{Q} P⊢Q))) ▷P in
    ▷Q n ⊨𝒫n

∀ᵒ-syntax : ∀{Γ}{Δ : Times Γ}{A : Set} → (A → Setᵒ Γ Δ) → Setᵒ Γ Δ
∀ᵒ-syntax = ∀ᵒ
infix 1 ∀ᵒ-syntax
syntax ∀ᵒ-syntax (λ x → P) = ∀ᵒ[ x ] P

∀ᵒ-annot-syntax : ∀{Γ}{Δ : Times Γ} → ∀ (A : Set) → (A → Setᵒ Γ Δ) → Setᵒ Γ Δ
∀ᵒ-annot-syntax A = ∀ᵒ {A = A}
infix 2 ∀ᵒ-annot-syntax
syntax ∀ᵒ-annot-syntax A (λ x → P) = ∀ᵒ[ x ⦂ A ] P

∃ᵒ-syntax : ∀{Γ}{Δ : Times Γ}{A : Set}{{_ : Inhabited A}} → (A → Setᵒ Γ Δ) → Setᵒ Γ Δ
∃ᵒ-syntax = ∃ᵒ
infix 2 ∃ᵒ-syntax
syntax ∃ᵒ-syntax (λ x → P) = ∃ᵒ[ x ] P

