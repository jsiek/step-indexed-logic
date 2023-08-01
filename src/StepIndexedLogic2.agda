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
open import Variables
open import SetO
open import Approx
open import Iteration

downClosed : Setₒ → Set
downClosed S = ∀ n → S n → ∀ k → k ≤ n → S k

RecEnv : Context → Set₁
RecEnv [] = topᵖ 
RecEnv (A ∷ Γ) = (Predₒ A) × RecEnv Γ

downClosedᵈ : ∀{Γ} → RecEnv Γ → Set
downClosedᵈ {[]} δ = ⊤
downClosedᵈ {A ∷ Γ} (P , δ) = (∀ a → downClosed (P a)) × downClosedᵈ δ

tzᵈ : ∀{Γ} → RecEnv Γ → Set
tzᵈ {[]} δ = ⊤
tzᵈ {A ∷ Γ} (P , δ) = (∀ a → (P a) 0) × tzᵈ δ

↓ᵈ : ℕ → ∀{Γ}{A} → Γ ∋ A → RecEnv Γ → RecEnv Γ
↓ᵈ k {A ∷ Γ} {.A} zeroᵒ (P , δ) = ↓ᵖ k P , δ
↓ᵈ k {A ∷ Γ} {B} (sucᵒ x) (P , δ) = P , ↓ᵈ k x δ

timeof : ∀{Γ}{A} → (x : Γ ∋ A) → Times Γ → Time
timeof {B ∷ Γ} zeroᵒ (t ∷ Δ) = t
timeof {B ∷ Γ} (sucᵒ x) (t ∷ Δ) = timeof x Δ

_≡ᵈ_ : ∀{Γ} → RecEnv Γ → RecEnv Γ → Set
_≡ᵈ_ {[]} δ δ′ = ⊤
_≡ᵈ_ {A ∷ Γ} (P , δ) (Q , δ′) = (∀ a → P a ≡ₒ Q a) × δ ≡ᵈ δ′

≡ᵈ-refl : ∀{Γ}{δ : RecEnv Γ} → δ ≡ᵈ δ
≡ᵈ-refl {[]} {δ} = tt
≡ᵈ-refl {A ∷ Γ} {(P , δ)} = (λ a → ≡ₒ-refl refl) , ≡ᵈ-refl

congruent : ∀{Γ : Context} → (RecEnv Γ → Setₒ) → Set₁
congruent S = ∀{δ δ′} → δ ≡ᵈ δ′ → (S δ) ≡ₒ (S δ′)

laters : ∀ (Γ : Context) → Times Γ
laters [] = []
laters (A ∷ Γ) = Later ∷ (laters Γ)

var-now : ∀ (Γ : Context) → ∀{A} → (x : Γ ∋ A) → Times Γ
var-now (B ∷ Γ) zeroᵒ = Now ∷ (laters Γ)
var-now (B ∷ Γ) (sucᵒ x) = Later ∷ (var-now Γ x)

module Member where

  lookup : ∀{Γ}{A} → Γ ∋ A → RecEnv Γ → Predₒ A
  lookup {B ∷ Γ} {.B} zeroᵒ (P , δ) = P
  lookup {B ∷ Γ} {A} (sucᵒ x) (P , δ) = lookup{Γ}{A} x δ

  down-lookup : ∀{Γ}{A}{x}{a : A} → (δ : RecEnv Γ) → downClosedᵈ δ → downClosed (lookup x δ a)
  down-lookup {x = zeroᵒ}{a} (P , δ) (dcP , dcδ) = dcP a
  down-lookup {x = sucᵒ x} (P , δ) (dcP , dcδ) = down-lookup δ dcδ

  ↓-lookup : ∀{Γ}{A}{B}{a}{k}{j}{δ : RecEnv Γ}
     → (x : Γ ∋ A)
     → (y : Γ ∋ B)
     → k ≤ j
     → ↓ k (lookup{Γ}{A} x δ a) ≡ₒ ↓ k (lookup{Γ}{A} x (↓ᵈ j y δ) a)
  ↓-lookup {a = a}{δ = P , δ} zeroᵒ zeroᵒ k≤j = ≡ₒ-sym (j≤k⇒↓kϕ≡[j]ϕ (P a) k≤j)
  ↓-lookup zeroᵒ (sucᵒ y) k≤j = ≡ₒ-refl refl
  ↓-lookup (sucᵒ x) zeroᵒ k≤j = ≡ₒ-refl refl
  ↓-lookup (sucᵒ x) (sucᵒ y) k≤j = ↓-lookup x y k≤j

{-
  lookup-diff : ∀{Γ}{Δ : Times Γ}{A}{B}{δ : RecEnv Γ}{j}
     → (x : Γ ∋ A)
     → (y : Γ ∋ B)
     → timeof x Δ ≢ timeof y Δ
     → lookup{Γ}{A} x (↓ᵈ j y δ) ≡ lookup{Γ}{A} x δ
  lookup-diff {C ∷ Γ} {t ∷ Δ} zeroᵒ zeroᵒ neq = ⊥-elim (neq refl)
  lookup-diff {C ∷ Γ} {t ∷ Δ} zeroᵒ (sucᵒ y) neq = refl
  lookup-diff {C ∷ Γ} {t ∷ Δ} (sucᵒ x) zeroᵒ neq = refl
  lookup-diff {C ∷ Γ} {t ∷ Δ} (sucᵒ x) (sucᵒ y) neq = lookup-diff x y neq

  timeof-diff : ∀{Γ}{Δ : Times Γ}{A}{B} (x : Γ ∋ A) (y : Γ ∋ B)
     → timeof x Δ ≡ Now → timeof y Δ ≡ Later
     → timeof x Δ ≢ timeof y Δ
  timeof-diff x y eq1 eq2 rewrite eq1 | eq2 = λ ()

  timeof-var-now : ∀{Γ}{A}
     → (x : Γ ∋ A)
     → timeof x (var-now Γ x) ≡ Now
  timeof-var-now {B ∷ Γ} zeroᵒ = refl
  timeof-var-now {B ∷ Γ} (sucᵒ x) = timeof-var-now x

  timeof-later : ∀{Γ}{A}
     → (x : Γ ∋ A)
     → (timeof x (laters Γ)) ≡ Later
  timeof-later {B ∷ Γ} zeroᵒ = refl
  timeof-later {B ∷ Γ} (sucᵒ x) = timeof-later x

  good-lookup : ∀{Γ}{A}{a}
    → (x : Γ ∋ A)
    → good-fun (var-now Γ x) (λ δ → lookup x δ a)
  good-lookup {.(A ∷ _)} {A} {a} zeroᵒ zeroᵒ (P , δ) j k k≤j =
     ≡ₒ-sym (lemma17e{_}{P} k≤j)
  good-lookup {.(A ∷ _)} {A} {a} zeroᵒ (sucᵒ y) rewrite timeof-later y =
     λ{(P , δ) j k k≤j → ≡ₒ-refl refl}
  good-lookup {.(_ ∷ _)} {A} {a} (sucᵒ x) zeroᵒ =
     λ{(P , δ) j k k≤j → ≡ₒ-refl refl}
  good-lookup {B ∷ Γ} {A} {a} (sucᵒ x) (sucᵒ y)
      with timeof y (var-now Γ x) in eq-y
  ... | Now = λ{(P , δ) j k k≤j → ↓-lookup x y k≤j }
  ... | Later =
        λ{(P , δ) j k k≤j →
            let eq = (lookup-diff{Γ}{_}{_}{_}{δ}{j} x y
                          (timeof-diff x y (timeof-var-now x) eq-y)) in
            subst (λ X → ↓ (suc k) (lookup x δ a) ≡ₒ ↓ (suc k) (X a))
                  (sym eq) (≡ₒ-refl refl)}

  cong-lookup : ∀{Γ}{A}{δ δ′ : RecEnv Γ}
     → (x : Γ ∋ A)
     → (a : A)
     → δ ≡ᵈ δ′
     → lookup x δ a ≡ₒ lookup x δ′ a
  cong-lookup {B ∷ Γ} {.B}{P , δ}{P′ , δ′} zeroᵒ a (P=P′ , d=d′) = P=P′ a
  cong-lookup {B ∷ Γ} {A}{P , δ}{P′ , δ′} (sucᵒ x) a (P=P′ , d=d′) =
     cong-lookup x a d=d′

  tz-lookup : ∀{Γ}{A}{x}{a : A} → (δ : RecEnv Γ) → tzᵈ δ → lookup x δ a 0
  tz-lookup {x = zeroᵒ} {a} (P , δ) (tzP , tzδ) = tzP a
  tz-lookup {x = sucᵒ x} (P , δ) (tzP , tzδ) = tz-lookup δ tzδ

  congruent-lookup : ∀{Γ}{A}
     → (x : Γ ∋ A)
     → (a : A)
     → congruent (λ δ → lookup x δ a)
  congruent-lookup {Γ}{A} x a d=d′ = cong-lookup x a d=d′
-}

strongly-nonexpansive : ∀{Γ}{A} → (x : Γ ∋ A) → (RecEnv Γ → Setₒ) → Set₁
strongly-nonexpansive x F = ∀ δ j k → k ≤ j → F δ ≡ₒ[ k ] F (↓ᵈ j x δ)

strongly-contractive : ∀{Γ}{A} → (x : Γ ∋ A) → (RecEnv Γ → Setₒ) → Set₁
strongly-contractive x F = ∀ δ j k → k ≤ j → F δ ≡ₒ[ suc k ] F (↓ᵈ j x δ)

strong-var : ∀{Γ}{A} → (x : Γ ∋ A) → Time → (RecEnv Γ → Setₒ) → Set₁
strong-var x Now F = strongly-nonexpansive x F
strong-var x Later F = strongly-contractive x F

strong-fun : ∀{Γ} → Times Γ → (RecEnv Γ → Setₒ) → Set₁
strong-fun {Γ} Δ F = ∀{A} (x : Γ ∋ A) → strong-var x (timeof x Δ) F

record Setᵒ (Γ : Context) (Δ : Times Γ) : Set₁ where
  field
    # : RecEnv Γ → Setₒ
{-    
    down : ∀ δ → downClosedᵈ δ → downClosed (# δ)
    strong : strong-fun Δ #
    congr : congruent #
-}    
open Setᵒ public

postulate down : ∀{Γ}{Δ} (ϕ : Setᵒ Γ Δ) → ∀ δ → downClosedᵈ δ → downClosed (# ϕ δ)
postulate strong : ∀{Γ}{Δ} (ϕ : Setᵒ Γ Δ) → strong-fun Δ (# ϕ)
postulate congr : ∀{Γ}{Δ} (ϕ : Setᵒ Γ Δ) → congruent (# ϕ)

{---------------------- Membership in Recursive Predicate ---------------------}


⟅_⟆ : ∀{A}{Γ}{Δ} → (A → Setᵒ (A ∷ Γ) (Later ∷ Δ)) → RecEnv Γ → (Predₒ A → Predₒ A)
⟅ Sᵃ ⟆  δ μS = λ a → # (Sᵃ a) (μS , δ)

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

▷ : ∀{Γ} → (RecEnv Γ → ℕ → Set) → (RecEnv Γ → ℕ → Set)
▷ ϕ δ k = ∀ j → j < k → ϕ δ j

down-▷ : ∀{Γ}{Δ : Times Γ}{ϕ : Setᵒ Γ Δ}
  → ∀ δ → downClosedᵈ δ → downClosed (▷ (# ϕ) δ)
down-▷ {Γ}{Δ}{ϕ} δ down-δ n ▷ϕn k k≤n j j<k = ▷ϕn j (≤-trans j<k k≤n)


module _ where
 abstract

  _∈_ : ∀{Γ}{A} → A → (x : Γ ∋ A) → Setᵒ Γ (var-now Γ x)
  a ∈ x = record { # = λ δ → (lookup x δ) a }
{-
; down = down-lookup
           ; tz = tz-lookup
           ; good = good-lookup x
           ; congr = congruent-lookup x a
           }
           -}
    where open Member using (lookup)

{---------------------- Later Operator ---------------------}

  ▷ᵒ : ∀{Γ}{Δ : Times Γ}
     → Setᵒ Γ Δ
       -----------------
     → Setᵒ Γ (laters Γ)
  ▷ᵒ S = record { # = λ δ k → ▷ (# S) δ k }

  ▷ᵒ≡ : ∀{Γ}{Δ}{ϕ : Setᵒ Γ Δ}
    → ▷ᵒ ϕ ≡ record { # = (λ δ k → ▷ (# ϕ) δ k) }
  ▷ᵒ≡ {Γ}{Δ}{ϕ} = let x = # (▷ᵒ ϕ) in refl

  ▷sk : ∀{Γ}{Δ}{ϕ : Setᵒ Γ Δ}{δ : RecEnv Γ}{k}
     → downClosedᵈ δ
     → ▷ (# ϕ) δ (suc k) ⇔ (# ϕ) δ k
  ▷sk {Γ}{Δ}{ϕ}{δ}{k} down-δ =
     (λ ▷ϕsk → ▷ϕsk k ≤-refl) , λ ϕk j j<sk → down ϕ δ down-δ k ϕk j (≤-pred j<sk)



{-
; down = {!!}
                ; tz = {!!}
                ; good = {!!}
                ; congr = {!!}
                }
                -}

{---------------------- Recursive Predicate -----------------------------------}

mu : ∀ {Γ}{Δ : Times Γ}{A} → (A → Setᵒ (A ∷ Γ) (Later ∷ Δ)) → (RecEnv Γ → A → Setₒ)
mu Sᵃ δ a k = ((⟅ Sᵃ ⟆ δ) ^ (1 + k)) (λ a k → ⊤) a k

abstract
  μᵒ : ∀{Γ}{Δ : Times Γ}{A}
     → (A → Setᵒ (A ∷ Γ) (Later ∷ Δ))
     → (A → Setᵒ Γ Δ)
  μᵒ {Γ}{Δ}{A} Sᵃ a =
    record { # = λ δ → mu Sᵃ δ a }
{-    
           ; down = {!!}
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
    record { # = λ δ k → ∀ (a : A) → # (P a) δ k }
{-    
           ; down = {!!}
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
    record { # = λ δ k → Σ[ a ∈ A ] # (P a) δ k }
{-    
           ; down = {!!}
           ; tz = {!!}
           ; good = {!!}
           ; congr = {!!}
           }
           -}

  #∃ᵒ≡ : ∀{Γ}{Δ : Times Γ}{A : Set}{{_ : Inhabited A}}{Sᵃ : A → Setᵒ Γ Δ}{δ}{k}
     → (# (∃ᵒ Sᵃ) δ k) ≡ (Σ[ a ∈ A ] (# (Sᵃ a) δ k))
  #∃ᵒ≡ = refl
  
  

{---------------------- Pure -----------------------------------------}

  _ᵒ : ∀{Γ} → Set → Setᵒ Γ (laters Γ)
  p ᵒ = record { # = λ δ k → p }
{-  
               ; down = {!!}
               ; tz = {!!}
               ; good = {!!}
               ; congr = {!!}
               }
-}               
  #pureᵒ≡ : ∀{p}{Γ}{δ : RecEnv Γ}{k} → # (p ᵒ) δ (suc k) ≡ p
  #pureᵒ≡ = refl

{---------------------- False -----------------------------------------}

  ⊥ᵒ : ∀{Γ} → Setᵒ Γ (laters Γ)
  ⊥ᵒ = ⊥ ᵒ

{---------------------- True -----------------------------------------}

  ⊤ᵒ : ∀{Γ} → Setᵒ Γ (laters Γ)
  ⊤ᵒ = record { # = λ δ k → ⊤ }
{-  
               ; down = {!!}
               ; tz = {!!}
               ; good = {!!}
               ; congr = {!!}
               }
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
  S ×ᵒ T = record { # = λ δ k → # S δ k × # T δ k }
{-  
                  ; down = {!!}
                  ; tz = {!!}
                  ; good = {!!}
                  ; congr = {!!}
                  }
-}                  
  #×ᵒ≡ : ∀{Γ}{Δ₁ Δ₂ : Times Γ}{ϕ : Setᵒ Γ Δ₁}{ψ : Setᵒ Γ Δ₂}{δ}{k}
       → (# (ϕ ×ᵒ ψ) δ k) ≡ (# ϕ δ k × # ψ δ k)
  #×ᵒ≡ {Γ}{Δ₁}{Δ₂}{ϕ}{ψ}{δ}{k} = refl

{---------------------- Disjunction -----------------------------------------}

  infixr 7 _⊎ᵒ_
  _⊎ᵒ_ : ∀{Γ}{Δ₁ Δ₂ : Times Γ}
     → Setᵒ Γ Δ₁
     → Setᵒ Γ Δ₂
       ------------------------
     → Setᵒ Γ (combine Δ₁ Δ₂)
  S ⊎ᵒ T = record { # = λ δ k → # S δ k ⊎ # T δ k }
{-  
                  ; down = {!!}
                  ; tz = {!!}
                  ; good = {!!}
                  ; congr = {!!}
                  }
                  -}

  #⊎ᵒ≡ : ∀{Γ}{Δ₁ Δ₂ : Times Γ}{ϕ : Setᵒ Γ Δ₁}{ψ : Setᵒ Γ Δ₂}{δ}{k}
       → (# (ϕ ⊎ᵒ ψ) δ k) ≡ (# ϕ δ k ⊎ # ψ δ k)
  #⊎ᵒ≡ {Γ}{Δ₁}{Δ₂}{ϕ}{ψ}{δ}{k} = refl
  
{---------------------- Implication -----------------------------------------}

  infixr 6 _→ᵒ_
  _→ᵒ_ : ∀{Γ}{Δ₁ Δ₂ : Times Γ}
     → Setᵒ Γ Δ₁
     → Setᵒ Γ Δ₂
       ------------------------
     → Setᵒ Γ (combine Δ₁ Δ₂)
  S →ᵒ T = record { # = λ δ k → ∀ j → j ≤ k → # S δ j → # T δ j }
{-  
                  ; down = {!!}
                  ; tz = {!!}
                  ; good = {!!}
                  ; congr = {!!}
                  }
-}                  
  #→ᵒ≡ : ∀{Γ}{Δ₁ Δ₂ : Times Γ}{ϕ : Setᵒ Γ Δ₁}{ψ : Setᵒ Γ Δ₂}{δ}{k}
       → (# (ϕ →ᵒ ψ) δ k) ≡ (∀ j → j ≤ k → # ϕ δ j → # ψ δ j)
  #→ᵒ≡ {Γ}{Δ₁}{Δ₂}{ϕ}{ψ}{δ}{k} = refl

{---------------------- Let for Predicates -----------------------------------------}

  letᵒ : ∀{A}{Γ}{t}{Δ} → (A → Setᵒ Γ Δ) → Setᵒ (A ∷ Γ) (t ∷ Δ) → Setᵒ Γ Δ   
  letᵒ Sᵃ T = record { # = λ δ k →  # T ((λ a k → # (Sᵃ a) δ k) , δ) k }
{-  
                     ; down = {!!}
                     ; tz = {!!}
                     ; good = {!!}
                     ; congr = {!!}
                     }
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

  let-×ᵒ : ∀{A}{P : A → Setᵒ [] []}{ϕ ψ : Setᵒ (A ∷ []) (Later ∷ [])}
     → letᵒ P (ϕ ×ᵒ ψ) ≡ (letᵒ P ϕ) ×ᵒ (letᵒ P ψ)
  let-×ᵒ = refl

  let-⊎ᵒ : ∀{A}{P : A → Setᵒ [] []}{ϕ ψ : Setᵒ (A ∷ []) (Later ∷ [])}
     → letᵒ P (ϕ ⊎ᵒ ψ) ≡ (letᵒ P ϕ) ⊎ᵒ (letᵒ P ψ)
  let-⊎ᵒ {A}{P}{ϕ}{ψ} = refl

  let-∀ᵒ : ∀{A}{B}{P : A → Setᵒ [] []}{ϕᵇ  : B → Setᵒ (A ∷ []) (Later ∷ [])}
     → letᵒ P (∀ᵒ ϕᵇ) ≡ ∀ᵒ λ b →  (letᵒ P (ϕᵇ b))
  let-∀ᵒ {A}{B}{P}{ϕᵇ} = refl

  let-∃ᵒ : ∀{A}{B}{{_ : Inhabited B}}{P : A → Setᵒ [] []}{ϕᵇ  : B → Setᵒ (A ∷ []) (Later ∷ [])}
     → letᵒ P (∃ᵒ ϕᵇ) ≡ ∃ᵒ λ b →  (letᵒ P (ϕᵇ b))
  let-∃ᵒ {A}{B}{P}{ϕᵇ} = refl

  {-# REWRITE let-▷ᵒ #-}
  {-# REWRITE let-∈ #-}
  {-# REWRITE let-pureᵒ #-}
  {-# REWRITE let-×ᵒ #-}
  {-# REWRITE let-⊎ᵒ #-}
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

module _ where
  infix 2 _≡ᵒ_
  _≡ᵒ_ : ∀{Γ}{Δ : Times Γ} → Setᵒ Γ Δ → Setᵒ Γ Δ → Set₁
  S ≡ᵒ T = ∀ δ → # S δ ≡ₒ # T δ

  ≡ₒ⇒≡ᵒ : ∀{ϕ ψ : Setᵒ Γ Δ} → (∀ δ → # ϕ δ ≡ₒ # ψ δ) → ϕ ≡ᵒ ψ
  ≡ₒ⇒≡ᵒ P≡ₒQ = P≡ₒQ

  ≡ᵒ⇒≡ₒ : ∀{S T : Setᵒ Γ Δ}{δ} → S ≡ᵒ T → # S δ ≡ₒ # T δ
  ≡ᵒ⇒≡ₒ {S}{T}{δ}{k} {δ′} eq = eq δ′

  ≡ᵒ-intro : ∀{ϕ ψ : Setᵒ Γ Δ} → (∀ δ k → # ϕ δ k ⇔ # ψ δ k) → ϕ ≡ᵒ ψ
  ≡ᵒ-intro P⇔Q k = P⇔Q k
  
  ≡ᵒ-elim : ∀{S T : Setᵒ Γ Δ}{δ}{k} → S ≡ᵒ T → # S δ k ⇔ # T δ k
  ≡ᵒ-elim {S}{T}{δ}{k} {δ′}{k′} eq = eq δ′ k′
  
  ≡ᵒ-refl : ϕ ≡ ψ → ϕ ≡ᵒ ψ
  ≡ᵒ-refl {ϕ} refl ttᵖ k = (λ z → z) , (λ z → z)

  ≡ᵒ-sym : ϕ ≡ᵒ ψ → ψ ≡ᵒ ϕ
  ≡ᵒ-sym {ϕ}{ψ} PQ ttᵖ k
      with PQ ttᵖ k
  ... | (ϕ⇒ψ , ψ⇒ϕ) = ψ⇒ϕ , ϕ⇒ψ

  ≡ᵒ-trans : ϕ ≡ᵒ ψ → ψ ≡ᵒ þ → ϕ ≡ᵒ þ
  ≡ᵒ-trans PQ QR ttᵖ k
      with PQ ttᵖ k | QR ttᵖ k
  ... | (ϕ⇒ψ , ψ⇒ϕ) | (ψ⇒þ , þ⇒ψ) = (λ z → ψ⇒þ (ϕ⇒ψ z)) , (λ z → ψ⇒ϕ (þ⇒ψ z))

lemma15b-env-fun : ∀{Γ}{Δ}{A}{δ : RecEnv Γ}{P : Predₒ A}
  (k j : ℕ) (Sᵃ : A → Setᵒ (A ∷ Γ) (Later ∷ Δ)) (a : A)
  → j ≤ k → ((⟅ Sᵃ ⟆ δ) ^ j) P a ≡ₒ[ j ] ((⟅ Sᵃ ⟆ δ) ^ k) P a
lemma15b-env-fun {Γ}{Δ}{A}{δ}{P} k j Sᵃ a j≤k =
    ((⟅ Sᵃ ⟆ δ) ^ j) P a
  ⩦⟨ {!!} ⟩
    ((⟅ Sᵃ ⟆ δ) ^ k) P a
  ∎

lemma18a : ∀{Γ}{Δ : Times Γ}{A} (k : ℕ) (Sᵃ : A → Setᵒ (A ∷ Γ) (Later ∷ Δ)) (a : A) (δ : RecEnv Γ)
  → mu Sᵃ δ a ≡ₒ[ k ] ((⟅ Sᵃ ⟆ δ) ^ k) (λ a k → ⊤) a
lemma18a {Γ}{Δ}{A} k Sᵃ a δ j = to k j , fro k j
  where
  to : ∀ k j → ↓ k (mu Sᵃ δ a) j → ↓ k ((⟅ Sᵃ ⟆ δ ^ k) (λ a₁ k₁ → ⊤) a) j
  to k j (j<k , mu-j) = j<k ,
     proj₂ (proj₁ (lemma15b-env-fun k (suc j) Sᵃ a j<k j) (≤-refl , mu-j))
  fro : ∀ k j → ↓ k ((⟅ Sᵃ ⟆ δ ^ k) (λ a₁ k₁ → ⊤) a) j → ↓ k (mu Sᵃ δ a) j
  fro k j (j<k , Sᵏj) =
     j<k , (proj₂ (proj₂ (lemma15b-env-fun k (suc j) Sᵃ a j<k j) (≤-refl , Sᵏj)))

lemma18b : ∀{Γ}{Δ : Times Γ}{A} (k : ℕ) (Sᵃ : A → Setᵒ (A ∷ Γ) (Later ∷ Δ)) (a : A) (δ : RecEnv Γ)
     → # (Sᵃ a) (mu Sᵃ δ , δ) ≡ₒ[ 1 + k ] ((⟅ Sᵃ ⟆ δ) ^ (1 + k)) (λ a k → ⊤) a
lemma18b {A}{Γ}{Δ} k Sᵃ a δ =
       # (Sᵃ a) (mu Sᵃ δ , δ)
   ⩦⟨ strong (Sᵃ a) zeroᵒ (mu Sᵃ δ , δ) k k ≤-refl ⟩
       # (Sᵃ a) (↓ᵖ k (mu Sᵃ δ) , δ)
   ⩦⟨ cong-↓ (λ a → congr (Sᵃ a) ((λ a → lemma18a k Sᵃ a δ) , ≡ᵈ-refl)) a ⟩
       # (Sᵃ a) (↓ᵖ k (((⟅ Sᵃ ⟆ δ) ^ k) (λ a k → ⊤)) , δ)
   ⩦⟨ ≡ₒ-sym (strong (Sᵃ a) zeroᵒ ((((⟅ Sᵃ ⟆ δ) ^ k) (λ a k → ⊤)) , δ) k k ≤-refl) ⟩
       # (Sᵃ a) (((⟅ Sᵃ ⟆ δ) ^ k) (λ a k → ⊤) , δ)
   ⩦⟨ ≡ₒ-refl refl ⟩
       ((⟅ Sᵃ ⟆ δ) ^ (suc k)) (λ a k → ⊤) a
   ∎

lemma19a : ∀{Γ}{Δ : Times Γ}{A} (Sᵃ : A → Setᵒ (A ∷ Γ) (Later ∷ Δ)) (a : A) (δ : RecEnv Γ) (k : ℕ)
  → mu Sᵃ δ a ≡ₒ[ k ] # (Sᵃ a) ((λ a k → mu Sᵃ δ a k) , δ)
lemma19a Sᵃ a δ k =
    let f = (⟅ Sᵃ ⟆ δ) in
      mu Sᵃ δ a
  ⩦⟨ lemma18a k Sᵃ a δ  ⟩
      (f ^ k) (λ a k → ⊤) a
  ⩦⟨ lemma15b-env-fun (suc k) k Sᵃ a (n≤1+n k) ⟩
      (f ^ (suc k)) (λ a k → ⊤) a
  ⩦⟨ ≡ₒ-sym (lemma17{((f ^ (suc k)) (λ a k → ⊤)) a} k) ⟩
      ↓ (suc k) ((f ^ (suc k)) (λ a k → ⊤) a)
   ⩦⟨ cong-↓ (λ a → ≡ₒ-sym (lemma18b k Sᵃ a δ)) a ⟩
      ↓ (suc k) (# (Sᵃ a) (mu Sᵃ δ , δ))
   ⩦⟨ lemma17{(# (Sᵃ a) (mu Sᵃ δ , δ))} k ⟩
      # (Sᵃ a) (mu Sᵃ δ , δ)
   ∎

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
  substᵒ ϕ=ψ 𝒫⊢ϕ n ⊨𝒫n = ⇔-to (ϕ=ψ ttᵖ n) (𝒫⊢ϕ n ⊨𝒫n)

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

