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
   using (≤-refl; ≤-antisym; ≤-trans; ≤-step; ≤⇒≤′; ≤′⇒≤; n≤1+n; <⇒≤)
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

Setₒ : Set₁
Setₒ = ℕ → Set

Predₒ : Set → Set₁
Predₒ A = A → Setₒ

downClosed : Setₒ → Set
downClosed S = ∀ n → S n → ∀ k → k ≤ n → S k

infix 2 _≡ₒ_
_≡ₒ_ : Setₒ → Setₒ → Set
S ≡ₒ T = ∀ k → S k ⇔ T k

≡ₒ-refl : ∀{S T : Setₒ}
  → S ≡ T
  → S ≡ₒ T
≡ₒ-refl refl i = ⩦-refl refl

≡ₒ-sym : ∀{S T : Setₒ}
  → S ≡ₒ T
  → T ≡ₒ S
≡ₒ-sym ST i = ⩦-sym (ST i)

≡ₒ-trans : ∀{S T R : Setₒ}
  → S ≡ₒ T
  → T ≡ₒ R
  → S ≡ₒ R
≡ₒ-trans ST TR i = ⩦-trans (ST i) (TR i)

instance
  SIL-Eqₒ : EquivalenceRelation Setₒ
  SIL-Eqₒ = record { _⩦_ = _≡ₒ_ ; ⩦-refl = ≡ₒ-refl
                   ; ⩦-sym = ≡ₒ-sym ; ⩦-trans = ≡ₒ-trans }

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

RecEnv : Context → Set₁
RecEnv [] = topᵖ 
RecEnv (A ∷ Γ) = (Predₒ A) × RecEnv Γ

downClosedᵈ : ∀{Γ} → RecEnv Γ → Set
downClosedᵈ {[]} δ = ⊤
downClosedᵈ {A ∷ Γ} (P , δ) = (∀ a → downClosed (P a)) × downClosedᵈ δ

tzᵈ : ∀{Γ} → RecEnv Γ → Set
tzᵈ {[]} δ = ⊤
tzᵈ {A ∷ Γ} (P , δ) = (∀ a → (P a) 0) × tzᵈ δ

↓ : ℕ → Setₒ → Setₒ
↓ k S zero = ⊤
↓ k S (suc j) = suc j < k × (S (suc j))

↓ᵖ : ℕ → ∀{A} → Predₒ A → Predₒ A
↓ᵖ j P a = ↓ j (P a)

↓ᵈ : ℕ → ∀{Γ}{A} → Γ ∋ A → RecEnv Γ → RecEnv Γ
↓ᵈ k {A ∷ Γ} {.A} zeroᵒ (P , δ) = ↓ᵖ k P , δ
↓ᵈ k {A ∷ Γ} {B} (sucᵒ x) (P , δ) = P , ↓ᵈ k x δ

congᵖ : ∀{A}{B} (F : Predₒ A → Predₒ B) → Set₁
congᵖ F = ∀ {P Q} → (∀ a → P a ≡ₒ Q a) → ∀ b → (F P b) ≡ₒ (F Q b)

cong-↓ : ∀{A}{k : ℕ} → congᵖ{A}{A} (↓ᵖ k)
cong-↓ {A} {k} {P} {Q} eq a zero =
   (λ _ → tt) , λ _ → tt
cong-↓ {A} {k} {P} {Q} eq a (suc i) =
   (λ {(si≤k , Pasi) → si≤k , (proj₁ (eq a (suc i)) Pasi)})
   ,
   λ {(si≤k , Qasi) → si≤k , (proj₂ (eq a (suc i)) Qasi)}

good-var : ∀{Γ}{A} → (x : Γ ∋ A) → Time → (RecEnv Γ → Setₒ) → Set₁
good-var {Γ}{A} x Now S =
    ∀ δ j k → k ≤ j → ↓ k (S δ) ≡ₒ ↓ k (S (↓ᵈ j x δ))
good-var {Γ}{A} x Later S =
    ∀ δ j k → k ≤ j → ↓ (suc k) (S δ) ≡ₒ ↓ (suc k) (S (↓ᵈ j x δ))

timeof : ∀{Γ}{A} → (x : Γ ∋ A) → Times Γ → Time
timeof {B ∷ Γ} zeroᵒ (t ∷ Δ) = t
timeof {B ∷ Γ} (sucᵒ x) (t ∷ Δ) = timeof x Δ

good-fun : ∀{Γ} → Times Γ → (RecEnv Γ → Setₒ) → Set₁
good-fun {Γ} Δ S = ∀{A} (x : Γ ∋ A) → good-var x (timeof x Δ) S

_≡ᵈ_ : ∀{Γ} → RecEnv Γ → RecEnv Γ → Set
_≡ᵈ_ {[]} δ δ′ = ⊤
_≡ᵈ_ {A ∷ Γ} (P , δ) (Q , δ′) = (∀ a → P a ≡ₒ Q a) × δ ≡ᵈ δ′

congruent : ∀{Γ : Context} → (RecEnv Γ → Setₒ) → Set₁
congruent S = ∀{δ δ′} → δ ≡ᵈ δ′ → (S δ) ≡ₒ (S δ′)

laters : ∀ (Γ : Context) → Times Γ
laters [] = []
laters (A ∷ Γ) = Later ∷ (laters Γ)

var-now : ∀ (Γ : Context) → ∀{A} → (x : Γ ∋ A) → Times Γ
var-now (B ∷ Γ) zeroᵒ = Now ∷ (laters Γ)
var-now (B ∷ Γ) (sucᵒ x) = Later ∷ (var-now Γ x)

module Lemma17 where

  lemma17 : ∀{A}{P : Predₒ A}{k}{a : A} →  ↓ᵖ k (↓ᵖ (suc k) P) a ≡ₒ ↓ᵖ k P a
  lemma17 {A} {P} {k} {a} zero = (λ _ → tt) , (λ _ → tt)
  lemma17 {A} {P} {k} {a} (suc i) =
    (λ {(x , (y , z)) → x , z}) , (λ {(x , y) → x , ((s≤s (<⇒≤ x)) , y)})

  lemma17b : ∀{A}{P : Predₒ A}{j}{k}{a : A}
     → suc j ≤′ k
     → ↓ᵖ j (↓ᵖ k P) a ≡ₒ ↓ᵖ j P a
  lemma17b {A} {P} {j} {.(suc j)} {a} _≤′_.≤′-refl = lemma17{A}{P}{j}{a}
  lemma17b {A} {P} {j} {suc k} {a} (≤′-step j≤k) =
      ↓ᵖ j (↓ᵖ (suc k) P) a           ⩦⟨ ≡ₒ-sym (lemma17b{A}{↓ᵖ (suc k) P} j≤k) ⟩
      ↓ᵖ j (↓ᵖ k (↓ᵖ (suc k) P)) a      ⩦⟨ E1 ⟩
      ↓ᵖ j (↓ᵖ k P) a                   ⩦⟨ lemma17b{A}{P}{j}{k}{a} j≤k ⟩ 
      ↓ᵖ j P a   ∎
      where
      E1 = cong-↓{A}{j}{(↓ᵖ k (↓ᵖ (suc k) P))}{(↓ᵖ k P)}
           (λ a → lemma17{A}{P}{k}{a}) a 

  lemma17c : ∀{A}{P : Predₒ A}{j}{k}{a : A}
     → j < k
     → ↓ᵖ j (↓ᵖ k P) a ≡ₒ ↓ᵖ j P a
  lemma17c {A} {P} {j} {k} {a} j<k = lemma17b{A}{P}{j}{k}{a} (≤⇒≤′ j<k)

  lemma17f : ∀{S : Setₒ}{k}
       → ↓ k (↓ k S) ≡ₒ ↓ k S
  lemma17f {S} {k} zero = (λ x → tt) , (λ x → tt)
  lemma17f {S} {k} (suc i) = (λ {(x , (y , z)) → y , z}) , λ {(x , y) → x , (x , y)}

  lemma17d : ∀{A}{P : Predₒ A}{k}{a : A}
       → ↓ᵖ k (↓ᵖ k P) a ≡ₒ ↓ᵖ k P a
  lemma17d {A} {P} {k} {a} zero = (λ x → tt) , (λ x → tt)
  lemma17d {A} {P} {k} {a} (suc i) = (λ {(x , (y , z)) → y , z}) , λ {(x , y) → x , (x , y)}

  lemma17e : ∀{A}{P : Predₒ A}{j}{k}{a : A}
     → j ≤ k
     → ↓ᵖ j (↓ᵖ k P) a ≡ₒ ↓ᵖ j P a
  lemma17e {A} {P} {j} {k} {a} j≤k
      with ≤⇒≤′ j≤k
  ... | _≤′_.≤′-refl = lemma17d{A}{P}
  ... | ≤′-step j≤n = lemma17c{A}{P} (s≤s (≤′⇒≤ j≤n))

module Member where

  open Lemma17 using (lemma17e)

  lookup : ∀{Γ}{A} → Γ ∋ A → RecEnv Γ → Predₒ A
  lookup {B ∷ Γ} {.B} zeroᵒ (P , δ) = P
  lookup {B ∷ Γ} {A} (sucᵒ x) (P , δ) = lookup{Γ}{A} x δ

{-
  ↓-lookup : ∀{Γ}{A}{B}{a}{k}{j}{δ : RecEnv Γ}
     → (x : Γ ∋ A)
     → (y : Γ ∋ B)
     → k ≤ j
     → ↓ k (lookup{Γ}{A} x δ a) ≡ₒ ↓ k (lookup{Γ}{A} x (↓ᵈ j y δ) a)
  ↓-lookup {δ = P , δ} zeroᵒ zeroᵒ k≤j = ≡ₒ-sym (lemma17e{P = P} k≤j)
  ↓-lookup zeroᵒ (sucᵒ y) k≤j = ≡ₒ-refl refl
  ↓-lookup (sucᵒ x) zeroᵒ k≤j = ≡ₒ-refl refl
  ↓-lookup (sucᵒ x) (sucᵒ y) k≤j = ↓-lookup x y k≤j

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

  down-lookup : ∀{Γ}{A}{x}{a : A} → (δ : RecEnv Γ) → downClosedᵈ δ → downClosed (lookup x δ a)
  down-lookup {x = zeroᵒ}{a} (P , δ) (dcP , dcδ) = dcP a
  down-lookup {x = sucᵒ x} (P , δ) (dcP , dcδ) = down-lookup δ dcδ

  congruent-lookup : ∀{Γ}{A}
     → (x : Γ ∋ A)
     → (a : A)
     → congruent (λ δ → lookup x δ a)
  congruent-lookup {Γ}{A} x a d=d′ = cong-lookup x a d=d′
-}

record Setᵒ (Γ : Context) (Δ : Times Γ) : Set₁ where
  field
    # : RecEnv Γ → Setₒ
{-    
    down : ∀ δ → downClosedᵈ δ → downClosed (# δ)
    tz : ∀ δ → tzᵈ δ → # δ 0
    good : good-fun Δ #
    congr : congruent #
-}    
open Setᵒ public

{---------------------- Membership in Recursive Predicate ---------------------}






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

abstract
  ▷ᵒ : ∀{Γ}{Δ : Times Γ}
     → Setᵒ Γ Δ
       -----------------
     → Setᵒ Γ (laters Γ)
  ▷ᵒ S = record { # = λ { δ zero → ⊤ ; δ (suc k) → # S δ k } }
{-
; down = {!!}
                ; tz = {!!}
                ; good = {!!}
                ; congr = {!!}
                }
                -}

{---------------------- Recursive Predicate -----------------------------------}

infixr 8 _^_
_^_ : ∀ {ℓ} {A : Set ℓ} → (A → A) → ℕ → (A → A)
f ^ zero     =  id
f ^ (suc n)  =  f ∘ (f ^ n)

⟅_⟆ : ∀{A}{Γ}{Δ} → (A → Setᵒ (A ∷ Γ) (Later ∷ Δ)) → RecEnv Γ → (Predₒ A → Predₒ A)
⟅ Sᵃ ⟆  δ μS = λ a → # (Sᵃ a) (μS , δ)

abstract
  μᵒ : ∀{Γ}{Δ : Times Γ}{A}
     → (A → Setᵒ (A ∷ Γ) (Later ∷ Δ))
     → (A → Setᵒ Γ Δ)
  μᵒ {Γ}{Δ}{A} Sᵃ a =
    record { # = λ δ k → ((⟅ Sᵃ ⟆ δ) ^ (1 + k)) (λ a k → ⊤) a k }
{-    
           ; down = {!!}
           ; tz = {!!}
           ; good = {!!}
           ; congr = {!!}
           }
-}

  #μᵒ≡ : ∀{Γ}{Δ : Times Γ}{A}{Sᵃ : A → Setᵒ (A ∷ Γ) (Later ∷ Δ)}{a : A}{δ}{k}
     → # (μᵒ Sᵃ a) δ k ≡ ((⟅ Sᵃ ⟆ δ) ^ (1 + k)) (λ a k → ⊤) a k
  #μᵒ≡ = refl


{---------------------- Forall -----------------------------------------}

abstract
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

∀ᵒ-syntax = ∀ᵒ
infix 1 ∀ᵒ-syntax
syntax ∀ᵒ-syntax (λ x → P) = ∀ᵒ[ x ] P

∀ᵒ-annot : ∀{Γ}{Δ : Times Γ} → ∀ A → (A → Setᵒ Γ Δ) → Setᵒ Γ Δ
∀ᵒ-annot A = ∀ᵒ{A = A}

∀ᵒ-annot-syntax = ∀ᵒ-annot
infix 2 ∀ᵒ-annot-syntax
syntax ∀ᵒ-annot-syntax A (λ x → P) = ∀ᵒ[ x ⦂ A ] P

{---------------------- Exists -----------------------------------------}

record Inhabited (A : Set) : Set where
  field
    elt : A
open Inhabited {{...}} public

instance
  ℕ-Inhabited : Inhabited ℕ
  ℕ-Inhabited = record { elt = zero }

abstract
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
  
  
∃ᵒ-syntax = ∃ᵒ
infix 2 ∃ᵒ-syntax
syntax ∃ᵒ-syntax (λ x → P) = ∃ᵒ[ x ] P

{---------------------- Pure -----------------------------------------}

abstract
  _ᵒ : ∀{Γ} → Set → Setᵒ Γ (laters Γ)
  p ᵒ = record { # = λ { δ 0 → ⊤ ; δ (suc k) → p } }
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

abstract
  ⊥ᵒ : ∀{Γ} → Setᵒ Γ (laters Γ)
  ⊥ᵒ = ⊥ ᵒ

{---------------------- True -----------------------------------------}

abstract
  ⊤ᵒ : ∀{Γ} → Setᵒ Γ (laters Γ)
  ⊤ᵒ = record { # = λ δ k → ⊤ }
{-  
               ; down = {!!}
               ; tz = {!!}
               ; good = {!!}
               ; congr = {!!}
               }
 -}

abstract
  #⊤ᵒ≡⊤ : ∀{Γ}{δ : RecEnv Γ}{k} → # ⊤ᵒ δ k ≡ ⊤
  #⊤ᵒ≡⊤ = refl

{---------------------- Conjunction -----------------------------------------}

choose : Time → Time → Time
choose Now Now = Now
choose Now Later = Now
choose Later Now = Now
choose Later Later = Later

combine : ∀{Γ} (Δ₁ Δ₂ : Times Γ) → Times Γ
combine {[]} Δ₁ Δ₂ = []
combine {A ∷ Γ} (x ∷ Δ₁) (y ∷ Δ₂) = (choose x y) ∷ (combine Δ₁ Δ₂)

abstract
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

{---------------------- Disjunction -----------------------------------------}

abstract
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

abstract
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

{---------------------- Let for Predicates -----------------------------------------}

abstract
  letᵒ : ∀{A}{Γ}{t}{Δ} → (A → Setᵒ Γ Δ) → Setᵒ (A ∷ Γ) (t ∷ Δ) → Setᵒ Γ Δ   
  letᵒ Sᵃ T = record { # = λ δ k →  # T ((λ a k → # (Sᵃ a) δ k) , δ) k }
{-  
                     ; down = {!!}
                     ; tz = {!!}
                     ; good = {!!}
                     ; congr = {!!}
                     }
-}
abstract
  let-▷ᵒ∈-to : ∀{A}{P : A → Setᵒ [] []}{a : A}{δ}{k}
     → # (letᵒ P (▷ᵒ (a ∈ zeroᵒ))) δ k → # (▷ᵒ (P a)) δ k
  let-▷ᵒ∈-to {A} {P} {a} {δ} {zero} letP▷ = tt
  let-▷ᵒ∈-to {A} {P} {a} {δ} {suc k} letP▷ = letP▷

  let-▷ᵒ∈-fro : ∀{A}{P : A → Setᵒ [] []}{a : A}{δ}{k}
      → # (▷ᵒ (P a)) δ k → # (letᵒ P (▷ᵒ (a ∈ zeroᵒ))) δ k
  let-▷ᵒ∈-fro {A} {P} {a} {δ} {zero} ▷P = tt
  let-▷ᵒ∈-fro {A} {P} {a} {δ} {suc k} ▷P = ▷P
  
  let-▷ᵒ : ∀{A}{t}{P : A → Setᵒ [] []}{ϕ : Setᵒ (A ∷ []) (t ∷ [])}
     → letᵒ P (▷ᵒ ϕ) ≡ ▷ᵒ (letᵒ P ϕ)
  let-▷ᵒ {A}{t}{P}{ϕ} =
      let xx = letᵒ P (▷ᵒ ϕ) in
      let yy =  ▷ᵒ (letᵒ P ϕ) in
      {!refl!}
  {-# REWRITE let-▷ᵒ #-}

  let-∈ : ∀{A}{P : A → Setᵒ [] []}{a : A}
     → letᵒ P (a ∈ zeroᵒ) ≡ (P a)
  let-∈ {A}{P}{a} = refl
  {-# REWRITE let-∈ #-}
  
  let-pureᵒ : ∀{A}{P : A → Setᵒ [] []}{p : Set}
     → letᵒ P (p ᵒ) ≡ p ᵒ
  let-pureᵒ = refl
  {-# REWRITE let-pureᵒ #-}

  let-×ᵒ : ∀{A}{P : A → Setᵒ [] []}{ϕ ψ : Setᵒ (A ∷ []) (Later ∷ [])}
     → letᵒ P (ϕ ×ᵒ ψ) ≡ (letᵒ P ϕ) ×ᵒ (letᵒ P ψ)
  let-×ᵒ = refl
  {-# REWRITE let-×ᵒ #-}

  let-⊎ᵒ : ∀{A}{P : A → Setᵒ [] []}{ϕ ψ : Setᵒ (A ∷ []) (Later ∷ [])}
     → letᵒ P (ϕ ⊎ᵒ ψ) ≡ (letᵒ P ϕ) ⊎ᵒ (letᵒ P ψ)
  let-⊎ᵒ {A}{P}{ϕ}{ψ} = refl
  {-# REWRITE let-⊎ᵒ #-}

  let-∀ᵒ : ∀{A}{B}{P : A → Setᵒ [] []}{ϕᵇ  : B → Setᵒ (A ∷ []) (Later ∷ [])}
     → letᵒ P (∀ᵒ ϕᵇ) ≡ ∀ᵒ λ b →  (letᵒ P (ϕᵇ b))
  let-∀ᵒ {A}{B}{P}{ϕᵇ} = refl
  {-# REWRITE let-∀ᵒ #-}

  let-∃ᵒ : ∀{A}{B}{{_ : Inhabited B}}{P : A → Setᵒ [] []}{ϕᵇ  : B → Setᵒ (A ∷ []) (Later ∷ [])}
     → letᵒ P (∃ᵒ ϕᵇ) ≡ ∃ᵒ λ b →  (letᵒ P (ϕᵇ b))
  let-∃ᵒ {A}{B}{P}{ϕᵇ} = refl
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
  abstract
    infix 2 _≡ᵒ_
    _≡ᵒ_ : ∀{Γ}{Δ : Times Γ} → Setᵒ Γ Δ → Setᵒ Γ Δ → Set₁
    S ≡ᵒ T = ∀ δ → # S δ ≡ₒ # T δ

    ≡ᵒ-refl : ϕ ≡ ψ → ϕ ≡ᵒ ψ
    ≡ᵒ-refl {ϕ} refl i = {!!}

    ≡ᵒ-sym : ϕ ≡ᵒ ψ → ψ ≡ᵒ ϕ
    ≡ᵒ-sym {ϕ}{ψ} PQ ttᵖ k
        with PQ ttᵖ k
    ... | (ϕ⇒ψ , ψ⇒ϕ) = ψ⇒ϕ , ϕ⇒ψ

    ≡ᵒ-trans : ϕ ≡ᵒ ψ → ψ ≡ᵒ þ → ϕ ≡ᵒ þ
    ≡ᵒ-trans PQ QR ttᵖ k
        with PQ ttᵖ k | QR ttᵖ k
    ... | (ϕ⇒ψ , ψ⇒ϕ) | (ψ⇒þ , þ⇒ψ) = (λ z → ψ⇒þ (ϕ⇒ψ z)) , (λ z → ψ⇒ϕ (þ⇒ψ z))


fixpointᵒ : ∀{Γ}{Δ : Times Γ}{A} (F : A → Setᵒ (A ∷ Γ) (Later ∷ Δ)) (a : A)
   → μᵒ F a ≡ᵒ letᵒ (μᵒ F) (F a)
fixpointᵒ F a = {!!}

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
  ⊥-elimᵒ ⊢⊥ ϕ zero ⊨𝒫n = {!!} -- tz ϕ ttᵖ tt
  ⊥-elimᵒ ⊢⊥ ϕ (suc n) ⊨𝒫sn = ⊥-elim (⊢⊥ (suc n) ⊨𝒫sn)

  ⊥⇒⊥ᵒ : ⊥ → 𝒫 ⊢ᵒ ⊥ᵒ
  ⊥⇒⊥ᵒ ()

  ⊥ᵒ⇒⊥ : [] ⊢ᵒ ⊥ᵒ → ⊥
  ⊥ᵒ⇒⊥ ⊢⊥ = ⊢ᵒE{[]}{⊥ᵒ} ⊢⊥ 1 tt

abstract
  pureᵒI : ∀{p : Set} → p → 𝒫 ⊢ᵒ p ᵒ
  pureᵒI s zero ⊨𝒫n = tt
  pureᵒI s (suc n) ⊨𝒫n = s

  pureᵒE : 𝒫 ⊢ᵒ p ᵒ  →  (p → 𝒫 ⊢ᵒ þ)  →  𝒫 ⊢ᵒ þ
  pureᵒE {𝒫} {p} {R} ⊢p p→⊢R zero 𝒫n = {!!} -- tz R ttᵖ tt
  pureᵒE {𝒫} {p} {R} ⊢p p→⊢R (suc n) 𝒫n = p→⊢R (⊢p (suc n) 𝒫n) (suc n) 𝒫n

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
    {!!} -- (down ϕ ttᵖ tt n ϕn k k≤n) , (downClosed-Πᵏ 𝒫 n ⊨𝒫n k k≤n)

abstract
  →ᵒI : ϕ ∷ 𝒫 ⊢ᵒ ψ  →  𝒫 ⊢ᵒ ϕ →ᵒ ψ
  →ᵒI {𝒫 = 𝒫} ϕ∷𝒫⊢ψ n ⊨𝒫n j j≤n ϕj = ϕ∷𝒫⊢ψ j (ϕj , downClosed-Πᵏ 𝒫 n ⊨𝒫n j j≤n)

  →ᵒE : 𝒫 ⊢ᵒ ϕ →ᵒ ψ  →  𝒫 ⊢ᵒ ϕ  →  𝒫 ⊢ᵒ ψ
  →ᵒE {𝒫} 𝒫⊢ϕ→ψ 𝒫⊢ϕ n ⊨𝒫n = let ϕn = 𝒫⊢ϕ n ⊨𝒫n in 𝒫⊢ϕ→ψ n ⊨𝒫n n ≤-refl ϕn

abstract
  monoᵒ : 𝒫 ⊢ᵒ ϕ  →  𝒫 ⊢ᵒ  ▷ᵒ ϕ
  monoᵒ {𝒫}{ϕ} ⊢ϕ zero ⊨𝒫n = tt
  monoᵒ {𝒫}{ϕ} ⊢ϕ (suc n) ⊨𝒫n = ⊢ϕ n (downClosed-Πᵏ 𝒫 (suc n) ⊨𝒫n n (n≤1+n n))

abstract
  lobᵒ : (▷ᵒ ϕ) ∷ 𝒫 ⊢ᵒ ϕ  →  𝒫 ⊢ᵒ ϕ
  lobᵒ {ϕ}{𝒫} step zero ⊨𝒫n = {!!} -- tz ϕ ttᵖ tt
  lobᵒ {ϕ}{𝒫} step (suc n) ⊨𝒫sn =
    let ⊨𝒫n = downClosed-Πᵏ 𝒫 (suc n) ⊨𝒫sn n (n≤1+n n) in
    let ϕn = lobᵒ {ϕ}{𝒫} step n ⊨𝒫n in
    step (suc n) (ϕn , ⊨𝒫sn)

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
  ∃ᵒE {þ = þ} ⊢∃ϕᵃ cont zero ⊨𝒫n = {!!} -- tz þ ttᵖ tt
  ∃ᵒE ⊢∃ϕᵃ cont (suc n) ⊨𝒫n
      with ⊢∃ϕᵃ (suc n) ⊨𝒫n
  ... | (a , ϕᵃasn) = cont a (suc n) (ϕᵃasn , ⊨𝒫n)

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
  ▷× ▷ϕ×ψ zero = λ _ → tt , tt
  ▷× ▷ϕ×ψ (suc n) = ▷ϕ×ψ (suc n)

abstract
  ▷⊎ : 𝒫 ⊢ᵒ (▷ᵒ (ϕ ⊎ᵒ ψ))  →  𝒫 ⊢ᵒ (▷ᵒ ϕ) ⊎ᵒ (▷ᵒ ψ)
  ▷⊎ ▷ϕ⊎ψ zero = λ _ → inj₁ tt
  ▷⊎ ▷ϕ⊎ψ (suc n) = ▷ϕ⊎ψ (suc n) 

abstract
  ▷→ : 𝒫 ⊢ᵒ (▷ᵒ (ϕ →ᵒ ψ))  →  𝒫 ⊢ᵒ (▷ᵒ ϕ) →ᵒ (▷ᵒ ψ)
  ▷→ ▷ϕ→ψ zero ⊨𝒫n .zero z≤n tt = tt
  ▷→ ▷ϕ→ψ (suc n) ⊨𝒫n .zero z≤n ▷ϕj = tt
  ▷→ ▷ϕ→ψ (suc n) ⊨𝒫n (suc j) (s≤s j≤n) ϕj = ▷ϕ→ψ (suc n) ⊨𝒫n j j≤n ϕj

abstract
  ▷∀ : ∀{ϕᵃ : A → Setᵏ} → 𝒫 ⊢ᵒ ▷ᵒ (∀ᵒ[ a ] ϕᵃ a)  →  𝒫 ⊢ᵒ (∀ᵒ[ a ] ▷ᵒ (ϕᵃ a))
  ▷∀ 𝒫⊢▷∀ϕᵃ zero ⊨𝒫n a = tt
  ▷∀ 𝒫⊢▷∀ϕᵃ (suc n) ⊨𝒫sn a = 𝒫⊢▷∀ϕᵃ (suc n) ⊨𝒫sn a

abstract
  ▷∃ : ∀{ϕᵃ : A → Setᵏ}{{_ : Inhabited A}} → 𝒫 ⊢ᵒ ▷ᵒ (∃ᵒ[ a ] ϕᵃ a)  →  𝒫 ⊢ᵒ (∃ᵒ[ a ] ▷ᵒ (ϕᵃ a))
  ▷∃ 𝒫⊢▷∃ϕᵃ zero ⊨𝒫n = elt , tt
  ▷∃ 𝒫⊢▷∃ϕᵃ (suc k) ⊨𝒫n = 𝒫⊢▷∃ϕᵃ (suc k) ⊨𝒫n

abstract
  ▷pureᵒ : [] ⊢ᵒ ▷ᵒ (p ᵒ) → [] ⊢ᵒ p ᵒ
  ▷pureᵒ ⊢▷ zero ttᵖ = tt
  ▷pureᵒ ⊢▷ (suc k) ttᵖ = ⊢▷ (suc (suc k)) tt 

abstract
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

{-
module RepRewrites where
  {- These interact with the rewrites for letᵒ -}
  {-# REWRITE #μᵒ≡ #-}
  {-# REWRITE #pureᵒ≡ #-}
  {-# REWRITE #⊤ᵒ≡⊤ #-}
  {-# REWRITE #⊎ᵒ≡ #-}
  {-# REWRITE #∃ᵒ≡ #-}

-}
