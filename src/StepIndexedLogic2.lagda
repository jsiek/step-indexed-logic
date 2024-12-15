\begin{comment}
\begin{code}
{-# OPTIONS --without-K --rewriting --prop #-}

{-

  Experimenting with abstract logical connectives and a flat
  organization.

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

open import Agda.Primitive using (lzero; lsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat
   using (ℕ; zero; suc; _+_; _∸_) renaming (_<_ to _<ₙ_)
open import Data.Product
   renaming (_,_ to _,ᵃ_; ∃ to ∃ᵃ) using ()
open import Data.Unit using (tt; ⊤)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; cong-app; subst)
open import Relation.Nullary using (¬_)
open import Function using (id; _∘_)
open import Level using (Lift)

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import EquivalenceRelationProp public

open import PropP
open import StrongInduction
open import SILVariables public
open import Env public
open import RawSetO
open import Approx
open import Iteration
open import SetO public
open import Fixpoint
open import Membership
open import Later
open import RecPred
open import Conjunction
open import Disjunction
open import Implication
open import Forall
open import Exists
open import Pure
open import Let
\end{code}
\end{comment}

\begin{code}
record Setⁱ : Set₁ where
  field
    # : Setₒ
    down : downClosed #
    tz : # 0
open Setⁱ public
  
abstract

 {---------------------- Membership in Recursive Predicate --------------------}

  _∈_ : ∀{Γ}{A} → A → (x : Γ ∋ A) → Setᵒ Γ (var-now Γ x)
  a ∈ x = record { # = (λ δ → (lookup x δ) a) ; down = down-lookup ; wellformed = (wellformed-lookup x) ; congr = (congruent-lookup x a) }

  #∈≡ : ∀{Γ}{A} → (a : A) → (x : Γ ∋ A) → # (a ∈ x) ≡ λ δ → (lookup x δ) a
  #∈≡ a x = refl
  
{---------------------- Later Operator ---------------------}

  ▷ᵒ : ∀{Γ}{Δ : Times Γ}
     → Setᵒ Γ Δ
       -----------------
     → Setᵒ Γ (laters Γ)
  ▷ᵒ {Γ}{Δ} S = record { # = (λ δ → ▷ ((# S) δ)) ; down = (down-later S) ; wellformed = (wellformed-▷ S) ; congr =  (λ δ=δ′ → cong-▷ (congr S δ=δ′)) }

  #▷ᵒ≡ : ∀{Γ}{Δ}{ϕ : Setᵒ Γ Δ} → # (▷ᵒ ϕ) ≡ λ δ → ▷ (# ϕ δ)
  #▷ᵒ≡ {Γ}{Δ}{ϕ} = let x = # (▷ᵒ ϕ) in refl

  ▷sk : ∀{Γ}{Δ}{ϕ : Setᵒ Γ Δ}{δ : RecEnv Γ}{k}
     → downClosedᵈ δ
     → ▷ (# ϕ δ) (suc k) ⇔ # ϕ δ k
  ▷sk {Γ}{Δ}{ϕ}{δ}{k} down-δ =
     (λ ▷ϕsk → ▷ϕsk k (≤-reflₚ{k})) ,ₚ λ ϕk j j<sk → down ϕ δ down-δ k ϕk j (≤-predₚ{j}{k} j<sk)

{---------------------- Recursive Predicate -----------------------------------}

abstract
  μᵒ : ∀{Γ}{Δ : Times Γ}{A}
     → (A → Setᵒ (A ∷ Γ) (Later ∷ Δ))
     → (A → Setᵒ Γ Δ)
  μᵒ {Γ}{Δ}{A} Sᵃ a = record { # = (λ δ → mu Sᵃ δ a) ; down = (down-mu Sᵃ a) ; wellformed = (wellformed-mu Sᵃ a) ; congr = (congruent-mu Sᵃ a) }

  #μᵒ≡ : ∀{Γ}{Δ : Times Γ}{A} (Sᵃ : A → Setᵒ (A ∷ Γ) (Later ∷ Δ)) (a : A) → ∀ δ k
     → # (μᵒ Sᵃ a) δ k ≡ mu Sᵃ δ a k
  #μᵒ≡ Sᵃ a δ k = refl

{---------------------- Forall -----------------------------------------}

  ∀ᵒ : ∀{Γ}{Δ : Times Γ}{A : Set}
     → (A → Setᵒ Γ Δ)
     → Setᵒ Γ Δ
  ∀ᵒ{Γ}{Δ}{A} P = record { # = (λ δ → ∀ₒ[ a ⦂ A ] # (P a) δ) ;
                           down = (λ δ dc-δ n Pδn k k≤n a → down (P a) δ dc-δ n (Pδn a) k k≤n) ;
                           wellformed = (wellformed-all P) ;
                           congr = (λ δ=δ′ → cong-∀ λ a → congr (P a) δ=δ′) }

  #∀ᵒ≡ : ∀{Γ}{Δ : Times Γ}{A : Set}{Sᵃ : A → Setᵒ Γ Δ}{δ}{k}
     → (# (∀ᵒ Sᵃ) δ k) ≡ ∀ (a : A) → # (Sᵃ a) δ k
  #∀ᵒ≡ = refl
  
{---------------------- Exists -----------------------------------------}

  ∃ᵒ : ∀{Γ}{Δ : Times Γ}{A : Set}
     → (A → Setᵒ Γ Δ)
     → Setᵒ Γ Δ
  ∃ᵒ{Γ}{Δ}{A} P = record { # = (λ δ → ∃ₒ[ a ⦂ A ] # (P a) δ) ;
                           down = (λ δ dc-δ n a×Paδn k k≤n → match a×Paδn λ a Pa → a ,ₚ (down (P a) δ dc-δ n Pa k k≤n)) ;
                           wellformed = (wellformed-exists P) ;
                           congr = (λ δ=δ′ → cong-∃ λ a → congr (P a) δ=δ′) }

  #∃ᵒ≡ : ∀{Γ}{Δ : Times Γ}{A : Set}{Sᵃ : A → Setᵒ Γ Δ}{δ}{k}
     → (# (∃ᵒ Sᵃ) δ k) ≡ (Σₚ[ a ∈ A ] (# (Sᵃ a) δ k))
  #∃ᵒ≡ = refl

  cong-∃ᵒ : ∀{Γ Δ}{A}{ϕᵃ ψᵃ : A → Setᵒ Γ Δ} → (∀ a → ϕᵃ a ≡ᵒ ψᵃ a) → ∃ᵒ ϕᵃ ≡ᵒ ∃ᵒ ψᵃ 
  cong-∃ᵒ{Γ}{Δ} ϕ=ψ = ⇔⇒≡ᵒ λ δ k → cong-∃ (λ a k₁ → let ϕa=ψa = ϕ=ψ a in ≡ᵒ⇒⇔{δ = δ}{k = k} ϕa=ψa) k

{---------------------- Pure (Set) ------------------------------------}

  _ᵒ : ∀{Γ} → Set → Setᵒ Γ (laters Γ)
  p ᵒ = record { # = (λ δ → p ₒ) ; down = (λ δ dc-δ n p k k≤n → p) ; wellformed = (wellformed-pure p) ;
                 congr = (λ δ=δ′ → ≡ₒ-refl refl) }

  #pureᵒ≡ : ∀{p}{Γ}{δ : RecEnv Γ}{k} → # (p ᵒ) δ k ≡ Squash p
  #pureᵒ≡ = refl

{---------------------- Pure (Prop) -----------------------------------}

  _ᵖ : ∀{Γ} → Prop → Setᵒ Γ (laters Γ)
  p ᵖ = record { # = (λ δ → p ₚ) ; down = (λ δ dc-δ n p k k≤n → p) ; wellformed = (wellformed-pure-prop p) ;
                 congr = (λ δ=δ′ → ≡ₒ-refl refl) }

  #pureᵖ≡ : ∀{p}{Γ}{δ : RecEnv Γ}{k} → # (p ᵖ) δ (suc k) ≡ p
  #pureᵖ≡ = refl

{---------------------- Indexed Set ------------------------------------}

  wellformed-indexed : ∀{Γ}{A}{Δ : Times Γ} (S : Setⁱ) (x : Γ ∋ A)
                     → wellformed-var x (timeof x Δ) (λ δ → # S)
  wellformed-indexed {Γ}{A}{Δ} S x
      with timeof x Δ
  ... | Now = λ δ j k k≤j → ≡ₒ-refl refl
  ... | Later = λ δ j k k≤j → ≡ₒ-refl refl

  _ⁱ : ∀{Γ} → Setⁱ → Setᵒ Γ (laters Γ)
  S ⁱ = record { # = (λ δ → # S) ;
                 down = (λ δ dc-δ n Sn k k≤n → down S n Sn k k≤n) ;
                 wellformed = wellformed-indexed S ;
                 congr = (λ δ=δ′ → ≡ₒ-refl refl) }

  #indexedᵒ≡ : ∀{S}{Γ}{δ : RecEnv Γ}{k} → # (S ⁱ) δ k ≡ # S k
  #indexedᵒ≡ = refl

{---------------------- False -----------------------------------------}

  ⊥ᵒ : ∀{Γ} → Setᵒ Γ (laters Γ)
  ⊥ᵒ = ⊥ ᵒ

  #⊥ᵒ≡⊥ : ∀{Γ}{δ : RecEnv Γ}{k} → # ⊥ᵒ δ k ≡ Squash ⊥
  #⊥ᵒ≡⊥ = refl

{---------------------- True -----------------------------------------}

  ⊤ᵒ : ∀{Γ} → Setᵒ Γ (laters Γ)
  ⊤ᵒ = ⊤ ᵒ

  #⊤ᵒ≡⊤ : ∀{Γ}{δ : RecEnv Γ}{k} → # ⊤ᵒ δ k ≡ Squash ⊤
  #⊤ᵒ≡⊤ = refl

{---------------------- Conjunction -----------------------------------------}

  infixr 7 _×ᵒ_
  _×ᵒ_ : ∀{Γ}{Δ₁ Δ₂ : Times Γ}
     → Setᵒ Γ Δ₁
     → Setᵒ Γ Δ₂
       ------------------------
     → Setᵒ Γ (combine Δ₁ Δ₂)
  S ×ᵒ T = record { # = (λ δ → (# S δ) ×ₒ (# T δ)) ;
                    down = (λ δ dc-δ n Sδn×Tδn k k≤n →
                       (down S δ dc-δ n (proj₁ₚ Sδn×Tδn) k k≤n)
                       ,ₚ (down T δ dc-δ n (proj₂ₚ Sδn×Tδn) k k≤n)) ;
                    wellformed = (wellformed-conjunction S T) ;
                    congr =  (λ δ=δ′ → cong-×ₒ (congr S δ=δ′) (congr T δ=δ′)) }

  #×ᵒ≡ : ∀{Γ}{Δ₁ Δ₂ : Times Γ}{ϕ : Setᵒ Γ Δ₁}{ψ : Setᵒ Γ Δ₂}{δ}{k}
       → (# (ϕ ×ᵒ ψ) δ k) ≡ (# ϕ δ k ×ₚ # ψ δ k)
  #×ᵒ≡ {Γ}{Δ₁}{Δ₂}{ϕ}{ψ}{δ}{k} = refl

  cong-×ᵒ : ∀{Γ}{Δ}{ϕ ϕ′ ψ ψ′ : Setᵒ Γ Δ} → ϕ ≡ᵒ ϕ′ → ψ ≡ᵒ ψ′ → ϕ ×ᵒ ψ ≡ᵒ ϕ′ ×ᵒ ψ′
  cong-×ᵒ {Γ}{Δ}{ϕ}{ϕ′}{ψ}{ψ′} ϕ=ϕ′ ψ=ψ′ = ⇔⇒≡ᵒ (λ δ k → ⇔-intro to fro)
    where
    to : ∀{δ}{k} → # (ϕ ×ᵒ ψ) δ k → # (ϕ′ ×ᵒ ψ′) δ k
    to {δ}{k} (ϕk ,ₚ ψk) = (⇔-to (≡ᵒ⇒⇔ ϕ=ϕ′) ϕk) ,ₚ (⇔-to (≡ᵒ⇒⇔ ψ=ψ′) ψk)
    fro  : ∀{k}{δ} → # (ϕ′ ×ᵒ ψ′) δ k → #(ϕ ×ᵒ ψ) δ k
    fro {δ}{k} (ϕ′k ,ₚ ψ′k) = (⇔-fro (≡ᵒ⇒⇔ ϕ=ϕ′) ϕ′k) ,ₚ (⇔-fro (≡ᵒ⇒⇔ ψ=ψ′) ψ′k)


{---------------------- Disjunction -----------------------------------------}

  infixr 7 _⊎ᵒ_
  _⊎ᵒ_ : ∀{Γ}{Δ₁ Δ₂ : Times Γ}
     → Setᵒ Γ Δ₁
     → Setᵒ Γ Δ₂
       ------------------------
     → Setᵒ Γ (combine Δ₁ Δ₂)
  S ⊎ᵒ T = record { # = (λ δ → (# S δ) ⊎ₒ (# T δ)) ;
                    down = (λ {δ dc-δ n (inj₁ₚ Sn) k k≤n → inj₁ₚ (down S δ dc-δ n Sn k k≤n);
                         δ dc-δ n (inj₂ₚ Tn) k k≤n → inj₂ₚ (down T δ dc-δ n Tn k k≤n)}) ;
                    wellformed = (wellformed-disjunction S T) ;
                    congr = λ δ=δ′ → cong-⊎ₒ (congr S δ=δ′) (congr T δ=δ′) }

  #⊎ᵒ≡ : ∀{Γ}{Δ₁ Δ₂ : Times Γ}{ϕ : Setᵒ Γ Δ₁}{ψ : Setᵒ Γ Δ₂}{δ}{k}
       → (# (ϕ ⊎ᵒ ψ) δ k) ≡ (# ϕ δ k ⊎ₚ # ψ δ k)
  #⊎ᵒ≡ {Γ}{Δ₁}{Δ₂}{ϕ}{ψ}{δ}{k} = refl

  cong-⊎ᵒ : ∀{Γ}{Δ}{ϕ ϕ′ ψ ψ′ : Setᵒ Γ Δ} → ϕ ≡ᵒ ϕ′ → ψ ≡ᵒ ψ′ → ϕ ⊎ᵒ ψ ≡ᵒ ϕ′ ⊎ᵒ ψ′
  cong-⊎ᵒ {Γ}{Δ}{ϕ}{ϕ′}{ψ}{ψ′} ϕ=ϕ′ ψ=ψ′ = ⇔⇒≡ᵒ (λ δ k → ⇔-intro to fro)
    where
    to : ∀{δ}{k} → # (ϕ ⊎ᵒ ψ) δ k → # (ϕ′ ⊎ᵒ ψ′) δ k
    to (inj₁ₚ x) = inj₁ₚ (proj₁ₚ (≡ᵒ⇒⇔ ϕ=ϕ′) x)
    to (inj₂ₚ y) = inj₂ₚ (proj₁ₚ (≡ᵒ⇒⇔ ψ=ψ′) y)
    fro  : ∀{δ}{k} → #(ϕ′ ⊎ᵒ ψ′) δ k → #(ϕ ⊎ᵒ ψ) δ k
    fro (inj₁ₚ x) = inj₁ₚ (proj₂ₚ (≡ᵒ⇒⇔ ϕ=ϕ′) x)
    fro (inj₂ₚ y) = inj₂ₚ (proj₂ₚ (≡ᵒ⇒⇔ ψ=ψ′) y)

{---------------------- Implication -----------------------------------------}

  infixr 6 _→ᵒ_
  _→ᵒ_ : ∀{Γ}{Δ₁ Δ₂ : Times Γ}
     → Setᵒ Γ Δ₁
     → Setᵒ Γ Δ₂
       ------------------------
     → Setᵒ Γ (combine Δ₁ Δ₂)
  S →ᵒ T = record { # = (λ δ → (# S δ) →ₒ (# T δ)) ;
                    down = (λ δ dc-δ n ∀j<n,Sj→Tj k k≤n j j≤k Sj →
                        ∀j<n,Sj→Tj j (≤-transₚ{j}{k}{n} j≤k k≤n) Sj) ;
                    wellformed = (wellformed-implication S T) ;
                    congr = (λ δ=δ′ → cong-→ₒ (congr S δ=δ′) (congr T δ=δ′)) }
                     
  #→ᵒ≡ : ∀{Γ}{Δ₁ Δ₂ : Times Γ}{ϕ : Setᵒ Γ Δ₁}{ψ : Setᵒ Γ Δ₂}{δ}{k}
       → (# (ϕ →ᵒ ψ) δ k) ≡ (∀ j → j ≤ₚ k → # ϕ δ j → # ψ δ j)
  #→ᵒ≡ {Γ}{Δ₁}{Δ₂}{ϕ}{ψ}{δ}{k} = refl

{---------------------- Let for Predicates -----------------------------------------}

  letᵒ : ∀{A}{Γ}{t}{Δ} → (A → Setᵒ Γ Δ) → Setᵒ (A ∷ Γ) (t ∷ Δ) → Setᵒ Γ Δ   
  letᵒ Sᵃ T = record { # =  (λ δ →  # T ((λ a → # (Sᵃ a) δ) ,ᵃ δ)) ;
                      down = (λ δ dc-δ n Tn k k≤n →
                              down T ((λ a k → # (Sᵃ a) δ k) ,ᵃ δ)
                                     ((λ a → down (Sᵃ a) δ dc-δ) ,ₚ dc-δ)
                                     n Tn k k≤n) ;
                      wellformed = (wellformed-let T Sᵃ) ;
                      congr = λ δ=δ′ → congr T ((λ a → congr (Sᵃ a) δ=δ′) ,ₚ δ=δ′) }
                        
  #letᵒ≡ : ∀{A}{Γ}{Δ}{t} (P : A → Setᵒ Γ Δ) (ϕ : Setᵒ (A ∷ Γ) (t ∷ Δ)) → ∀ δ k
     → (# (letᵒ P ϕ) δ k) ≡ (# ϕ ((λ a k → # (P a) δ k) ,ᵃ δ) k)
  #letᵒ≡ {A}{Γ}{Δ}{t} P ϕ d k = refl
  
  let-▷ᵒ : ∀{A}{t}{P : A → Setᵒ [] []}{ϕ : Setᵒ (A ∷ []) (t ∷ [])}
     → letᵒ P (▷ᵒ ϕ) ≡ ▷ᵒ (letᵒ P ϕ)
  let-▷ᵒ {A} {t} {P} {ϕ} = refl
  
  let-∈ : ∀{A}{P : A → Setᵒ [] []}{a : A}
     → letᵒ P (a ∈ zeroᵒ) ≡ (P a)
  let-∈ {A}{P}{a} = refl
  
  let-pureᵒ : ∀{A : Set}{P : A → Setᵒ [] []}{p : Set}
     → letᵒ P (p ᵒ) ≡ p ᵒ
  let-pureᵒ = refl

  let-pureᵖ : ∀{A : Set}{P : A → Setᵒ [] []}{p : Prop}
     → letᵒ P (p ᵖ) ≡ p ᵖ
  let-pureᵖ = refl

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
  let-⊎ᵒ = refl

  let-→ᵒ : ∀{A}{P : A → Setᵒ [] []}{ϕ ψ : Setᵒ (A ∷ []) (Later ∷ [])}
     → letᵒ P (ϕ →ᵒ ψ) ≡ (letᵒ P ϕ) →ᵒ (letᵒ P ψ)
  let-→ᵒ = refl

  let-∀ᵒ : ∀{A}{B}{P : A → Setᵒ [] []}{ϕᵇ  : B → Setᵒ (A ∷ []) (Later ∷ [])}
     → letᵒ P (∀ᵒ ϕᵇ) ≡ ∀ᵒ λ b →  (letᵒ P (ϕᵇ b))
  let-∀ᵒ {A}{B}{P}{ϕᵇ} = refl

  let-∃ᵒ : ∀{A}{B}{P : A → Setᵒ [] []}{ϕᵇ  : B → Setᵒ (A ∷ []) (Later ∷ [])}
     → letᵒ P (∃ᵒ ϕᵇ) ≡ ∃ᵒ λ b →  (letᵒ P (ϕᵇ b))
  let-∃ᵒ {A}{B}{P}{ϕᵇ} = refl

{-# REWRITE let-⊥ᵒ #-}
{-# REWRITE let-⊤ᵒ #-}
{-# REWRITE let-▷ᵒ #-}
{-# REWRITE let-∈ #-}
{-# REWRITE let-pureᵒ #-}
{-# REWRITE let-pureᵖ #-}
{-# REWRITE let-×ᵒ #-}
{-# REWRITE let-⊎ᵒ #-}
{-# REWRITE let-→ᵒ #-}
{-# REWRITE let-∀ᵒ #-}
{-# REWRITE let-∃ᵒ #-}

{---------------------- Fixpoint Theorem --------------------------------------}

Setᵏ : Set₁
Setᵏ = Setᵒ [] []

private variable ϕ ϕ′ ψ ψ′ þ σ : Setᵏ
private variable 𝒫 : List Setᵏ
private variable p : Set
private variable A B C : Set
private variable Γ : Context
private variable Δ Δ₁ Δ₂ : Times Γ

abstract
  fixpointᵒ : ∀{Γ}{Δ : Times Γ}{A} (Sᵃ : A → Setᵒ (A ∷ Γ) (Later ∷ Δ)) (a : A)
     → (μᵒ Sᵃ) a ≡ᵒ letᵒ (μᵒ Sᵃ) (Sᵃ a)
  fixpointᵒ{Γ}{Δ}{A} Sᵃ a = ≡ₒ⇒≡ᵒ{Γ}{Δ} aux
    where
    aux : ∀ δ → # (μᵒ Sᵃ a) δ ≡ₒ # (letᵒ (μᵒ Sᵃ) (Sᵃ a)) δ
    aux δ =
        # (μᵒ Sᵃ a) δ 
      ⩦⟨ ≡ₒ-refl refl ⟩
        mu Sᵃ δ a
      ⩦⟨ equiv-approx (lemma19a Sᵃ a δ) ⟩
        # (Sᵃ a) ((λ a k → mu Sᵃ δ a k) ,ᵃ δ) 
      ⩦⟨ ≡ₒ-refl refl ⟩
        # (Sᵃ a) ((λ a k → # (μᵒ Sᵃ a) δ k) ,ᵃ δ)
      ⩦⟨ ≡ₒ-refl refl ⟩
        # (letᵒ (μᵒ Sᵃ) (Sᵃ a)) δ
      ∎

{---------------------- Proof Theory for Step Indexed Logic -------------------}

Πᵏ : List Setᵏ → Setᵏ
Πᵏ [] = ⊤ᵒ
Πᵏ (P ∷ 𝒫) = P ×ᵒ Πᵏ 𝒫 

abstract
  infix 1 _⊢ᵒ_
  _⊢ᵒ_ : List Setᵏ → Setᵏ → Prop  -- try changing to Set
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
  ttᵒ n _ = squash tt

abstract
  ⊥-elimᵒ : 𝒫 ⊢ᵒ ⊥ᵒ → (ϕ : Setᵏ) → 𝒫 ⊢ᵒ ϕ
  ⊥-elimᵒ ⊢⊥ ϕ n ⊨𝒫sn 
      with ⊢⊥ n ⊨𝒫sn
  ... | squash ()

  ⊥⇒⊥ᵒ : ⊥ → 𝒫 ⊢ᵒ ⊥ᵒ
  ⊥⇒⊥ᵒ ()

  ⊥ᵒ⇒⊥ : [] ⊢ᵒ ⊥ᵒ → ⊥ₚ{lzero}
  ⊥ᵒ⇒⊥ ⊢⊥ 
      with ⊢⊥ 0 (squash tt)
  ... | squash ()
  
abstract
  pureᵒI : ∀{p : Set} → p → 𝒫 ⊢ᵒ p ᵒ
  pureᵒI s n ⊨𝒫n = squash s

  pureᵒE : 𝒫 ⊢ᵒ p ᵒ  →  (p → 𝒫 ⊢ᵒ þ)  →  𝒫 ⊢ᵒ þ
  pureᵒE {𝒫} {p} {R} ⊢p p→⊢R n 𝒫n 
     with ⊢p n 𝒫n
  ... | squash r = p→⊢R r n 𝒫n

  pureᵒE[] : [] ⊢ᵒ p ᵒ  →  Squash p
  pureᵒE[] ⊢pᵒ = ⊢pᵒ 0 (squash tt)

  pureᵖI : ∀{p : Prop} → p → 𝒫 ⊢ᵒ p ᵖ
  pureᵖI s n ⊨𝒫n = s

  pureᵖE : ∀{p : Prop} → 𝒫 ⊢ᵒ p ᵖ  →  (p → 𝒫 ⊢ᵒ þ)  →  𝒫 ⊢ᵒ þ
  pureᵖE {𝒫} {p} {R} ⊢p p→⊢R n 𝒫n 
     with ⊢p n 𝒫n
  ... | r = p→⊢R r n 𝒫n

  pureᵖE[] : ∀{p : Prop} → [] ⊢ᵒ p ᵖ  → p
  pureᵖE[] ⊢pᵖ = ⊢pᵖ 0 (squash tt)

{-
pureᵒE-syntax = pureᵒE
infix 1 pureᵒE-syntax
syntax pureᵒE-syntax pᵒ (λ p → ⊢þ) = let-pureᵒ[ p ] pᵒ within ⊢þ
-}

abstract
  _,ᵒ_ : 𝒫 ⊢ᵒ ϕ  →  𝒫 ⊢ᵒ ψ  →  𝒫 ⊢ᵒ ϕ ×ᵒ ψ
  (𝒫⊢ϕ ,ᵒ 𝒫⊢ψ) n ⊨𝒫n = 𝒫⊢ϕ n ⊨𝒫n ,ₚ 𝒫⊢ψ n ⊨𝒫n

  proj₁ᵒ : ∀{𝒫 : List Setᵏ }{P Q : Setᵏ}
    → 𝒫 ⊢ᵒ P ×ᵒ Q
      ------------
    → 𝒫 ⊢ᵒ P
  proj₁ᵒ 𝒫⊢P×Q n ⊨𝒫n = proj₁ₚ (𝒫⊢P×Q n ⊨𝒫n)

  proj₂ᵒ : 𝒫 ⊢ᵒ ϕ ×ᵒ ψ  →  𝒫 ⊢ᵒ ψ
  proj₂ᵒ 𝒫⊢ϕ×ψ n ⊨𝒫n = proj₂ₚ (𝒫⊢ϕ×ψ n ⊨𝒫n)

abstract
  inj₁ᵒ : 𝒫 ⊢ᵒ ϕ → 𝒫 ⊢ᵒ ϕ ⊎ᵒ ψ
  inj₁ᵒ 𝒫⊢ϕ n ⊨𝒫n = inj₁ₚ (𝒫⊢ϕ n ⊨𝒫n)

  inj₂ᵒ : 𝒫 ⊢ᵒ ψ → 𝒫 ⊢ᵒ ϕ ⊎ᵒ ψ
  inj₂ᵒ 𝒫⊢ψ n ⊨𝒫n = inj₂ₚ (𝒫⊢ψ n ⊨𝒫n)

  caseᵒ : 𝒫 ⊢ᵒ ϕ ⊎ᵒ ψ  →  ϕ ∷ 𝒫 ⊢ᵒ þ  →  ψ ∷ 𝒫 ⊢ᵒ þ  →  𝒫 ⊢ᵒ þ
  caseᵒ 𝒫⊢ϕ⊎ψ ϕ∷𝒫⊢þ ψ∷𝒫⊢þ n ⊨𝒫n
      with 𝒫⊢ϕ⊎ψ n ⊨𝒫n
  ... | inj₁ₚ ϕn = ϕ∷𝒫⊢þ n (ϕn ,ₚ ⊨𝒫n)
  ... | inj₂ₚ ψn = ψ∷𝒫⊢þ n (ψn ,ₚ ⊨𝒫n)

  case3ᵒ : 𝒫 ⊢ᵒ ϕ ⊎ᵒ ψ ⊎ᵒ þ  →  ϕ ∷ 𝒫 ⊢ᵒ σ  →  ψ ∷ 𝒫 ⊢ᵒ σ  →  þ ∷ 𝒫 ⊢ᵒ σ →  𝒫 ⊢ᵒ σ
  case3ᵒ 𝒫⊢ϕ⊎ψ⊎þ ϕ∷𝒫⊢σ ψ∷𝒫⊢σ þ∷𝒫⊢σ n ⊨𝒫n
      with 𝒫⊢ϕ⊎ψ⊎þ n ⊨𝒫n
  ... | inj₁ₚ ϕn = ϕ∷𝒫⊢σ n (ϕn ,ₚ ⊨𝒫n)
  ... | inj₂ₚ (inj₁ₚ ψn) = ψ∷𝒫⊢σ n (ψn ,ₚ ⊨𝒫n)
  ... | inj₂ₚ (inj₂ₚ þn) = þ∷𝒫⊢σ n (þn ,ₚ ⊨𝒫n)

abstract
  downClosed-Πᵏ : (𝒫 : List Setᵏ) → downClosed (# (Πᵏ 𝒫) ttᵖ)
  downClosed-Πᵏ [] = λ n _ k _ → (squash tt)
  downClosed-Πᵏ (ϕ ∷ 𝒫) n (ϕn ,ₚ ⊨𝒫n) k k≤n =
    down ϕ ttᵖ ttₚ n ϕn k k≤n ,ₚ (downClosed-Πᵏ 𝒫 n ⊨𝒫n k k≤n)

abstract
  →ᵒI : ϕ ∷ 𝒫 ⊢ᵒ ψ  →  𝒫 ⊢ᵒ ϕ →ᵒ ψ
  →ᵒI {𝒫 = 𝒫} ϕ∷𝒫⊢ψ n ⊨𝒫n j j≤n ϕj = ϕ∷𝒫⊢ψ j (ϕj ,ₚ downClosed-Πᵏ 𝒫 n ⊨𝒫n j j≤n)

  →ᵒE : 𝒫 ⊢ᵒ ϕ →ᵒ ψ  →  𝒫 ⊢ᵒ ϕ  →  𝒫 ⊢ᵒ ψ
  →ᵒE {𝒫} 𝒫⊢ϕ→ψ 𝒫⊢ϕ n ⊨𝒫n = let ϕn = 𝒫⊢ϕ n ⊨𝒫n in 𝒫⊢ϕ→ψ n ⊨𝒫n n (≤-reflₚ{n}) ϕn

abstract
  monoᵒ : 𝒫 ⊢ᵒ ϕ  →  𝒫 ⊢ᵒ  ▷ᵒ ϕ
  monoᵒ {𝒫} ⊢ϕ k ⊨𝒫k j j<k =
        ⊢ϕ j (downClosed-Πᵏ 𝒫 k ⊨𝒫k j (≤-transₚ{j}{suc j}{k} (n≤1+nₚ j) j<k)) 

abstract
  lobᵒ : (▷ᵒ ϕ) ∷ 𝒫 ⊢ᵒ ϕ  →  𝒫 ⊢ᵒ ϕ
  lobᵒ {ϕ}{𝒫} step k ⊨𝒫k = aux k step ⊨𝒫k
    where
    aux : ∀ k → ▷ᵒ ϕ ∷ 𝒫 ⊢ᵒ ϕ → # (Πᵏ 𝒫) ttᵖ k → # ϕ ttᵖ k
    aux = strong-induction si
     where
      si : ∀ n → (∀ i → i <ₚ n → ▷ᵒ ϕ ∷ 𝒫 ⊢ᵒ ϕ → # (Πᵏ 𝒫) ttᵖ i → # ϕ ttᵖ i)
         →  ▷ᵒ ϕ ∷ 𝒫 ⊢ᵒ ϕ  →  # (Πᵏ 𝒫) ttᵖ n → # ϕ ttᵖ n
      si n IH step Pn =
        let ⊨𝒫n = downClosed-Πᵏ 𝒫 n Pn n (≤-reflₚ{n}) in
        step n ((λ j j<sucn → IH j j<sucn step (downClosed-Πᵏ 𝒫 n Pn j (≤-transₚ{j}{suc j}{n} (n≤1+nₚ j) j<sucn))) ,ₚ Pn)

abstract
  substᵒ : ϕ ≡ᵒ ψ  →  𝒫 ⊢ᵒ ϕ  →  𝒫 ⊢ᵒ ψ
  substᵒ ϕ=ψ 𝒫⊢ϕ n ⊨𝒫n = ⇔-to ((≡ᵒ⇒≡ₒ ϕ=ψ) n) (𝒫⊢ϕ n ⊨𝒫n)

abstract
  iffᵒ : ([] ⊢ᵒ ϕ  →ᵒ ψ) → ([] ⊢ᵒ ψ  →ᵒ ϕ) → ϕ ≡ᵒ ψ
  iffᵒ ϕ→ψ ψ→ϕ = ⇔⇒≡ᵒ λ δ k →
         (λ ϕk → ϕ→ψ k (squash tt) k (≤-reflₚ {k}) ϕk)
      ,ₚ (λ ψk → ψ→ϕ k (squash tt) k (≤-reflₚ {k}) ψk)

abstract
  Λᵒ : {ϕᵃ : A → Setᵏ} → (∀ a → 𝒫 ⊢ᵒ ϕᵃ a)  →  𝒫 ⊢ᵒ ∀ᵒ ϕᵃ
  Λᵒ ∀ϕᵃa n ⊨𝒫n a = ∀ϕᵃa a n ⊨𝒫n

Λᵒ-syntax = Λᵒ
infix 1 Λᵒ-syntax
syntax Λᵒ-syntax (λ a → ⊢ϕᵃa) = Λᵒ[ a ] ⊢ϕᵃa

abstract
  ∀ᵒE : ∀{ϕᵃ : A → Setᵏ} → 𝒫 ⊢ᵒ ∀ᵒ ϕᵃ  →  (a : A)  →  𝒫 ⊢ᵒ ϕᵃ a
  ∀ᵒE ⊢∀ϕᵃ a n ⊨𝒫n = ⊢∀ϕᵃ n ⊨𝒫n a

  ∃ᵒI : ∀{ϕᵃ : A → Setᵏ} → (a : A)  →  𝒫 ⊢ᵒ ϕᵃ a  →  𝒫 ⊢ᵒ ∃ᵒ ϕᵃ
  ∃ᵒI a ⊢ϕᵃa n ⊨𝒫n = a ,ₚ (⊢ϕᵃa n ⊨𝒫n)

  ∃ᵒE : ∀{ϕᵃ : A → Setᵏ}{þ : Setᵏ}
     → 𝒫 ⊢ᵒ ∃ᵒ ϕᵃ  →  (∀ a → ϕᵃ a ∷ 𝒫 ⊢ᵒ þ)  →  𝒫 ⊢ᵒ þ
  ∃ᵒE ⊢∃ϕᵃ cont n ⊨𝒫n
      with ⊢∃ϕᵃ n ⊨𝒫n
  ... | (a ,ₚ ϕᵃasn) = cont a n (ϕᵃasn ,ₚ ⊨𝒫n)

abstract
  Zᵒ : ϕ ∷ 𝒫 ⊢ᵒ ϕ
  Zᵒ n (ϕn ,ₚ ⊨𝒫n) = ϕn

abstract
  Sᵒ : 𝒫 ⊢ᵒ ψ  →  ϕ ∷ 𝒫 ⊢ᵒ ψ
  Sᵒ 𝒫⊢ψ n (ϕn ,ₚ ⊨𝒫n) = 𝒫⊢ψ n ⊨𝒫n


λᵒ : ∀ ϕ → (ϕ ∷ 𝒫 ⊢ᵒ ϕ → ϕ ∷ 𝒫 ⊢ᵒ ψ) → 𝒫 ⊢ᵒ ϕ →ᵒ ψ
λᵒ ϕ f = →ᵒI{ϕ = ϕ} (f Zᵒ)

λᵒ-syntax : ∀ ϕ → (ϕ ∷ 𝒫 ⊢ᵒ ϕ → ϕ ∷ 𝒫 ⊢ᵒ ψ) → 𝒫 ⊢ᵒ ϕ →ᵒ ψ
λᵒ-syntax = λᵒ
infix 1 λᵒ-syntax
syntax λᵒ-syntax ϕ (λ ⊢ϕ → ⊢ψ) = λᵒ[ ⊢ϕ ⦂ ϕ ] ⊢ψ

unpackᵒ : ∀{ϕᵃ : A → Setᵏ}{þ : Setᵏ}
     → 𝒫 ⊢ᵒ ∃ᵒ ϕᵃ  →  (∀ a → ϕᵃ a ∷ 𝒫 ⊢ᵒ ϕᵃ a → ϕᵃ a ∷ 𝒫 ⊢ᵒ þ)  →  𝒫 ⊢ᵒ þ
unpackᵒ ∃ϕ cont = ∃ᵒE ∃ϕ λ a → cont a Zᵒ

foldᵒ : ∀{𝒫} (Sᵃ : A → Setᵒ (A ∷ []) (Later ∷ [])) (a : A) →  𝒫 ⊢ᵒ letᵒ (μᵒ Sᵃ) (Sᵃ a)  →  𝒫 ⊢ᵒ μᵒ Sᵃ a
foldᵒ Sᵃ a Sᵃ[μSᵃ] = substᵒ (≡ᵒ-sym (fixpointᵒ Sᵃ a)) Sᵃ[μSᵃ]

unfoldᵒ : ∀{𝒫} (Sᵃ : A → Setᵒ (A ∷ []) (Later ∷ [])) (a : A) →  𝒫 ⊢ᵒ μᵒ Sᵃ a  →  𝒫 ⊢ᵒ letᵒ (μᵒ Sᵃ) (Sᵃ a)
unfoldᵒ Sᵃ a μSᵃ = substᵒ (fixpointᵒ Sᵃ a) μSᵃ

abstract
  ▷× : 𝒫 ⊢ᵒ (▷ᵒ (ϕ ×ᵒ ψ))  →  𝒫 ⊢ᵒ (▷ᵒ ϕ) ×ᵒ (▷ᵒ ψ)
  ▷× ▷ϕ×ψ n 𝒫n = (λ j j<n → proj₁ₚ (▷ϕ×ψ n 𝒫n j j<n))
                ,ₚ (λ j j<n → proj₂ₚ (▷ϕ×ψ n 𝒫n j j<n))

  
  ▷⊎ : 𝒫 ⊢ᵒ (▷ᵒ (ϕ ⊎ᵒ ψ))  →  𝒫 ⊢ᵒ (▷ᵒ ϕ) ⊎ᵒ (▷ᵒ ψ)
  ▷⊎ ▷ϕ⊎ψ zero 𝒫n = inj₁ₚ λ j ()
  ▷⊎ {𝒫}{ϕ}{ψ} ▷ϕ⊎ψ (suc n) 𝒫n 
      with ▷ϕ⊎ψ (suc n) 𝒫n n (≤-reflₚ{n})
  ... | inj₁ₚ ϕn = inj₁ₚ λ { j j≤n → down ϕ ttᵖ ttₚ n ϕn j j≤n }
  ... | inj₂ₚ ψn = inj₂ₚ λ { j j≤n → down ψ ttᵖ ttₚ n ψn j j≤n }


  ▷→ : 𝒫 ⊢ᵒ (▷ᵒ (ϕ →ᵒ ψ))  →  𝒫 ⊢ᵒ (▷ᵒ ϕ) →ᵒ (▷ᵒ ψ)
  ▷→ ▷ϕ→ψ n ⊨𝒫n i i≤n ▷ϕi j j<si = 
     let ϕj→ψj = ▷ϕ→ψ n ⊨𝒫n j (≤-transₚ{suc j}{i}{n} j<si i≤n) j (≤-reflₚ{j}) in
     ϕj→ψj (▷ϕi j j<si)

  →▷ : 𝒫 ⊢ᵒ (▷ᵒ ϕ) →ᵒ (▷ᵒ ψ) → 𝒫 ⊢ᵒ (▷ᵒ (ϕ →ᵒ ψ))
  →▷ {𝒫}{ϕ}{ψ} ▷ϕ→▷ψ n 𝒫n j j<n i i≤j ϕi =
    let ▷ψsi = ▷ϕ→▷ψ n 𝒫n (suc i) (≤-transₚ{suc i}{suc j}{n} i≤j j<n)
                λ j j<si → down ϕ ttᵖ ttₚ i ϕi j j<si in
    down (▷ᵒ ψ) ttᵖ ttₚ (suc i) ▷ψsi (suc i) (≤-reflₚ{i}) i (≤-reflₚ{suc i})

  ▷∀ : ∀{ϕᵃ : A → Setᵏ} → 𝒫 ⊢ᵒ ▷ᵒ (∀ᵒ ϕᵃ)  →  𝒫 ⊢ᵒ (∀ᵒ λ a → ▷ᵒ (ϕᵃ a))
  ▷∀ 𝒫⊢▷∀ϕᵃ n ⊨𝒫sn a j j< = 𝒫⊢▷∀ϕᵃ n ⊨𝒫sn j j< a

record Inhabited (A : Set) : Set where
  field
    elt : A
open Inhabited {{...}} public

instance
  ℕ-Inhabited : Inhabited ℕ
  ℕ-Inhabited = record { elt = zero }

abstract
  ▷∃ : ∀{ϕᵃ : A → Setᵏ}{{_ : Inhabited A}} → 𝒫 ⊢ᵒ ▷ᵒ (∃ᵒ ϕᵃ)  →  𝒫 ⊢ᵒ (∃ᵒ λ a → ▷ᵒ (ϕᵃ a))
  ▷∃ 𝒫⊢▷∃ϕᵃ zero ⊨𝒫k = elt ,ₚ (λ j ())
  ▷∃ {ϕᵃ = ϕᵃ} 𝒫⊢▷∃ϕᵃ (suc k) ⊨𝒫sk 
      with 𝒫⊢▷∃ϕᵃ (suc k) ⊨𝒫sk k (≤-reflₚ{k})
  ... | a ,ₚ ϕk =
        a ,ₚ λ {j j≤k →
             let ϕj = down (ϕᵃ a) ttᵖ ttₚ k ϕk j j≤k in
             down (ϕᵃ a) ttᵖ ttₚ j ϕj j (≤-reflₚ{j})}

  ▷pureᵒ : [] ⊢ᵒ ▷ᵒ (p ᵒ) → [] ⊢ᵒ p ᵒ
  ▷pureᵒ ⊢▷ k ttᵖ = ⊢▷ (suc k) (squash tt) k (s≤sₚ{k} (≤-reflₚ{k})) 

▷→▷ : 𝒫 ⊢ᵒ ▷ᵒ ϕ  →  ϕ ∷ 𝒫 ⊢ᵒ ψ  →  𝒫 ⊢ᵒ ▷ᵒ ψ
▷→▷ ▷P P⊢Q = →ᵒE (▷→ (monoᵒ (→ᵒI P⊢Q))) ▷P

∀ᵒ-syntax : ∀{Γ}{Δ : Times Γ}{A : Set} → (A → Setᵒ Γ Δ) → Setᵒ Γ Δ
∀ᵒ-syntax = ∀ᵒ
infix 1 ∀ᵒ-syntax
syntax ∀ᵒ-syntax (λ x → P) = ∀ᵒ[ x ] P

∀ᵒ-annot-syntax : ∀{Γ}{Δ : Times Γ} → ∀ (A : Set) → (A → Setᵒ Γ Δ) → Setᵒ Γ Δ
∀ᵒ-annot-syntax A = ∀ᵒ {A = A}
infix 2 ∀ᵒ-annot-syntax
syntax ∀ᵒ-annot-syntax A (λ x → P) = ∀ᵒ[ x ⦂ A ] P

∃ᵒ-syntax : ∀{Γ}{Δ : Times Γ}{A : Set} → (A → Setᵒ Γ Δ) → Setᵒ Γ Δ
∃ᵒ-syntax = ∃ᵒ
infix 2 ∃ᵒ-syntax
syntax ∃ᵒ-syntax (λ x → P) = ∃ᵒ[ x ] P

{---------------------- Eventually Operator ---------------------}

◇ᵒ : ∀{Γ}{Δ : Times Γ}
   → ℕ
   → Setᵒ Γ Δ
     -----------------
   → Setᵒ Γ (laters Γ)
◇ᵒ {Γ} {Δ} zero ϕ = ▷ᵒ ϕ
◇ᵒ {Γ} {Δ} (suc i) ϕ = ◇ᵒ i (▷ᵒ ϕ)

▷◇≡◇▷ : ∀{ϕ : Setᵏ} i → ▷ᵒ (◇ᵒ i ϕ) ≡ᵒ ◇ᵒ i (▷ᵒ ϕ)
▷◇≡◇▷ {ϕ} zero = ≡ᵒ-refl refl
▷◇≡◇▷ {ϕ} (suc i) = ▷◇≡◇▷{▷ᵒ ϕ} i 

abstract
  ▷⇒◇ :  𝒫 ⊢ᵒ ▷ᵒ ϕ  →  𝒫 ⊢ᵒ ◇ᵒ 0 ϕ
  ▷⇒◇ ▷ϕ n 𝒫n = ▷ϕ n 𝒫n
  
▷◇⇒◇ : ∀ i → 𝒫 ⊢ᵒ ▷ᵒ (◇ᵒ i ϕ) → 𝒫 ⊢ᵒ ◇ᵒ (suc i) ϕ
▷◇⇒◇ zero ▷◇ϕ = ▷◇ϕ
▷◇⇒◇ {𝒫} (suc i) ▷◇ϕ = ▷◇⇒◇ {𝒫} i ▷◇ϕ

▷◇⇒◇▷ : ∀ i → 𝒫 ⊢ᵒ ▷ᵒ (◇ᵒ i ϕ) → 𝒫 ⊢ᵒ ◇ᵒ i (▷ᵒ ϕ)
▷◇⇒◇▷ {𝒫} i ▷◇ϕ = ▷◇⇒◇{𝒫} i ▷◇ϕ

◇▷⇒▷◇ : ∀ i → 𝒫 ⊢ᵒ ◇ᵒ i (▷ᵒ ϕ) → 𝒫 ⊢ᵒ ▷ᵒ (◇ᵒ i ϕ)
◇▷⇒▷◇ {𝒫} zero ▷▷ϕ = ▷▷ϕ
◇▷⇒▷◇ {𝒫} (suc i) ◇▷ϕ = ◇▷⇒▷◇ i ◇▷ϕ

mono◇ : ∀{k} → 𝒫 ⊢ᵒ ϕ  →  𝒫 ⊢ᵒ ◇ᵒ k ϕ
mono◇ {k = zero} ϕ = monoᵒ ϕ
mono◇ {k = suc k} ϕ =
  let ◇kϕ = mono◇ {k = k} ϕ in
  let ▷◇kϕ = monoᵒ ◇kϕ in
  ▷◇⇒◇ k ▷◇kϕ

ϕ→ψ⇒◇ϕ→◇ψ : ∀{k} → 𝒫 ⊢ᵒ ϕ →ᵒ ψ → 𝒫 ⊢ᵒ (◇ᵒ k ϕ) →ᵒ (◇ᵒ k ψ)
ϕ→ψ⇒◇ϕ→◇ψ {k = zero} ϕ→ψ = ▷→ (monoᵒ ϕ→ψ)
ϕ→ψ⇒◇ϕ→◇ψ {k = suc k} ϕ→ψ =
  let ◇kϕ→◇kψ = ϕ→ψ⇒◇ϕ→◇ψ {k = k} ϕ→ψ in
  let ▷◇kϕ→▷◇kψ = ▷→ (monoᵒ ◇kϕ→◇kψ) in
  →ᵒI (▷◇⇒◇▷ k (→ᵒE (Sᵒ ▷◇kϕ→▷◇kψ) (◇▷⇒▷◇ k Zᵒ)))

◇→◇ : ∀{𝒫}{P Q : Setᵏ} (k : ℕ)
   → 𝒫 ⊢ᵒ ◇ᵒ k P
   → P ∷ 𝒫 ⊢ᵒ Q
     ------------
   → 𝒫 ⊢ᵒ ◇ᵒ k Q
◇→◇ {𝒫} {P} {Q} k ◇P P⊢Q =
  let ◇P→◇Q = ϕ→ψ⇒◇ϕ→◇ψ {k = k} (→ᵒI P⊢Q) in
  →ᵒE ◇P→◇Q ◇P

{-
abstract
  ⊢∃ᵒE : ∀{ϕᵃ : A → Setᵏ} → [] ⊢ᵒ ∃ᵒ[ a ] ϕᵃ a → Σ[ a ∈ A ] ([] ⊢ᵒ ϕᵃ a)
  ⊢∃ᵒE {ϕᵃ = ϕᵃ} ⊢∃a,ϕᵃ =
     let xx = ⊢ᵒE{[]}{∃ᵒ[ a ] ϕᵃ a} ⊢∃a,ϕᵃ 0 (squash tt) in
     match xx λ a ϕa →
     a , (⊢ᵒI{[]}{ϕᵃ a} (λ n _ →
       (match (⊢ᵒE{[]}{∃ᵒ[ a ] ϕᵃ a} ⊢∃a,ϕᵃ n (squash tt)) λ b c →
       {!!})))
-}

_⊂_ : List Setᵏ → List Setᵏ → Prop
𝒫 ⊂ [] = ⊤ₚ
𝒫 ⊂ (ϕ ∷ 𝒫′) = (𝒫 ⊢ᵒ ϕ) ×ₚ (𝒫 ⊂ 𝒫′)

abstract

  ⊂E : ∀{𝒫 𝒫′ : List Setᵏ}{n}
     → 𝒫′ ⊂ 𝒫
     → # (Πᵏ 𝒫′) ttᵖ n
     → # (Πᵏ 𝒫) ttᵖ n
  ⊂E {[]} {𝒫′} {n} 𝒫′⊂𝒫 𝒫′n = squash tt
  ⊂E {ϕ ∷ 𝒫} {𝒫′} {n} (⊢ϕ ,ₚ 𝒫′⊂𝒫) 𝒫′n = ⊢ϕ n 𝒫′n ,ₚ (⊂E 𝒫′⊂𝒫 𝒫′n)

  weaken : ∀{𝒫 𝒫′ : List Setᵏ}{ϕ}
     → 𝒫 ⊢ᵒ ϕ
     → 𝒫′ ⊂ 𝒫
     → 𝒫′ ⊢ᵒ ϕ
  weaken {𝒫}{𝒫′}{ϕ} ⊢ϕ 𝒫′⊂𝒫 n 𝒫′n = ⊢ϕ n (⊂E 𝒫′⊂𝒫 𝒫′n)

drop : ∀{𝒫 𝒫′ : List Setᵏ}{ϕ}
   → 𝒫 ⊂ 𝒫′
   → (ϕ ∷ 𝒫) ⊂ 𝒫′
drop {𝒫} {[]} {ϕ} 𝒫⊂𝒫′ = ttₚ
drop {𝒫} {ψ ∷ 𝒫′} {ϕ} (𝒫⊢ψ ,ₚ 𝒫⊂𝒫′) = Sᵒ{𝒫}{ψ}{ϕ} 𝒫⊢ψ ,ₚ drop 𝒫⊂𝒫′

⊂-refl : ∀{𝒫} → 𝒫 ⊂ 𝒫
⊂-refl {[]} = ttₚ
⊂-refl {P ∷ 𝒫} = Zᵒ ,ₚ drop ⊂-refl

abstract
  ▷ϕ⇒ϕ : [] ⊢ᵒ ▷ᵒ ϕ → [] ⊢ᵒ ϕ
  ▷ϕ⇒ϕ ▷ϕ n (squash tt) = ▷ϕ (suc n) (squash tt) n (≤-reflₚ{n})

◇ϕ⇒ϕ : ∀ k → [] ⊢ᵒ ◇ᵒ k ϕ → [] ⊢ᵒ ϕ
◇ϕ⇒ϕ zero ▷ϕ = ▷ϕ⇒ϕ ▷ϕ
◇ϕ⇒ϕ (suc k) ◇k▷ϕ =
  let ◇kϕ = ▷ϕ⇒ϕ (◇▷⇒▷◇ k ◇k▷ϕ) in
  ◇ϕ⇒ϕ k ◇kϕ
\end{code}
