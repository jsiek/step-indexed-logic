{-# OPTIONS --without-K --rewriting --prop --allow-unsolved-metas #-}

module Proofs where

open import Agda.Primitive using (lzero; lsuc)
open import Data.List using (List; []; _∷_)
open import Data.Nat
   using (ℕ; zero; suc; _+_; _∸_)
open import Data.Product
   renaming (_,_ to _,ᵃ_) using ()
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; cong-app; subst)
open import Relation.Nullary using (¬_)
open import Function using (id; _∘_)
open import Level using (Lift)

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import EquivalenceRelation public

open import PropLib
open import StrongInduction
open import Variables public
open import RawSetO
open import Approx
open import Iteration
open import SetO public
open import Fixpoint
open import Membership
open import Later
open import RecPred
open import StepIndexedLogic2

private variable ϕ ϕ′ ψ ψ′ þ : Setᵏ
private variable 𝒫 : List Setᵏ
private variable p : Prop
private variable A B C : Set
private variable Γ : Context
private variable Δ Δ₁ Δ₂ : Times Γ

{---------------------- Proof Theory for Step Indexed Logic -------------------}

Πᵏ : List Setᵏ → Setᵏ
Πᵏ [] = ⊤ᵒ
Πᵏ (P ∷ 𝒫) = P ×ᵒ Πᵏ 𝒫 

abstract
  infix 1 _⊢ᵒ_
  _⊢ᵒ_ : List Setᵏ → Setᵏ → Prop
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
  ttᵒ = ⊢ᵒI λ n _ → tt

abstract
  ⊥-elimᵒ : 𝒫 ⊢ᵒ ⊥ᵒ → (ϕ : Setᵏ) → 𝒫 ⊢ᵒ ϕ
  ⊥-elimᵒ ⊢⊥ ϕ n ⊨𝒫sn = ⊥-elim (⊢⊥ n ⊨𝒫sn)

  ⊥⇒⊥ᵒ : ⊥{lzero} → 𝒫 ⊢ᵒ ⊥ᵒ
  ⊥⇒⊥ᵒ ()

  ⊥ᵒ⇒⊥ : [] ⊢ᵒ ⊥ᵒ → ⊥{lzero}
  ⊥ᵒ⇒⊥ ⊢⊥ = ⊢ᵒE{[]}{⊥ᵒ} ⊢⊥ 1 tt

abstract
  pureᵒI : ∀{p : Prop} → p → 𝒫 ⊢ᵒ p ᵒ
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
  →ᵒE {𝒫} 𝒫⊢ϕ→ψ 𝒫⊢ϕ n ⊨𝒫n = let ϕn = 𝒫⊢ϕ n ⊨𝒫n in 𝒫⊢ϕ→ψ n ⊨𝒫n n (≤-refl{n}) ϕn

abstract
  monoᵒ : 𝒫 ⊢ᵒ ϕ  →  𝒫 ⊢ᵒ  ▷ᵒ ϕ
  monoᵒ {𝒫} ⊢ϕ k ⊨𝒫k j j<k =
        ⊢ϕ j (downClosed-Πᵏ 𝒫 k ⊨𝒫k j (≤-trans{j}{suc j}{k} (n≤1+n j) j<k)) 

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
        let ⊨𝒫n = downClosed-Πᵏ 𝒫 n Pn n (≤-refl{n}) in
        step n ((λ j j<sucn → IH j j<sucn step (downClosed-Πᵏ 𝒫 n Pn j (≤-trans{j}{suc j}{n} (n≤1+n j) j<sucn))) , Pn)

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

λᵒ-syntax : ∀ ϕ → (ϕ ∷ 𝒫 ⊢ᵒ ϕ → ϕ ∷ 𝒫 ⊢ᵒ ψ) → 𝒫 ⊢ᵒ ϕ →ᵒ ψ
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
      with ▷ϕ⊎ψ (suc n) 𝒫n n (≤-refl{n})
  ... | inj₁ ϕn = inj₁ λ { j j≤n → down ϕ ttᵖ tt n ϕn j j≤n }
  ... | inj₂ ψn = inj₂ λ { j j≤n → down ψ ttᵖ tt n ψn j j≤n }

  
  ▷→ : 𝒫 ⊢ᵒ (▷ᵒ (ϕ →ᵒ ψ))  →  𝒫 ⊢ᵒ (▷ᵒ ϕ) →ᵒ (▷ᵒ ψ)
  ▷→ ▷ϕ→ψ n ⊨𝒫n i i≤n ▷ϕi j j<si = 
     let ϕj→ψj = ▷ϕ→ψ n ⊨𝒫n j (≤-trans{suc j}{i}{n} j<si i≤n) j (≤-refl{j}) in
     ϕj→ψj (▷ϕi j j<si)

  ▷∀ : ∀{ϕᵃ : A → Setᵏ} → 𝒫 ⊢ᵒ ▷ᵒ (∀ᵒ ϕᵃ)  →  𝒫 ⊢ᵒ (∀ᵒ λ a → ▷ᵒ (ϕᵃ a))
  ▷∀ 𝒫⊢▷∀ϕᵃ n ⊨𝒫sn a j j< = 𝒫⊢▷∀ϕᵃ n ⊨𝒫sn j j< a

  ▷∃ : ∀{ϕᵃ : A → Setᵏ}{{_ : Inhabited A}} → 𝒫 ⊢ᵒ ▷ᵒ (∃ᵒ ϕᵃ)  →  𝒫 ⊢ᵒ (∃ᵒ λ a → ▷ᵒ (ϕᵃ a))
  ▷∃ 𝒫⊢▷∃ϕᵃ zero ⊨𝒫k = elt , (λ j ())
  ▷∃ {ϕᵃ = ϕᵃ} 𝒫⊢▷∃ϕᵃ (suc k) ⊨𝒫sk 
      with 𝒫⊢▷∃ϕᵃ (suc k) ⊨𝒫sk k (≤-refl{k})
  ... | a , ϕk =
      a , λ {j j≤k →
             let ϕj = down (ϕᵃ a) ttᵖ tt k ϕk j j≤k in
             down (ϕᵃ a) ttᵖ tt j ϕj j (≤-refl{j})}

  ▷pureᵒ : [] ⊢ᵒ ▷ᵒ (p ᵒ) → [] ⊢ᵒ p ᵒ
  ▷pureᵒ ⊢▷ k ttᵖ = ⊢▷ (suc k) tt k (s≤s{k} (≤-refl{k})) 

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

abstract
  ◇◇⇒◇ :  𝒫 ⊢ᵒ ◇ᵒ (◇ᵒ ϕ)  →  𝒫 ⊢ᵒ ◇ᵒ ϕ
  ◇◇⇒◇ ◇◇ϕ n 𝒫n
      with ◇◇ϕ n 𝒫n
  ... | j , sj≤n , k , sk≤j , ϕk = k , (≤-trans{suc k}{j}{n} sk≤j (≤-trans{j}{suc j}{n} (n≤1+n j) sj≤n)  , ϕk)

{-
  ▷◇⇒◇ :  𝒫 ⊢ᵒ ▷ᵒ (◇ᵒ ϕ)  →  𝒫 ⊢ᵒ ◇ᵒ ϕ
  ▷◇⇒◇ ▷◇ϕ zero 𝒫z =
      let xx = ▷◇ϕ {!!} {!!}
      in {!!}
  ▷◇⇒◇ ▷◇ϕ (suc n) 𝒫sn = {!!} , ({!!} , {!!})
-}

{-  
    let xx = ▷▷ϕ n 𝒫n {!!} {!!} j {!!} in
    xx


      {!!} , {!!} , {!!}
-}

