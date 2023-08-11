\begin{comment}
\begin{code}
{-# OPTIONS --rewriting --prop #-}

module July2023.LogRel2 where

open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Nat.Induction
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List using (map)
open import Data.Nat.Properties

open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import PropLib using (⊥-elimₛ) renaming (_⊎_ to _⊎ₚ_; ⊥-elim to ⊥-elimₚ; Σ to Σₚ; ¬_ to ¬ₚ_)

{-
open import Data.Product using () renaming (_×_ to _×ₐ_; _,_ to _,ₐ_; Σ to Σₐ)
open import Data.Sum using () renaming (_⊎_ to _⊎ₐ_; inj₁ to inj₁ₐ; inj₂ to inj₂ₐ)
open import PropLib
-}

open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Induction using (RecStruct)
--open import Induction.WellFounded as WF
--open import Data.Product.Relation.Binary.Lex.Strict using (×-Lex; ×-wellFounded; ×-preorder)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; cong₂; subst; trans)
open import Sig
open import Var
open import StepIndexedLogic2
open import July2023.STLC2
open import EquivalenceRelationProp public

\end{code}
\end{comment}



\subsection{Definition of the Logical Relation}
\label{sec:log-rel}

The logical relation is comprised of two mutually recursive
predicates, 𝒱 for values and ℰ for terms. The intuitive meaning
of the predicates is that, for a given type $A$, 
$𝒱⟦ A ⟧\, V$ means that value $V$ is well behaved according to type $A$
and $ℰ⟦ A ⟧\, M$ means that $M$ is well behaved according to type $A$.

As we discussed in Section~\ref{sec:mutually-recursive}, SIL does not
directly support mutual recursion but we can merge the two predicates
into one predicate using a sum type, which here we name 𝒱⊎ℰ.  We
define 𝒱⊎ℰ by an application of μᵒ, so we first need to define the
non-recursive version of 𝒱⊎ℰ, which we call \textsf{pre}-𝒱⊎ℰ, defined
below. It simply dispatches to the non-recursive \textsf{pre}-𝒱 and
\textsf{pre}-ℰ functions which we get to shortly.

\begin{code}
Γ₁ : Context
Γ₁ = ((Type × Term) ⊎ (Type × Term)) ∷ []

pre-ℰ : Type → Term → Setᵒ Γ₁ (Later ∷ [])
pre-𝒱 : Type → Term → Setᵒ Γ₁ (Later ∷ [])

pre-𝒱⊎ℰ : ((Type × Term) ⊎ (Type × Term)) → Setᵒ Γ₁ (Later ∷ [])
pre-𝒱⊎ℰ (inj₁ (A , V)) = pre-𝒱 A V
pre-𝒱⊎ℰ (inj₂ (A , M)) = pre-ℰ A M

𝒱⊎ℰ : ((Type × Term) ⊎ (Type × Term)) → Setᵒ [] []
𝒱⊎ℰ X = μᵒ pre-𝒱⊎ℰ X

𝒱⟦_⟧ : Type → Term → Setᵒ [] []
𝒱⟦ A ⟧ V = 𝒱⊎ℰ (inj₁ (A , V))

ℰ⟦_⟧ : Type → Term → Setᵒ [] []
ℰ⟦ A ⟧ M = 𝒱⊎ℰ (inj₂ (A , M))
\end{code}

When we use 𝒱 and ℰ recursively inside their own definitions, we do so
by using the membership operator of SIL with \textsf{recᵒ} (for ``this
recursive predicate''), and either \textsf{inj₁} for 𝒱 and
\textsf{inj₂} for ℰ. So we define the following shorthand notation for
these recursive references to 𝒱 and ℰ.

\begin{code}
𝒱ᵒ⟦_⟧ : Type → Term → Setᵒ Γ₁ (Now ∷ [])
𝒱ᵒ⟦ A ⟧ V = inj₁ (A , V) ∈ recᵒ

ℰᵒ⟦_⟧ : Type → Term → Setᵒ Γ₁ (Now ∷ [])
ℰᵒ⟦ A ⟧ M = inj₂ (A , M) ∈ recᵒ
\end{code}

The definition of \textsf{pre-ℰ}, i.e., what it means for a term to be
well behaved, is essentially a statement of what we'd like to prove:
``progress'' and ``preservation''. In particular, the progress part
says that either $M$ is a well-behaved value or it is reducible. The
preservation part says that if $M$ reduces to $N$, then $N$ is also
well behaved. Note that we insert the ▷ᵒ operator in front of the
recursive use of ℰ to satisfy SIL's rules for well formed recursive
definitions.

\begin{code}
pre-ℰ A M = (pre-𝒱 A M ⊎ᵒ (reducible M)ᵒ) ×ᵒ (∀ᵒ[ N ] (M —→ N)ᵒ →ᵒ ▷ᵒ (ℰᵒ⟦ A ⟧ N))
\end{code}

The definition of \textsf{pre-𝒱} defines what it means to be a
well-behaved value according to a given type. For type ℕ, the value
must be the literal for zero or be the successor of a well-behaved
value at type ℕ. For function types, the value must be either a lambda
abstraction or fixpoint. For a lambda abstraction, given an arbitrary
well-behaved values $W$, substituting it into the lambda's body $N$
produces a well-behaved term.  For a fixpoint $μ\,V$, the term $V$
must be a value (syntactically) and substituting the whole fixpoint
into $V$ produces a well-behaved value. We insert the ▷ᵒ operator
around each recursive use of 𝒱 and ℰ.

\begin{minipage}{\textwidth}
\begin{code}
pre-𝒱 `ℕ `zero       = ⊤ᵒ
pre-𝒱 `ℕ (`suc V)    = pre-𝒱 `ℕ V
pre-𝒱 (A ⇒ B) (ƛ N)  = ∀ᵒ[ W ] ▷ᵒ (𝒱ᵒ⟦ A ⟧ W) →ᵒ ▷ᵒ (ℰᵒ⟦ B ⟧ (N [ W ]))
pre-𝒱 (A ⇒ B) (μ V)  = (Value V)ᵒ ×ᵒ (▷ᵒ (𝒱ᵒ⟦ A ⇒ B ⟧ (V [ μ V ])))
pre-𝒱 A M            = ⊥ᵒ
\end{code}
\end{minipage}

Next we prove several lemmas that encapsulate uses of the fixpoint
theorem.  We define the following shorthand for referring to the two
parts of the ℰ predicate.

\begin{code}
progress : Type → Term → Setᵒ [] []
progress A M = 𝒱⟦ A ⟧ M ⊎ᵒ (reducible M)ᵒ

preservation : Type → Term → Setᵒ [] []
preservation A M = ∀ᵒ[ N ] ((M —→ N)ᵒ →ᵒ ▷ᵒ (ℰ⟦ A ⟧ N))
\end{code}

\noindent The first lemma states that $ℰ⟦ A ⟧ M$ is equivalent to the
conjunction of progress and preservation. The proof uses the fixpoint
theorem twice, once to unfold the definintion of ℰ and then again
to fold the definition of 𝒱.

\begin{code}
ℰ-stmt : ∀{A}{M} → ℰ⟦ A ⟧ M ≡ᵒ progress A M ×ᵒ preservation A M
ℰ-stmt {A}{M} =
  ℰ⟦ A ⟧ M                                 ⩦⟨ ≡ᵒ-refl refl ⟩
  μᵒ pre-𝒱⊎ℰ (inj₂ (A , M))                ⩦⟨ fixpointᵒ pre-𝒱⊎ℰ (inj₂ (A , M)) ⟩
  letᵒ (μᵒ pre-𝒱⊎ℰ) (pre-𝒱⊎ℰ (inj₂ (A , M))) 
      ⩦⟨ cong-×ᵒ (cong-⊎ᵒ (≡ᵒ-sym (fixpointᵒ pre-𝒱⊎ℰ (inj₁ (A , M)))) (≡ᵒ-refl refl)) (≡ᵒ-refl refl) ⟩
  progress A M ×ᵒ preservation A M           ∎
\end{code}

\noindent The following introduction rule for ℰ is a directly
corollary of the above.

\begin{code}
ℰ-intro : ∀ {𝒫}{A}{M} → 𝒫 ⊢ᵒ progress A M → 𝒫 ⊢ᵒ preservation A M → 𝒫 ⊢ᵒ ℰ⟦ A ⟧ M
ℰ-intro 𝒫⊢prog 𝒫⊢pres = substᵒ (≡ᵒ-sym ℰ-stmt) (𝒫⊢prog ,ᵒ 𝒫⊢pres)
\end{code}

\begin{code}
ℰ-elim : ∀ {𝒫}{A}{M} → 𝒫 ⊢ᵒ ℰ⟦ A ⟧ M → 𝒫 ⊢ᵒ progress A M ×ᵒ preservation A M
ℰ-elim 𝒫⊢ℰ = substᵒ ℰ-stmt 𝒫⊢ℰ
\end{code}

Next we turn several uses of the fixpoint theorem for 𝒱.
The \textsf{zero} literal is well-behaved at type ℕ.

\begin{code}
𝒱-zero : 𝒱⟦ `ℕ ⟧ `zero ≡ᵒ ⊤ᵒ
𝒱-zero = let X = inj₁ (`ℕ , `zero) in
    𝒱⟦ `ℕ ⟧ `zero
  ⩦⟨ ≡ᵒ-refl refl ⟩
    𝒱⊎ℰ X
  ⩦⟨ fixpointᵒ pre-𝒱⊎ℰ X ⟩
    letᵒ (μᵒ pre-𝒱⊎ℰ) (pre-𝒱⊎ℰ X)
  ⩦⟨ ≡ᵒ-refl refl ⟩
    ⊤ᵒ
  ∎
\end{code}

\noindent The successor of a value is well-behaved at type ℕ
if-and-only-if the value is a well-behaved ℕ.

\begin{code}
𝒱-suc : 𝒱⟦ `ℕ ⟧ (`suc V) ≡ᵒ 𝒱⟦ `ℕ ⟧ V
𝒱-suc {V} = let X = inj₁ (`ℕ , `suc V) in
    𝒱⟦ `ℕ ⟧ (`suc V)
  ⩦⟨ ≡ᵒ-refl refl ⟩
    𝒱⊎ℰ X
  ⩦⟨ fixpointᵒ pre-𝒱⊎ℰ X ⟩
    letᵒ (μᵒ pre-𝒱⊎ℰ) (pre-𝒱⊎ℰ X)
  ⩦⟨ ≡ᵒ-sym (fixpointᵒ pre-𝒱⊎ℰ (inj₁ (`ℕ , V))) ⟩
    𝒱⟦ `ℕ ⟧ V
  ∎

𝒱-suc-I : ∀{𝒫} → 𝒫 ⊢ᵒ 𝒱⟦ `ℕ ⟧ V → 𝒫 ⊢ᵒ 𝒱⟦ `ℕ ⟧ (`suc V)
𝒱-suc-I 𝒱V = substᵒ (≡ᵒ-sym 𝒱-suc) 𝒱V

𝒱-suc-E : ∀{𝒫} → 𝒫 ⊢ᵒ 𝒱⟦ `ℕ ⟧ (`suc V) → 𝒫 ⊢ᵒ 𝒱⟦ `ℕ ⟧ V
𝒱-suc-E 𝒱suc = substᵒ 𝒱-suc 𝒱suc
\end{code}

\noindent A lambda abstraction $ƛ N$ is well-behaved at type $A ⇒ B$
if-and-only-if $N [ W ]$ is well-behaved at $B$ assuming that $W$ is
well-behaved at $A$.

\begin{code}
𝒱-fun : ∀{A B}{N} → 𝒱⟦ A ⇒ B ⟧ (ƛ N) ≡ᵒ (∀ᵒ[ W ] ((▷ᵒ (𝒱⟦ A ⟧ W)) →ᵒ (▷ᵒ (ℰ⟦ B ⟧ (N [ W ])))))
𝒱-fun {A}{B}{N} = let X = (inj₁ (A ⇒ B , ƛ N)) in
     𝒱⟦ A ⇒ B ⟧ (ƛ N)
   ⩦⟨ ≡ᵒ-refl refl ⟩
     𝒱⊎ℰ X
   ⩦⟨ fixpointᵒ pre-𝒱⊎ℰ X ⟩
     letᵒ (μᵒ pre-𝒱⊎ℰ) (pre-𝒱⊎ℰ X)
   ⩦⟨ ≡ᵒ-refl refl ⟩ 
     (∀ᵒ[ W ] ((▷ᵒ (𝒱⟦ A ⟧ W)) →ᵒ (▷ᵒ (ℰ⟦ B ⟧ (N [ W ])))))
   ∎
\end{code}

\noindent A fixpoint value $μ\,V$ is well-behaved at type $A ⇒ B$ if-and-only-if $V$ is
a value and $V[μ\, V]$ is well behaved at $A ⇒ B$.

\begin{code}
𝒱-μ : ∀{A B}{V} → 𝒱⟦ A ⇒ B ⟧ (μ V) ≡ᵒ (Value V)ᵒ ×ᵒ (▷ᵒ (𝒱⟦ A ⇒ B ⟧ (V [ μ V ])))
𝒱-μ {A}{B}{V} = let X = (inj₁ (A ⇒ B , μ V)) in
     𝒱⟦ A ⇒ B ⟧ (μ V)
   ⩦⟨ ≡ᵒ-refl refl ⟩
     𝒱⊎ℰ X
   ⩦⟨ fixpointᵒ pre-𝒱⊎ℰ X ⟩
     letᵒ (μᵒ pre-𝒱⊎ℰ) (pre-𝒱⊎ℰ X)
   ⩦⟨ ≡ᵒ-refl refl ⟩ 
     (Value V)ᵒ ×ᵒ (▷ᵒ (𝒱⟦ A ⇒ B ⟧ (V [ μ V ])))
   ∎
\end{code}

If we have a well-behaved value at type $ℕ$, then it must either be
zero or successor.

\begin{code}
𝒱-ℕ-case : ∀ {𝒫}{ϕ} M → 𝒫 ⊢ᵒ 𝒱⟦ `ℕ ⟧ M
   → (M ≡ `zero → 𝒫 ⊢ᵒ ϕ)
   → (∀ V → M ≡ `suc V → 𝒫 ⊢ᵒ 𝒱⟦ `ℕ ⟧ V → 𝒫 ⊢ᵒ ϕ)
   → 𝒫 ⊢ᵒ ϕ
𝒱-ℕ-case {𝒫}{ϕ} M ⊢𝒱M case-z case-s = aux M (unfoldᵒ pre-𝒱⊎ℰ (inj₁ (`ℕ , M)) ⊢𝒱M) case-z case-s
  where
  aux : ∀ {𝒫}{ϕ} M → 𝒫 ⊢ᵒ letᵒ (μᵒ pre-𝒱⊎ℰ) (pre-𝒱 `ℕ M)
   → (M ≡ `zero → 𝒫 ⊢ᵒ ϕ)
   → (∀ V → M ≡ `suc V → 𝒫 ⊢ᵒ 𝒱⟦ `ℕ ⟧ V → 𝒫 ⊢ᵒ ϕ)
    → 𝒫 ⊢ᵒ ϕ
  aux `zero ⊢𝒱M case-z case-s = case-z refl
  aux (`suc M) ⊢𝒱M case-z case-s =
    case-s M refl (substᵒ (≡ᵒ-sym (fixpointᵒ pre-𝒱⊎ℰ (inj₁ (`ℕ , M)))) ⊢𝒱M)
  aux (L · N) ⊢𝒱M case-z case-s = ⊥-elimᵒ ⊢𝒱M _
  aux (` x) ⊢𝒱M case-z case-s = ⊥-elimᵒ ⊢𝒱M _
  aux (ƛ N) ⊢𝒱M case-z case-s = ⊥-elimᵒ ⊢𝒱M _
  aux (case L M N) ⊢𝒱M case-z case-s = ⊥-elimᵒ ⊢𝒱M _
  aux (μ N) ⊢𝒱M case-z case-s = ⊥-elimᵒ ⊢𝒱M _
\end{code}

If we have a well-behaved value at a function type $A ⇒ B$,
then it must either be a lambda abstraction or a fixpoint value.

\begin{code}
𝒱-fun-case : ∀{𝒫}{A}{B}{V}{R} → 𝒫 ⊢ᵒ 𝒱⟦ A ⇒ B ⟧ V
  → (∀ N → V ≡ ƛ N → 𝒫 ⊢ᵒ R)  →  (∀ V′ → V ≡ μ V′ → 𝒫 ⊢ᵒ R)  →  𝒫 ⊢ᵒ R
𝒱-fun-case {𝒫}{A}{B}{V}{R} ⊢𝒱V caseλ caseμ =
  aux A B V (unfoldᵒ pre-𝒱⊎ℰ (inj₁ (A ⇒ B , V)) ⊢𝒱V) caseλ caseμ
  where
  aux : ∀ {𝒫} A B V → 𝒫 ⊢ᵒ letᵒ (μᵒ pre-𝒱⊎ℰ) (pre-𝒱 (A ⇒ B) V)
    → (∀ N → V ≡ ƛ N → 𝒫 ⊢ᵒ R)  →  (∀ V′ → V ≡ μ V′ → 𝒫 ⊢ᵒ R) → 𝒫 ⊢ᵒ R
  aux {𝒫} A B (ƛ N) 𝒱V caseλ caseμ = caseλ N refl
  aux {𝒫} A B (μ N) 𝒱V caseλ caseμ = caseμ N refl
  aux {𝒫} A B (L · M) 𝒱V caseλ caseμ = ⊥-elimᵒ 𝒱V _
  aux {𝒫} A B (case L M N) 𝒱V caseλ caseμ = ⊥-elimᵒ 𝒱V _
  aux {𝒫} A B (` x) 𝒱V caseλ caseμ = ⊥-elimᵒ 𝒱V _
  aux {𝒫} A B `zero 𝒱V caseλ caseμ = ⊥-elimᵒ 𝒱V _
  aux {𝒫} A B (`suc V) 𝒱V caseλ caseμ = ⊥-elimᵒ 𝒱V _
\end{code}

\noindent A well-behaved value is of course a value.

\begin{code}
𝒱⇒Value : ∀ {𝒫} A M → 𝒫 ⊢ᵒ 𝒱⟦ A ⟧ M → 𝒫 ⊢ᵒ (Value M)ᵒ
𝒱⇒Value {𝒫} A M ⊢𝒱M = aux A M (unfoldᵒ pre-𝒱⊎ℰ (inj₁ (A , M)) ⊢𝒱M)
  where
  aux : ∀ {𝒫} A M → 𝒫 ⊢ᵒ letᵒ (μᵒ pre-𝒱⊎ℰ) (pre-𝒱 A M) → 𝒫 ⊢ᵒ (Value M)ᵒ
  aux `ℕ `zero ⊢𝒱M = pureᵒI V-zero
  aux `ℕ (`suc M) ⊢𝒱M =
     let IH = 𝒱⇒Value `ℕ M (foldᵒ pre-𝒱⊎ℰ (inj₁ (`ℕ , M)) ⊢𝒱M) in
     pureᵒE IH λ vM → pureᵒI (V-suc vM)
  aux `ℕ (L · N) ⊢𝒱M = ⊥-elimᵒ ⊢𝒱M _
  aux `ℕ (` x) ⊢𝒱M = ⊥-elimᵒ ⊢𝒱M _
  aux `ℕ (ƛ N) ⊢𝒱M = ⊥-elimᵒ ⊢𝒱M _
  aux `ℕ (case L M N) ⊢𝒱M = ⊥-elimᵒ ⊢𝒱M _
  aux `ℕ (μ N) ⊢𝒱M = ⊥-elimᵒ ⊢𝒱M _
  aux (A ⇒ B) (ƛ N) ⊢𝒱M = pureᵒI V-ƛ
  aux (A ⇒ B) (μ N) ⊢𝒱M = pureᵒE (proj₁ᵒ ⊢𝒱M) λ vN → pureᵒI (V-μ vN)
  aux (A ⇒ B) (` x) ⊢𝒱M = ⊥-elimᵒ ⊢𝒱M _
  aux (A ⇒ B) (L · N) ⊢𝒱M = ⊥-elimᵒ ⊢𝒱M _
  aux (A ⇒ B) (case L M N) ⊢𝒱M = ⊥-elimᵒ ⊢𝒱M _
  aux (A ⇒ B) `zero ⊢𝒱M = ⊥-elimᵒ ⊢𝒱M _
  aux (A ⇒ B) (`suc M) ⊢𝒱M = ⊥-elimᵒ ⊢𝒱M _
\end{code}

\noindent A well-behaved value is also a well-behaved term.

\begin{code}
𝒱⇒ℰ : ∀{A}{𝒫}{V} →  𝒫 ⊢ᵒ 𝒱⟦ A ⟧ V  →  𝒫 ⊢ᵒ ℰ⟦ A ⟧ V
𝒱⇒ℰ {A}{𝒫}{V} 𝒫⊢𝒱V = ℰ-intro prog pres
    where prog = inj₁ᵒ 𝒫⊢𝒱V
          pres = Λᵒ[ N ] →ᵒI (pureᵒE Zᵒ λ V—→N →
                   pureᵒE (Sᵒ (𝒱⇒Value A V 𝒫⊢𝒱V)) λ v →
                   ⊥-elimₛ (value-irreducible v V—→N))
\end{code}

\subsection{Definition of Semantic Type Safety for Open Terms}
\label{sec:sem-type-safety}

The predicates 𝒱 and ℰ characterize well-behaved terms without any
free variables, that is, closed terms. (Note that the definition of
\textsf{pre-𝒱} does not include a case for variables.)  However, we
shall also need to handle terms with free variables, i.e., open
terms.  The standard approach is to apply a substitution,
mapping variables to closed values, to turn the open term into a
closed term.

The following defines a well-behaved substitution, that is, a
substitution that maps variables to well-behaved values.

\begin{code}
𝓖⟦_⟧ : (Γ : List Type) → Subst → List (Setᵒ [] [])
𝓖⟦ [] ⟧ σ = []
𝓖⟦ A ∷ Γ ⟧ σ = (𝒱⟦ A ⟧ (σ 0)) ∷ 𝓖⟦ Γ ⟧ (λ x → σ (suc x))
\end{code}

\noindent A term $V$ is a well-behaved open value at type $A$ in type
environment Γ if, for any well-behaved substitution γ, $⟪ γ ⟫\, V$ is
a well behaved value.

\begin{code}
infix 3 _⊨ⱽ_⦂_
_⊨ⱽ_⦂_ : List Type → Term → Type → Prop
Γ ⊨ⱽ V ⦂ A = ∀ (γ : Subst) → 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝒱⟦ A ⟧ (⟪ γ ⟫ V)
\end{code}

\noindent A term $M$ is well-behaved open term at type $A$ in
type environment Γ if, for any well-behaved substitution γ,
$⟪ γ ⟫\, M$ is well behaved.

\begin{code}
infix 3 _⊨_⦂_
_⊨_⦂_ : List Type → Term → Type → Prop
Γ ⊨ M ⦂ A = ∀ (γ : Subst) → 𝓖⟦ Γ ⟧ γ ⊢ᵒ ℰ⟦ A ⟧ (⟪ γ ⟫ M)
\end{code}

The proof of semantic type safety will make use of the Fundamental
Lemma for this logical relation, which states that a well-typed term
is also a well-behaved open term. More formally, $Γ ⊢ M ⦂ A$ implies
$Γ ⊨ M ⦂ A$ (and likewise for well-typed values).  The proof will be
by induction on the derivation of $Γ ⊢ M ⦂ A$, with a case for each
typing rule. Each of those cases will be proved in a separate
``compatibility`` lemma in Section~\ref{sec:compatibility-lemmas}.
But first we prove the ``bind'' lemma.



