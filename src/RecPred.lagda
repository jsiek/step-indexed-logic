\begin{comment}
\begin{code}
{-# OPTIONS --without-K --prop #-}
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_,_;_×_) -- ; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Nat using (ℕ; zero; suc; _+_)
--open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_; _∸_; z≤n; s≤s; _≤′_; ≤′-step)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans)

open import PropP
open import RawSetO
open import SetO
open import Variables
open import Env
open import Approx
open import Iteration
open import Fixpoint
open import EquivalenceRelationProp

module RecPred where
\end{code}
\end{comment}

\subsection{Recursive Predicates: Downward closed, Wellformed, Congruent}

We defined the semantics of recursive predicates in
\S\ref{sec:fixpoint-lemmas}, with the \textsf{mu} function. In this
section we prove the triad of properties that are needed to define
the μᵒ operator in Setᵒ. 

Given a downward closed recursive environment δ, \textsf{mu Sᵃ δ a} is
also downward closed. So we are given a $j ≤ k$ and may assume
\textsf{mu Sᵃ δ a k}, and need to show \textsf{mu Sᵃ δ a j}.
Unfolding \textsf{mu} in the premise, we have $(⟅ Sᵃ ⟆ δ)^{1 \plus k} ⊤ᵖ a k$
and therefore$(⟅ Sᵃ ⟆ δ)^{1 \plus k} ⊤ᵖ a j$ because function iteration is
downward closed (\textsf{down-iter} from \S\ref{sec:iteration}).
Lemma 15 (\textsf{lemma15b-env-fun} of \S\ref{sec:fixpoint-lemmas})
tells us that $(⟅ Sᵃ ⟆ δ)^{1 \plus k} ⊤ᵖ a j$
is $(j\plus 1)$-equivalent to $(⟅ Sᵃ ⟆ δ)^{1 \plus j} ⊤ᵖ a j$,
so we can conclude that $(⟅ Sᵃ ⟆ δ)^{1 \plus j} ⊤ᵖ a j$,
that is, \textsf{mu Sᵃ δ a j}.

\begin{code}
down-mu : ∀{Γ}{Δ}{A}(Sᵃ : A → Setᵒ (A ∷ Γ) (Later ∷ Δ)) (a : A) (δ : RecEnv Γ)
   → downClosedᵈ δ → downClosed (mu Sᵃ δ a)
down-mu Sᵃ a δ dc-δ k μSᵃa-k j j≤k =
   let dc-Sδ : downClosed-fun (⟅ Sᵃ ⟆ δ)
       dc-Sδ = λ P a′ dc-P → down (Sᵃ a′) (P , δ) (dc-P ,ₚ dc-δ) in
   let Sδsk-j : ((⟅ Sᵃ ⟆ δ ^ (1 + k)) ⊤ᵖ) a j
       Sδsk-j = down-iter (suc k) (⟅ Sᵃ ⟆ δ) dc-Sδ a k μSᵃa-k j j≤k in
   let eq : (((⟅ Sᵃ ⟆ δ ^ (1 + j)) ⊤ᵖ) a)  ≡ₒ[ 1 + j ]  (((⟅ Sᵃ ⟆ δ ^ (1 + k)) ⊤ᵖ) a)
       eq = lemma15b-env-fun {δ = δ} (1 + k) (1 + j) Sᵃ a (s≤sₚ{j}{k} j≤k) in
   let Sδsj-j : ((⟅ Sᵃ ⟆ δ) ^ (1 + j)) ⊤ᵖ a j
       Sδsj-j = proj₂ₚ (proj₂ₚ (eq j) ((≤-reflₚ{j}) ,ₚ Sδsk-j)) in
   Sδsj-j
\end{code}

Next we prove that \textsf{mu} produces wellformed propositions. The
proof has two cases.  When the variable is at time \textsf{Now}, we
need to show that \textsf{mu} is nonexpansive; whereas when the
variable is at time \textsf{Later}, we need to show that \textsf{mu}
is contractive.

To show that \textsf{mu} is nonexpansive, we need to show that
$\mathsf{mu}\; Sᵃ\; δ\; a ≡ₒ\!\![ k ]\; \mathsf{mu}\; Sᵃ\; (↓ᵈ_j x δ) \; a$.
We proceed by induction on $k$. The base case $k=0$ is trivially true.
For the induction step, we assume
\begin{align*}
\mathsf{mu}\; Sᵃ\; δ\; a & ≡ₒ\!\![ k′ ]\; \mathsf{mu}\; Sᵃ\; (↓ᵈ_j x δ) \; a & \text{(IH)}
\end{align*}
and need to prove the same but for $1 \plus k′$.
The proof is by the following equational reasoning.
\begin{align*}
      & ↓_{1 \plus k′} (\mathsf{mu}\; Sᵃ\; δ\; a) \\
      & ≡ₒ ↓_{1 \plus k′} ((Sᵃ \; a) \; (\mathsf{mu}\; Sᵃ\; δ , δ)) & \text{by Lemma 19a of \S\ref{sec:fixpoint-lemmas}} \\
      & ≡ₒ ↓_{1 \plus k′} ((Sᵃ \; a) \; (\mathsf{mu}\; Sᵃ\; δ , ↓ᵈ_j x δ)) & \text{$(Sᵃ\;a)$ is nonexpansive wrt. variable $1 \plus x$} \\
      & ≡ₒ ↓_{1 \plus k′} ((Sᵃ\; a) \; (↓ᵖ_{k′} (\mathsf{mu}\; Sᵃ\; δ) , ↓ᵈ_j x δ)) & \text{$(Sᵃ\;a)$ is contractive wrt. variable $0$} \\
      & ≡ₒ ↓_{1 \plus k′} ((Sᵃ \; a) \; (↓ᵖ_{k′} (\mathsf{mu}\; Sᵃ\; (↓ᵈ_j x δ)) , ↓ᵈ_j x δ)) & \text{by (IH)}\\
      & ≡ₒ ↓_{1 \plus k′} ((Sᵃ\; a) \;(\mathsf{mu}\; Sᵃ\; (↓ᵈ_j x δ) , ↓ᵈ_j x δ)) & \text{$(Sᵃ\;a)$ is contractive wrt. variable $0$} \\
      & ≡ₒ ↓ _{1 \plus k′} (\mathsf{mu}\; Sᵃ\; (↓ᵈ_j x δ) a) & \text{by Lemma 19a of \S\ref{sec:fixpoint-lemmas}}
\end{align*}
\noindent The Agda proof is in figure~\ref{fig:mu-nonexpansive}.

\begin{figure}[tbp]
\begin{code}
mu-nonexpansive : ∀{Γ}{Δ : Times Γ}{A}{B} (Sᵃ : A → Setᵒ (A ∷ Γ) (Later ∷ Δ)) (a : A) (x : Γ ∋ B)
   → timeof x Δ ≡ Now → (δ : RecEnv Γ) (k j : ℕ) → (k ≤ₚ j)
   → mu Sᵃ δ a ≡ₒ[ k ] mu Sᵃ (↓ᵈ j x δ) a
mu-nonexpansive {Γ} {Δ} {A} Sᵃ a x time-x δ zero j k≤j = ≡ₒ[0]
mu-nonexpansive {Γ} {Δ} {A}{B} Sᵃ a x time-x δ (suc k′) j k≤j =
      ↓ (suc k′) (mu Sᵃ δ a)
  ⩦⟨ lemma19a Sᵃ a δ (suc k′) ⟩
      ↓ (suc k′) (# (Sᵃ a) (mu Sᵃ δ , δ))
  ⩦⟨ nonexpansive-Sa-sx (mu Sᵃ δ , δ) j (suc k′) k≤j ⟩
      ↓ (suc k′) (# (Sᵃ a) (mu Sᵃ δ , ↓ᵈ j x δ))
  ⩦⟨ contractive-Sa-z (mu Sᵃ δ , ↓ᵈ j x δ) k′ k′ (≤-reflₚ{k′}) ⟩
      ↓ (suc k′) (# (Sᵃ a) (↓ᵖ k′ (mu Sᵃ δ) , ↓ᵈ j x δ))
  ⩦⟨ cong-approx (suc k′) (congr (Sᵃ a) (IH ,ₚ ≡ᵈ-refl)) ⟩
      ↓ (suc k′) (# (Sᵃ a) (↓ᵖ k′ (mu Sᵃ (↓ᵈ j x δ)) , ↓ᵈ j x δ))
  ⩦⟨ ≡ₒ-sym (contractive-Sa-z (mu Sᵃ (↓ᵈ j x δ) , ↓ᵈ j x δ) k′ k′ (≤-reflₚ{k′})) ⟩
      ↓ (suc k′) (# (Sᵃ a) (mu Sᵃ (↓ᵈ j x δ) , ↓ᵈ j x δ))
  ⩦⟨ ≡ₒ-sym (lemma19a Sᵃ a (↓ᵈ j x δ) (suc k′)) ⟩
      ↓ (suc k′) (mu Sᵃ (↓ᵈ j x δ) a)
  ∎
  where
  nonexpansive-Sa-sx : nonexpansive (sucᵒ x) (# (Sᵃ a))
  nonexpansive-Sa-sx = wellformed-now⇒nonexpansive{x = sucᵒ x}{Δ = Later ∷ Δ}
                            (wellformed (Sᵃ a) (sucᵒ x)) time-x
  contractive-Sa-z : contractive zeroᵒ (# (Sᵃ a))
  contractive-Sa-z = wellformed (Sᵃ a) zeroᵒ 
  IH : ∀ a → ↓ k′ (mu Sᵃ δ a) ≡ₒ ↓ k′ (mu Sᵃ (↓ᵈ j x δ) a)
  IH a = mu-nonexpansive Sᵃ a x time-x δ k′ j (≤-transₚ{k′}{suc k′}{j} (n≤1+nₚ k′) k≤j)
\end{code}
\caption{\textsf{mu} is nonexpansive}
\label{fig:mu-nonexpansive}
\end{figure}

Next we prove that \textsf{mu} is contractive, so we need to show that
$\mathsf{mu}\; Sᵃ\; δ\; a ≡ₒ\!\![ 1 \plus k ] \mathsf{mu}\; Sᵃ\; (↓ᵈ_j x δ) a$.
We prove this by induction on $k$ and equational reasoning:
\begin{align*}
    &  ↓_{1 \plus k} (\mathsf{mu}\; Sᵃ\; δ\; a) \\
    & ≡ₒ ↓_{1 \plus k} ((Sᵃ\; a) \;(\mathsf{mu}\; Sᵃ\; δ , δ)) & \text{by Lemma 19a} \\
    & ≡ₒ ↓_{1 \plus k} ((Sᵃ\; a) \;(\mathsf{mu}\; Sᵃ\; δ , ↓ᵈ_j x δ))
       & \text{because $(Sᵃ\;a)$ is contractive in variable $1\plus x$} \\ 
    & ≡ₒ ↓_{1 \plus k} ((Sᵃ \; a) \; (↓ᵖ_k (\mathsf{mu}\; Sᵃ\; δ) , ↓ᵈ_j x δ))      
       & \text{because $(Sᵃ\;a)$ is contractive in variable $0$} \\
    & ≡ₒ ↓_{1 \plus k} ((Sᵃ \;a)\; (↓ᵖ_k (\mathsf{mu}\; Sᵃ\; (↓ᵈ_j x δ)) , ↓ᵈ_j x δ))
       & \text{by cases on $k$ and the induction hypothesis} \\
    & ≡ₒ ↓_{1 \plus k} ((Sᵃ \; a) \; (\mathsf{mu}\; Sᵃ\; (↓ᵈ_j x δ) , (↓ᵈ_j x δ)))
      & \text{because $(Sᵃ\;a)$ is contractive in variable $0$} \\
    & ≡ₒ ↓_{1 \plus k} (\mathsf{mu}\; Sᵃ\; (↓ᵈ_j x δ) \; a)
      & \text{by Lemma 19a}
\end{align*}
\noindent The Agda proof is in figure~\ref{fig:mu-contractive}.

\begin{figure}[tbp]
\begin{code}
mu-contractive : ∀{A}{Γ}{Δ}{B} → (Sᵃ : A → Setᵒ (A ∷ Γ) (Later ∷ Δ)) (a : A) (x : Γ ∋ B)
   → timeof x Δ ≡ Later → (δ : RecEnv Γ) (k j : ℕ) → (k ≤ₚ j)
   → mu Sᵃ δ a ≡ₒ[ 1 + k ] mu Sᵃ (↓ᵈ j x δ) a
mu-contractive {A} {Γ} {Δ} {B} Sᵃ a x time-x δ k j k≤j =
      ↓ (suc k) (mu Sᵃ δ a)
  ⩦⟨ lemma19a Sᵃ a δ (suc k) ⟩
      ↓ (suc k) (# (Sᵃ a) (mu Sᵃ δ , δ))
  ⩦⟨ contractive-Sᵃ-sx (mu Sᵃ δ , δ) j k k≤j ⟩
      ↓ (suc k) (# (Sᵃ a) (mu Sᵃ δ , ↓ᵈ j x δ))
  ⩦⟨ contractive-Sa-z (mu Sᵃ δ , ↓ᵈ j x δ) k k (≤-reflₚ{k}) ⟩      
      ↓ (suc k) (# (Sᵃ a) (↓ᵖ k (mu Sᵃ δ) , ↓ᵈ j x δ))
  ⩦⟨ cong-approx (suc k) (congr (Sᵃ a) (IH k k≤j ,ₚ ≡ᵈ-refl)) ⟩      
      ↓ (suc k) (# (Sᵃ a) (↓ᵖ k (mu Sᵃ (↓ᵈ j x δ)) , ↓ᵈ j x δ))
  ⩦⟨ ≡ₒ-sym (contractive-Sa-z (mu Sᵃ (↓ᵈ j x δ) , ↓ᵈ j x δ) k k (≤-reflₚ{k})) ⟩
      ↓ (suc k) (# (Sᵃ a) (mu Sᵃ (↓ᵈ j x δ) , (↓ᵈ j x δ)))
  ⩦⟨ ≡ₒ-sym (lemma19a Sᵃ a (↓ᵈ j x δ) (suc k)) ⟩  
      ↓ (suc k) (mu Sᵃ (↓ᵈ j x δ) a)
  ∎
  where
  contractive-Sᵃ-sx : contractive (sucᵒ x) (# (Sᵃ a))
  contractive-Sᵃ-sx = wellformed-later⇒contractive {A = B}{sucᵒ x}{Δ = Later ∷ Δ}
                       (wellformed (Sᵃ a) (sucᵒ x)) time-x
  contractive-Sa-z : contractive zeroᵒ (# (Sᵃ a))
  contractive-Sa-z = wellformed (Sᵃ a) zeroᵒ 
  IH : ∀ k → k ≤ₚ j → ∀ a → ↓ k (mu Sᵃ δ a) ≡ₒ ↓ k (mu Sᵃ (↓ᵈ j x δ) a)
  IH zero  k≤j a = ≡ₒ[0]
  IH (suc k) k≤j a = mu-contractive Sᵃ a x time-x δ k j (≤-transₚ{k}{suc k}{j} (n≤1+nₚ k) k≤j)
\end{code}
\caption{\textsf{mu} is contractive}
\label{fig:mu-contractive}
\end{figure}

\noindent With the above two lemmas complete, we prove that
\textsf{mu} is wellformed.

\begin{code}
wellformed-mu : ∀{Γ}{Δ : Times Γ}{A} (Sᵃ : A → Setᵒ (A ∷ Γ) (Later ∷ Δ)) (a : A)
   → wellformed-prop Δ (λ δ → mu Sᵃ δ a)
wellformed-mu {Γ} {Δ} {A} Sᵃ a x
    with timeof x Δ in time-x
... | Now = λ δ j k k≤j → mu-nonexpansive Sᵃ a x time-x δ k j k≤j
... | Later = λ δ j k k≤j → mu-contractive Sᵃ a x time-x δ k j k≤j
\end{code}

It remains to prove that \textsf{mu} is congruent. We first show that
function iteration is congruent in the following lemma.

\begin{code}
cong-iter : ∀{A}{a : A} (i : ℕ) (f g : Predₒ A → Predₒ A)
  → (∀ P Q a → (∀ b → P b ≡ₒ Q b) → f P a ≡ₒ g Q a) → (I : Predₒ A)
  → (f ^ i) I a ≡ₒ (g ^ i) I a
cong-iter zero f g f=g I = ≡ₒ-refl refl
cong-iter{A}{a} (suc i) f g f=g I =
  let IH = λ b → cong-iter{A}{b} i f g f=g I in
  f=g ((f ^ i) I) ((g ^ i) I) a IH
\end{code}

\noindent Our goal is a direct corollary of the lemma.

\begin{code}
congruent-mu : ∀{Γ}{Δ : Times Γ}{A} (Sᵃ : A → Setᵒ (A ∷ Γ) (Later ∷ Δ)) (a : A)
   → congruent (λ δ → mu Sᵃ δ a)
congruent-mu{Γ}{Δ}{A} Sᵃ a {δ}{δ′} δ=δ′ k =
  cong-iter (suc k) (⟅ Sᵃ ⟆ δ) (⟅ Sᵃ ⟆ δ′) (λ P Q a P=Q → congr (Sᵃ a) (P=Q ,ₚ δ=δ′)) ⊤ᵖ k
\end{code}
