\begin{comment}
\begin{code}
{-# OPTIONS --without-K --prop #-}

open import Data.Nat using (ℕ; zero; suc; _+_)

open import PropP
open import Variables
open import RawSetO
open import SetO
open import Approx
open import Env
open import EquivalenceRelationProp

module Later where
\end{code}
\end{comment}

\subsection{Later: Semantics and Lemmas}

The following ▷ function defines the semantics of the later operator
in SIL.  It says that a proposition ϕ is true later when it is true at
all step indices that are strictly smaller than the current one.

\begin{code}
▷ : Setₒ → Setₒ
▷ ϕ k = ∀ j → j <ₚ k → ϕ j
\end{code}

\noindent An alternative definition is to say that ▷ ϕ is true at $k$
if ϕ is true at $k \minus 1$, unless $k=0$ in which case $▷ ϕ$ is true
unconditionally~\citep{Dreyer:2011wl}. We prefer the above definition
because it does not involve case splitting, which inhibits automatic
reasoning in Agda.

The later operator is downward closed.

\begin{code}
down-later : ∀{Γ}{Δ : Times Γ} (ϕ : Setᵒ Γ Δ)
  → ∀ δ → downClosedᵈ δ → downClosed (▷ (# ϕ δ))
down-later {Γ}{Δ} ϕ δ down-δ n ▷ϕn k k≤n j j<k = ▷ϕn j (≤-transₚ{suc j}{k}{n} j<k k≤n)
\end{code}

The later operator admits the followig congruence rule.

\begin{code}
cong-▷ : ∀{ϕ ψ : Setₒ} → ϕ ≡ₒ ψ → ▷ ϕ ≡ₒ ▷ ψ
cong-▷ {ϕ}{ψ} ϕ=ψ i = (λ ▷ϕi j j<i → let ψj = proj₁ₚ (ϕ=ψ j) (▷ϕi j j<i) in ψj)
        ,ₚ (λ ▷ψi j j<i → let ϕj = proj₂ₚ (ϕ=ψ j) (▷ψi j j<i) in ϕj)
\end{code}

The later operator is contractive in the following sense.

\begin{code}
contractive-▷ : ∀{k} (S : Setₒ) → ▷ S ≡ₒ[ suc k ] ▷ (↓ k S)
contractive-▷ {k} S zero = (λ _ → ttₚ ,ₚ (λ x ())) ,ₚ (λ _ → ttₚ ,ₚ (λ x ()))
contractive-▷ {k} S (suc i) = (λ { (x ,ₚ x₁) → x ,ₚ (λ j x₂ → ≤-transₚ{suc j}{suc i}{k} x₂ x ,ₚ (x₁ j x₂))})
     ,ₚ λ { (x ,ₚ ▷↓kSsi) → x ,ₚ (λ j x₂ → let xx = ▷↓kSsi j x₂ in proj₂ₚ xx)}
\end{code}

The formula \textsf{▷ S} is well formed in the environment
\textsf{laters Γ}.  To prove this, we need to show that \textsf{▷ S}
is contractive with respect to any variable $x$ in the environment.
That is, we need to show that
\[
   ▷ (S \; δ) ≡ₒ\!\![ k\plus 1 ] ▷ (S \; (↓ᵈ_j x δ))
\]
We know that \textsf{S} is well formed, so in particular, \textsf{S} is
well formed with respect to $x$ at time \textsf{timeof x Δ}. The proof
then splits into the two cases for \textsf{timeof x Δ}, either
\textsf{Now} or \textsf{Later}. If the time of $x$ in Δ is \textsf{Now},
then we know that \textsf{S} is nonexpansive in $x$
(that is, $↓_k (S \; δ) ≡ₒ ↓_k (S \; (↓ᵈ_j x δ))$). Therefore we have
\begin{align*}
  ↓_{k\plus 1} ▷ (S \; δ)  &≡ₒ ↓_{k\plus 1} ▷ ↓_k (S \; δ) \\
  & ≡ₒ ↓_{k\plus 1} ▷ ↓_k (S \; (↓ᵈ_j x δ)) \\
  & ≡ₒ ↓_{k\plus 1} ▷ (S \; (↓ᵈ_j x δ))
\end{align*}
On the other hand, if the time of $x$ in Δ is \textsf{Later},
then we know that \textsf{S} is contractive in $x$
(that is, $↓_{k\plus 1} (S \; δ) ≡ₒ ↓_{k\plus 1} (S \; (↓ᵈ_j x δ))$).
Therefore we have
\begin{align*}
   ↓_{k\plus 1} ▷ (S \; δ) & ≡ₒ ↓_{k\plus 1} ↓_{k \plus 2} ▷ (S \; δ) \\
   & ≡ₒ ↓_{k\plus 1} ↓_{k \plus 2} ▷ ↓_{k\plus 1} (S \; δ) \\
   & ≡ₒ ↓_{k\plus 1} ↓_{k \plus 2} ▷ ↓_{k\plus 1} (S \; (↓ᵈ_j x δ)) \\
  & ≡ₒ ↓_{k\plus 1} ↓_{k \plus 2} ▷ (S \; (↓ᵈ_j x δ)) \\
  & ≡ₒ ↓_{k\plus 1} ▷ (S \; (↓ᵈ_j x δ))
\end{align*}

\noindent The following proof in Agda provides the justification for each step.

\begin{code}
wellformed-▷ : ∀{Γ}{Δ : Times Γ}(S : Setᵒ Γ Δ) → wellformed-prop (laters Γ) (λ δ → ▷ (# S δ))
wellformed-▷ {Γ}{Δ} S x rewrite timeof-later{Γ} x
    with wellformed S x
... | wellformedS {- wellformedS : wellformed-var x (timeof x Δ) (# S) -}
    with timeof x Δ
... | Now = λ δ j k k≤j → {- wellformedS : nonexpansive x (# S) -}
    let nonexpansiveSx = wellformedS δ j k k≤j in
      ↓ (suc k) (▷ (# S δ))
    ⩦⟨ contractive-▷ (# S δ) ⟩
      ↓ (suc k) (▷ (↓ k (# S δ)))
    ⩦⟨ cong-approx (suc k) (cong-▷ nonexpansiveSx) ⟩
      ↓ (suc k) (▷ (↓ k (# S (↓ᵈ j x δ))))
    ⩦⟨ ≡ₒ-sym (contractive-▷ (# S (↓ᵈ j x δ))) ⟩
      ↓ (suc k) (▷ (# S (↓ᵈ j x δ)))
    ∎
... | Later =  λ δ j k k≤j → {- wellformedS: contractive x (# S) -}
    let contractiveSx = wellformedS δ j k k≤j in
      ↓ (suc k) (▷ (# S δ))
    ⩦⟨ ≡ₒ-sym (lemma17 (suc k)) ⟩
      ↓ (suc k) (↓ (2 + k) (▷ (# S δ)))
    ⩦⟨ cong-approx (suc k) (contractive-▷ (# S δ)) ⟩
      ↓ (suc k) (↓ (2 + k) (▷ (↓ (suc k) (# S δ))))
    ⩦⟨ cong-approx (suc k) (cong-approx (2 + k) (cong-▷ contractiveSx)) ⟩
      ↓ (suc k) (↓ (2 + k) (▷ (↓ (suc k) ((# S) (↓ᵈ j x δ)))))
    ⩦⟨ ≡ₒ-sym (cong-approx (suc k) (contractive-▷ (# S (↓ᵈ j x δ)))) ⟩
      ↓ (suc k) (↓ (2 + k) (▷ (# S (↓ᵈ j x δ))))
    ⩦⟨ lemma17 (suc k) ⟩
      ↓ (suc k) (▷ (# S (↓ᵈ j x δ)))
    ∎
\end{code}

