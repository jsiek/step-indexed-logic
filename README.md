# step-indexed-logic
A modal logic for reasoning about step-indexed logical relations

The Step-indexed Logic (SIL) includes first-order logic (i.e., a logic
with "and", "or", "implies", "for all", etc.). To distinguish its
connectives from Agda's, we add a superscript "o". So "and" is written
`×ᵒ`, "implies" is written `→ᵒ`, and so on.  SIL also includes a
notion of time in which there is a clock counting down. The logic is
designed in such a way that if a formula `P` is true at some time then
`P` stays true in the future (at lower counts). So formulas are
downward closed.  When the clock reaches zero, every formula becomes
true.  Furthermore, the logic includes a "later" operator, written `▷ᵒ
P`, meaning that `P` is true one clock tick in the future. When we use
SIL to reason about the cast calculus, one clock tick will correspond
to one reduction step.

Just as `Set` is the type of true/false formulas in Agda, `Setᵒ` is
the type of true/false formulas in SIL. It is a record that bundles
the formula itself, represented with a function of type `ℕ → Set`,
with proofs that the formula is downward closed and true at zero.

    record Setᵒ : Set₁ where
      field
        # : ℕ → Set
        down : downClosed #
        tz : # 0                -- tz short for true at zero
    open Setᵒ public

For example, the "false" proposition is false at every time except zero.

    ⊥ᵒ : Setᵒ
    ⊥ᵒ = record { # = λ { zero → ⊤ ; (suc k) → ⊥ }
                ; down = ... ; tz = ... }

The "and" proposition `P ×ᵒ Q` is true at a given time `k` if both `P`
and `Q` are true at time `k`.

    _×ᵒ_ : Setᵒ → Setᵒ → Setᵒ
    P ×ᵒ Q = record { # = λ k → # P k × # Q k
                    ; down = ... ; tz = ... }

The "for all" proposition `∀ᵒ[ a ] P` is true at a given time `k` if
the predicate `P` is true for all `a` at time `k`.

    ∀ᵒ : ∀{A : Set} → (A → Setᵒ) → Setᵒ
    ∀ᵒ{A} P = record { # = λ k → ∀ (a : A) → # (P a) k
                     ; down = ... ; tz = ... }

The "exists" proposition `∃ᵒ[ a ] P` is true at a given time `k` if
the predicate `P` is true for some `a` at time `k`. However, we
must require that the type `A` is inhabited so that this proposition
is true at time zero.

    ∃ᵒ : ∀{A : Set}{{_ : Inhabited A}} → (A → Setᵒ) → Setᵒ
    ∃ᵒ{A} P = record { # = λ k → Σ[ a ∈ A ] # (P a) k
                         ; down = ... ; tz = ... }

We embed arbitrary Agda formulas into the step-indexed logic with the
following constant operator, written `S ᵒ`, which is true if and only
if `S` is true, except at time zero, when `S ᵒ` has to be true.

    _ᵒ  : Set → Setᵒ
    S ᵒ = record { # = λ { zero → ⊤ ; (suc k) → S }
                 ; down = ... ; tz = ... }

Next we discuss the most important and interesting of the propositions,
the one for defining a recursive predicate. The following is a first
attempt at writing down the type of this proposition. The idea is that
this constructor of recursive predicates works like the Y-combinator
in that it turns a non-recursive predicate into a recursive one.

    μᵒ : ∀{A}
       → (A → (A → Setᵒ) → Setᵒ)
         -----------------------
       → A → Setᵒ

The non-recursive predicate has type `A → (A → Setᵒ) → Setᵒ`. It has
an extra parameter `(A → Setᵒ)` that will be bound to the
recursive predicate itself. To clarify, lets look at an example.
Suppose we want to define multi-step reduction according to
the following rules:

                M —→ L    L —→* N
    -------     ------------------
    M —→* M     M —→* N

We would first define a non-recursive predicate that has an extra
parameter, let us name it `R` for recursion. Inside the definition of
`mreduce`, we use `R` is the place where we would recursively use
`mreduce`, as follows.

    mreduce : Term × Term → (Term × Term → Setᵒ) → Setᵒ
    mreduce (M , N) R = (M ≡ N)ᵒ ⊎ᵒ (∃ᵒ[ L ] (M —→ L)ᵒ ×ᵒ R (L , N))

Because we use `∃ᵒ` with a Term, we need to prove that Term is inhabited.

```
instance
  TermInhabited : Inhabited Term
  TermInhabited = record { elt = ` 0 }

```
We then apply the `μᵒ` proposition to `mreduce` to
obtain the desired recursive predicate `—→*`.

    _—→*_ : Term → Term → Setᵒ
    M —→* N = μᵒ mreduce (M , N)

The problem with the above story is that it's not possible in Agda (to
my knowledge) to construct a recursive predicate from an arbitrary
function of type `A → (A → Setᵒ) → Setᵒ`. Instead, we need to place
restrictions on the function. In particular, if we make sure that the
recursion never happens "now", but only "later", then it becomes
possible to construct `μᵒ`. We define the `Setˢ` type in Agda to
capture this restriction. (The superscript "s" stands for step
indexed.) Furthermore, to allow the nesting of recursive definitions,
we must generalize from a single predicate parameter to an environment
of predicates. The type of the environment is given by a `Context`:

    Context : Set₁
    Context = List Set

We represent an environment of recursive predicates with a tuple of
the following type.

    RecEnv : Context → Set₁
    RecEnv [] = topᵖ 
    RecEnv (A ∷ Γ) = (A → Setᵒ) × RecEnv Γ

We use de Bruijn indices to represent the variables that refer to the
recursive predicates, which we define as follows.

    data _∋_ : Context → Set → Set₁ where
      zeroˢ : ∀{Γ}{A} → (A ∷ Γ) ∋ A
      sucˢ : ∀{Γ}{A}{B} → Γ ∋ B → (A ∷ Γ) ∋ B

For each variable, we track whether it has been used "now" or not. So
we define `Time` as follows. The `Later` constructor does double duty
to mean a predicate has either been used "later" or not at all.

    data Time : Set where
      Now : Time
      Later : Time

The following defines a list of times, one for each variable in `Γ`.

    data Times : Context → Set₁ where
      ∅ : Times []
      cons : ∀{Γ}{A} → Time → Times Γ → Times (A ∷ Γ)

The `Setˢ` type is a record indexed by the type of the environment and
by the time for each variable. The representation of `Setˢ` (the `#`
field) is a function that maps an environment of predicates
(one predicate for each in-scope μ) to a `Setᵒ`.

    record Setˢ (Γ : Context) (ts : Times Γ) : Set₁ where
      field
        # : RecEnv Γ → Setᵒ 
        ...
    open Setˢ public

We define variants of all the propositional connectives to work on
Setˢ.

The "later" operator `▷ˢ` asserts that `P` is true in the future, so the
predicate `▷ˢ P` can safely say that any use of recursive predicate in
`P` happens `Later`.

    laters : ∀ (Γ : Context) → Times Γ
    laters [] = ∅
    laters (A ∷ Γ) = cons Later (laters Γ)

    ▷ˢ : ∀{Γ}{ts : Times Γ}
       → Setˢ Γ ts
         -----------------
       → Setˢ Γ (laters Γ)

The "and" operator, `P ×ˢ Q` is categorized as `Later` for a variable
only if both `P` and `Q` are `Later` for that variable. Otherwise it
is `Now`.  We use the following function to make this choice:

    choose : Kind → Kind → Kind
    choose Now Now = Now
    choose Now Later = Now
    choose Later Now = Now
    choose Later Later = Later

We define `combine` to apply `choose` to a list of times.

    combine : ∀{Γ} (ts₁ ts₂ : Times Γ) → Times Γ
    combine {[]} ts₁ ts₂ = ∅
    combine {A ∷ Γ} (cons x ts₁) (cons y ts₂) =
        cons (choose x y) (combine ts₁ ts₂)

Here's the type of the "and" operator:

    _×ˢ_ : ∀{Γ}{ts₁ ts₂ : Times Γ} → Setˢ Γ ts₁ → Setˢ Γ ts₂
       → Setˢ Γ (combine ts₁ ts₂)

The other propositions follow a similar pattern.

The membership formula `a ∈ x` is true when `a` is in the predicate
bound to variable `x` in the environment. The time for `x` is required
to be `Now`.

    var-now : ∀ (Γ : Context) → ∀{A} → (x : Γ ∋ A) → Times Γ
    var-now (B ∷ Γ) zeroˢ = cons Now (laters Γ)
    var-now (B ∷ Γ) (sucˢ x) = cons Later (var-now Γ x)

    _∈_ : ∀{Γ}{A}
       → A
       → (x : Γ ∋ A)
       → Setˢ Γ (var-now Γ x)
    a ∈ x =
      record { # = λ δ → (lookup x δ) a
             ; ... }

The `μˢ` formula defines a (possibly nested) recursive predicate.

    μˢ : ∀{Γ}{ts : Times Γ}{A}
       → (A → Setˢ (A ∷ Γ) (cons Later ts))
         ----------------------------------
       → (A → Setˢ Γ ts)

It takes a non-recursive predicate from `A` to `Setˢ` and produces a
recursive predicate in `A`. Note that the variable `zeroˢ`, the
one introduced by this `μˢ`, is required to have time `Later`.

If the recursive predicate is not nested inside other recursive
predicates, then you can directly use the following `μᵒ` operator.

    μᵒ : ∀{A}
       → (A → Setˢ (A ∷ []) (cons Later ∅))
         ----------------------------------
       → (A → Setᵒ)

Let's revisit the example of defining multi-step reduction.  The
non-recursive `mreduce` predicate is defined as follows.

```
mreduce : Term × Term → Setˢ ((Term × Term) ∷ []) (cons Later ∅)
mreduce (M , N) = (M ≡ N)ˢ ⊎ˢ (∃ˢ[ L ] (M —→ L)ˢ ×ˢ ▷ˢ (((L , N) ∈ zeroˢ)))
```

Note that the `R` parameter has become implicit; it has moved into the
environment. Also the application `R (L , N)` is replaced by
`▷ˢ ((L , N) ∈ zeroˢ)`, where the de Bruijn index `zeroˢ` refers to
the predicate `R` in the environment.

We define the recursive predicate `M —→* N` by applying `μᵒ`
to `mreduce`.

```
infix 2 _—→*_
_—→*_ : Term → Term → Setᵒ
M —→* N = μᵒ mreduce (M , N)
```

Here are a couple uses of the multi-step reduction relation.

```
X₀ : #($ (Num 0) —→* $ (Num 0)) 1
X₀ = inj₁ refl

X₁ : #((ƛ ($ (Num 1))) · $ (Num 0) —→* $ (Num 1)) 2
X₁ = inj₂ (_ , (β ($̬ _) , inj₁ refl))
```

## Proofs in Step-indexed Logic

Just like first-orderd logic, SIL comes with rules of deduction for
carrying out proofs. The judgement form is `𝒫 ⊢ᵒ P`, where `𝒫` is a
list of assumptions and `P` is a formula.  The judgement `𝒫 ⊢ᵒ P` is
true iff for every time `k`, all of `𝒫` are true at `k` implies that `P`
is true at `k`. So in Agda we have the following definition.

    Πᵒ : List Setᵒ → Setᵒ
    Πᵒ [] = ⊤ᵒ
    Πᵒ (P ∷ 𝒫) = P ×ᵒ Πᵒ 𝒫 

    _⊢ᵒ_ : List Setᵒ → Setᵒ → Set
    𝒫 ⊢ᵒ P = ∀ k → # (Πᵒ 𝒫) k → # P k

Many of the deduction rules are the same as in first order logic.
For example, here are the introduction and elimination rules
for conjunction. We use the same notation as Agda, but with
a superscript "o".

    _,ᵒ_ : ∀{𝒫 : List Setᵒ }{P Q : Setᵒ}
      → 𝒫 ⊢ᵒ P
      → 𝒫 ⊢ᵒ Q
        ------------
      → 𝒫 ⊢ᵒ P ×ᵒ Q

    proj₁ᵒ : ∀{𝒫 : List Setᵒ }{P Q : Setᵒ}
      → 𝒫 ⊢ᵒ P ×ᵒ Q
        ------------
      → 𝒫 ⊢ᵒ P

    proj₂ᵒ : ∀{𝒫 : List Setᵒ }{P Q : Setᵒ}
      → 𝒫 ⊢ᵒ P ×ᵒ Q
        ------------
      → 𝒫 ⊢ᵒ Q

The introduction rule for a constant formula `S ᵒ` is straightforward.
A proof of `S` in regular Agda is sufficient to build a proof of `S ᵒ`
in SIL.

    constᵒI : ∀{𝒫}{S : Set}
       → S
       → 𝒫 ⊢ᵒ S ᵒ

On the other hand, given a proof of `S ᵒ` in SIL, one cannot obtain a
proof of `S` directly in Agda. That is, the following rule is invalid
because `𝒫` could be false at every index.

    bogus-constᵒE : ∀ {𝒫}{S : Set}{R : Setᵒ}
       → 𝒫 ⊢ᵒ S ᵒ
       → S

Instead, we have an elimination rule in continuation-passing style.
That is, if we have a proof of `S ᵒ` and need to prove some arbitrary
goal `R`, then it suffices to prove `R` under the assumption that `S`
is true.

    constᵒE : ∀ {𝒫}{S : Set}{R : Setᵒ}
       → 𝒫 ⊢ᵒ S ᵒ
       → (S → 𝒫 ⊢ᵒ R)
       → 𝒫 ⊢ᵒ R

Analogous to `subst` in Agda's standard library, SIL has `substᵒ`
which says that if `P` and `Q` are equivalent, then a proof of `P` gives
a proof of `Q`.

    substᵒ : ∀{𝒫}{P Q : Setᵒ}
      → P ≡ᵒ Q
        -------------------
      → 𝒫 ⊢ᵒ P  →  𝒫 ⊢ᵒ Q

The deduction rules also include ones for the "later" operator.  As we
mentioned earlier, if a proposition is true now it will also be true
later.

    monoᵒ : ∀ {𝒫}{P}
       → 𝒫 ⊢ᵒ P
         -----------
       → 𝒫 ⊢ᵒ  ▷ᵒ P

One can transport induction on natural numbers into SIL to obtain the
following Löb rule, which states that when proving any property `P`,
one is allowed to assume that `P` is true later.

    lobᵒ : ∀ {𝒫}{P}
       → (▷ᵒ P) ∷ 𝒫 ⊢ᵒ P
         -----------------------
       → 𝒫 ⊢ᵒ P

For comparison, here's induction on natural numbers

      P 0
    → (∀ k → P k → P (suc k))
    → ∀ n → P n

In the world of SIL, propositions are always true at zero, so the base
case `P 0` is not necessary. The induction step `(∀ k → P k → P (suc k))`
is similar to the premise `(▷ᵒ P) ∷ 𝒫 ⊢ᵒ P` because `▷ᵒ` subtracts one.

The following is a handy proof rule that turns a proof of `P` in SIL
into an assumption in Agda that `P` is true for some positive natural
number.

    ⊢ᵒ-sucP : ∀{𝒫}{P Q : Setᵒ}
       → 𝒫 ⊢ᵒ P
       → (∀{n} → # P (suc n) → 𝒫 ⊢ᵒ Q)
       → 𝒫 ⊢ᵒ Q

As usual for temporal logics (or more generally, for modal logics),
there are distribution rules that push "later" through the other
logical connectives. For example, the following rule distributes
"later" through conjunction.

    ▷× : ∀{𝒫} {P Q : Setᵒ}
       → 𝒫 ⊢ᵒ (▷ᵒ (P ×ᵒ Q))
         ----------------------
       → 𝒫 ⊢ᵒ (▷ᵒ P) ×ᵒ (▷ᵒ Q)
