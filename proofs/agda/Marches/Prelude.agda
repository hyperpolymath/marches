{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-
  Marches — the little logic the Agda development needs.

  No standard library: the import cone is this repository plus the
  modules Agda ships (Agda.Primitive, Agda.Builtin.*), in step with the
  Lean development, which uses core Lean and no Mathlib. Every
  definition here is the textbook one.
-}
module Marches.Prelude where

open import Agda.Builtin.Equality public using (_≡_; refl)
open import Agda.Builtin.List     public using (List; []; _∷_)

infix  3 ¬_
infixr 1 _⊎_

-- The empty type, and negation as a map into it.
data ⊥ : Set where

¬_ : Set → Set
¬ P = P → ⊥

-- Disjunction (Lean's `Or`).
data _⊎_ (P Q : Set) : Set where
  inj₁ : P → P ⊎ Q
  inj₂ : Q → P ⊎ Q

sym : {X : Set} {x y : X} → x ≡ y → y ≡ x
sym refl = refl

subst : {X : Set} (P : X → Set) {x y : X} → x ≡ y → P x → P y
subst P refl px = px

⊥-elim : {X : Set} → ⊥ → X
⊥-elim ()

-- Natural numbers and their order, defined as Lean's core library defines
-- them: `Nat.le` has the constructors `refl : n ≤ n` and
-- `step : n ≤ m → n ≤ m + 1`, and `n < m` is `n + 1 ≤ m`.
open import Agda.Builtin.Nat public using (zero; suc) renaming (Nat to ℕ)

infix 4 _≤_ _<_

data _≤_ (n : ℕ) : ℕ → Set where
  refl : n ≤ n
  step : ∀ {m} → n ≤ m → n ≤ suc m

_<_ : ℕ → ℕ → Set
n < m = suc n ≤ m

-- Inequality (Lean's `≠`: `a ≠ b` is `a = b → False`).
infix 4 _≢_
_≢_ : {X : Set} → X → X → Set
x ≢ y = ¬ (x ≡ y)

-- Dependent pairs, the counterpart of Lean's `∃` (residual R1: Lean's `∃`
-- is a `Prop`, this is a type with its witness inside).
infixr 4 _,_
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

∃ : {A : Set} → (A → Set) → Set
∃ {A} B = Σ A B

-- Logical equivalence, with Lean's field names for `Iff`.
infix 3 _↔_
record _↔_ (P Q : Set) : Set where
  constructor mk↔
  field
    mp  : P → Q
    mpr : Q → P

open _↔_ public

↔-sym : {P Q : Set} → P ↔ Q → Q ↔ P
↔-sym e = mk↔ (mpr e) (mp e)

↔-trans : {P Q R : Set} → P ↔ Q → Q ↔ R → P ↔ R
↔-trans e f = mk↔ (λ x → mp f (mp e x)) (λ z → mpr e (mpr f z))

-- Non-dependent pairs (Lean's `Prod`, with `.1` and `.2` as `proj₁` and
-- `proj₂`).
infixr 2 _×_
_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

-- The order is transitive (Lean's `Nat.le_trans`), by induction on the
-- second proof, as `Nat.le` is defined.
≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
≤-trans p refl     = p
≤-trans p (step q) = step (≤-trans p q)
