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
