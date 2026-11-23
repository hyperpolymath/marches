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
