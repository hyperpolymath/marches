{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-
  Marches — Kernel theorem, single region (Agda source of
  `Marches/Kernel.lean`).

  If a path algebra is strictly inflationary, then running any
  non-empty word of labels strictly worsens the starting signature;
  in particular no non-empty word can return to its start.
  This is the algebraic core of loop-freedom.
-}
module Marches.Kernel where

open import Marches.Prelude
open import Marches.Basic

-- Helper: running any word either strictly worsens or is the identity.
run-le : (A : PathAlgebra) → StrictlyInflationary A →
  ∀ (ls : List (Label A)) (a : Carrier A) →
  better A a (run A ls a) ⊎ run A ls a ≡ a
run-le A h []       a = inj₂ refl
run-le A h (l ∷ ls) a with run-le A h ls (ext A l a)
... | inj₁ w = inj₁ (trans A (h l a) w)
... | inj₂ e = inj₁ (subst (better A a) (sym e) (h l a))

-- Kernel theorem: a non-empty word strictly worsens.
run-worsens : (A : PathAlgebra) → StrictlyInflationary A →
  ∀ (l : Label A) (ls : List (Label A)) (a : Carrier A) →
  better A a (run A (l ∷ ls) a)
run-worsens A h l ls a with run-le A h ls (ext A l a)
... | inj₁ w = trans A (h l a) w
... | inj₂ e = subst (better A a) (sym e) (h l a)

-- No non-empty word returns to its start: loop-freedom.
no-return : (A : PathAlgebra) → StrictlyInflationary A →
  ∀ (l : Label A) (ls : List (Label A)) (a : Carrier A) →
  ¬ (run A (l ∷ ls) a ≡ a)
no-return A h l ls a he =
  irrefl A a (subst (better A a) he (run-worsens A h l ls a))
