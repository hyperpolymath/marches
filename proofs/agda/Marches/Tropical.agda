{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-
  Marches — Tropical instance (Agda source of `Marches/Tropical.lean`).

  The (min, +) shortest-path algebra as a strictly inflationary path
  algebra: signatures are ℕ costs, labels are edge weights, extension adds
  weight + 1 (positive weights ⇒ strictness). Read as a grade at a crossing
  (rung 3): alternatives keep the cheaper route, sequencing adds costs, and
  the unit of sequencing is cost 0. The two K-4 laws hold.

  `TropicalNat` is min-plus. It is not the max-plus `MaxPlus` of
  resource-algebra's M-2, and nothing here links to tropical-types (see
  `docs/kcut-correspondence.adoc`, KC-7 and KC-8). The grade's order `altLe`
  is marches' own; it is NOT resource-algebra's Agda `_≼_`.
-}
module Marches.Tropical where

open import Marches.Prelude
open import Marches.Basic
open import Marches.Kernel

TropicalNat : PathAlgebra
TropicalNat = record
  { Carrier = ℕ
  ; Label   = ℕ
  ; better  = _<_
  ; ext     = λ w a → a + (w + 1)
  ; trans   = <-trans
  ; irrefl  = <-irrefl
  }

tropical-strict : StrictlyInflationary TropicalNat
tropical-strict w a = ≤-suc (≤-add-right a w)

-- The kernel theorem, instantiated: no non-empty word of positive weights
-- returns a cost to itself.
tropical-no-return : (l : ℕ) (ls : List ℕ) (a : ℕ) → run TropicalNat (l ∷ ls) a ≢ a
tropical-no-return l ls a = no-return TropicalNat tropical-strict l ls a

-- The grade at a crossing (Lean namespace `Marches.TropicalGrade`).
module TropicalGrade where

  -- Alternatives (⊕): keep the cheaper of two routes.
  alt : ℕ → ℕ → ℕ
  alt a b = min a b

  -- Sequencing (⊗): costs add along a path.
  seq : ℕ → ℕ → ℕ
  seq a b = a + b

  -- The unit of sequencing (𝟙): the cost of the empty word.
  one : ℕ
  one = 0

  -- K-4, first law: 𝟙 ⊗ x ≡ x (Lean's `Nat.zero_add`).
  seq-unitl : (x : ℕ) → seq one x ≡ x
  seq-unitl zero    = refl
  seq-unitl (suc x) = cong suc (seq-unitl x)

  -- K-4, second law: x ⊕ x ≡ x.
  alt-idem : (x : ℕ) → alt x x ≡ x
  alt-idem x with x ≤ᵇ x
  ... | true  = refl
  ... | false = refl

  -- Extension is sequencing with the label's cost w + 1.
  ext-eq-seq : (w a : ℕ) → ext TropicalNat w a ≡ seq a (w + 1)
  ext-eq-seq w a = refl

  -- The unit belongs to the empty word only: no label costs 𝟙.
  label-cost-ne-one : (w : ℕ) → w + 1 ≢ one
  label-cost-ne-one w ()

  -- `alt` selects the `better` route.
  alt-of-better : ∀ {a b} → better TropicalNat a b → alt a b ≡ a
  alt-of-better {a} {b} h with a ≤ᵇ b | ≤→≤ᵇ (≤-of-< h)
  ... | true  | _  = refl
  ... | false | ()

  -- The order `alt` induces: `a ≼ b` when `b` absorbs `a`.
  altLe : ℕ → ℕ → Set
  altLe a b = alt a b ≡ b

  -- S-3 inside marches: `better` runs WITH cost, `altLe` runs AGAINST it.
  better-reverses-altLe : ∀ {a b} → better TropicalNat a b → altLe b a
  better-reverses-altLe {a} {b} h with b ≤ᵇ a in eq
  ... | true  = ⊥-elim (<-irrefl a (≤-trans h (≤ᵇ→≤ b a eq)))
  ... | false = refl

  -- 𝟙 is the TOP of `altLe`.
  altLe-one : ∀ (x : ℕ) → altLe x one
  altLe-one zero    = refl
  altLe-one (suc x) = refl

  -- Computed witness, the same numbers as resource-algebra's S-3.
  s3-witness : better TropicalNat 1 2 × altLe 2 1
  s3-witness = refl , refl
