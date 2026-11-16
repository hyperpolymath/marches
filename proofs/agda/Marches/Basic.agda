{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-
  Marches — Basic definitions (Agda source of `Marches/Basic.lean`).

  A *path algebra*: route signatures with a strict preference order,
  policy labels, and an extension action (applying an arc's policy to
  a route). `better a b` reads "a is strictly preferred to b"
  (min-selection convention: lower is better).

  Everything here is a definition except `strict-implies-inflationary`.
  The statement comparison with the Lean file is in
  `docs/agda-lean-correspondence.adoc`.
-}
module Marches.Basic where

open import Marches.Prelude

record PathAlgebra : Set₁ where
  field
    Carrier : Set
    Label   : Set
    -- Strict preference: `better a b` means `a` strictly preferred to `b`.
    better  : Carrier → Carrier → Set
    -- Policy extension: apply arc label `l` to route signature `a`.
    ext     : Label → Carrier → Carrier
    trans   : ∀ {a b c} → better a b → better b c → better a c
    irrefl  : ∀ a → ¬ better a a

open PathAlgebra public

-- Sobrinho-style strictness: extension strictly worsens every route
-- (in Sobrinho's notation, a ≺ l ⊕ a).
StrictlyInflationary : PathAlgebra → Set
StrictlyInflationary A = ∀ (l : Label A) (a : Carrier A) → better A a (ext A l a)

-- Non-strict variant: extension never improves a route.
Inflationary : PathAlgebra → Set
Inflationary A = ∀ (l : Label A) (a : Carrier A) → ¬ better A (ext A l a) a

-- Run a word of labels left to right from a starting signature.
run : (A : PathAlgebra) → List (Label A) → Carrier A → Carrier A
run A []       a = a
run A (l ∷ ls) a = run A ls (ext A l a)

strict-implies-inflationary : (A : PathAlgebra) →
  StrictlyInflationary A → Inflationary A
strict-implies-inflationary A h l a hbad = irrefl A a (trans A (h l a) hbad)
