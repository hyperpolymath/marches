{-# OPTIONS --safe --without-K --cubical-compatible #-}
-- Expected rejection: a provider-learned route re-exported upward over a
-- customer arc is ⊥, not a provider route. Claiming it survives as `p` must
-- be refused, which pins that `Marches.GaoRexford.valley-dies` is decided
-- by the table and is not true by accident of an equation that holds anyway.
-- expect: bot != p
module ValleySurvives where

open import Marches.Prelude
open import Marches.GaoRexford

valley-survives : gext fromCust (gext fromProv c) ≡ p
valley-survives = refl
