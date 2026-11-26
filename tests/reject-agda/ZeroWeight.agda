{-# OPTIONS --safe --without-K --cubical-compatible #-}
-- Expected rejection: under `TropicalNat`, extending a route over a label
-- of weight 0 still costs 1 more, because `ext w a = a + (w + 1)`. Claiming
-- that a zero-weight label leaves the cost unchanged must be refused, for the
-- reason below. If `TropicalNat.ext` ever lost its `+ 1` (became `a + w`),
-- the claim would hold by `refl`, so this fixture would no longer be refused
-- with that message, and the gate would fail. (Checked 2026-11-24 with the
-- `+ 1` removed: the gate fails, here first because `tropical-strict` no
-- longer checks.) So the control is tied to the definition itself.
-- expect: 1 != 0 of type ℕ
module ZeroWeight where

open import Marches.Prelude
open import Marches.Basic
open import Marches.Tropical

zero-weight-free : ext TropicalNat 0 0 ≡ 0
zero-weight-free = refl
