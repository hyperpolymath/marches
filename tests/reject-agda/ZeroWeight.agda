{-# OPTIONS --safe --without-K --cubical-compatible #-}
-- Expected rejection: `TropicalNat` adds `w + 1`, not `w`, and the `+ 1` is
-- what makes it strict. With a zero-weight extension a cost does not grow:
-- claiming `0 < 0 + 0` must be refused. This pins that the positive weight
-- in `Marches.Tropical.TropicalNat` is load-bearing for `tropical-strict`.
-- expect: 1 != 0 of type ℕ
module ZeroWeight where

open import Marches.Prelude

zero-weight-strict : 0 < 0 + 0
zero-weight-strict = refl
