{-# OPTIONS --safe --without-K --cubical-compatible #-}
-- Expected rejection: loop-freedom does not hold without strictness.
-- The free-wheeling algebra (one signature, one label, extension the
-- identity, no preference) is not strictly inflationary, and the one-label
-- word returns to its start. Claiming `no-return` for it must be refused;
-- this fixture shows the hypothesis of `Marches.Kernel.no-return` is
-- load-bearing (falsifier F2, `Marches/Freewheel.lean` on the Lean side).
-- expect: should be empty
module FreewheelReturns where

open import Marches.Prelude
open import Marches.Basic

freewheel : PathAlgebra
freewheel = record
  { Carrier = ⊤ ; Label = ⊤ ; better = λ _ _ → ⊥ ; ext = λ _ a → a
  ; trans = λ b _ → b ; irrefl = λ _ b → b }

returns-anyway : ¬ (run freewheel (tt ∷ []) tt ≡ tt)
returns-anyway ()
