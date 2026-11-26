{-# OPTIONS --safe --without-K --cubical-compatible #-}
-- Expected rejection: the discipline rejects DISAGREE. Claiming its
-- extension never improves a route, by refuting the witness at `direct`,
-- must be refused: `drank (dext direct) < drank direct` holds (`refl`).
-- This pins that `Marches.BadGadget.disagree-not-inflationary` is decided
-- by the table, not true by accident.
-- expect: are valid: refl
module DisagreeAccepted where

open import Marches.Prelude hiding (step)
open import Marches.BadGadget
import Marches.Prelude as P

accepted : ∀ (r : DRoute) → ¬ (drank (dext r) < drank r)
accepted direct   ()
accepted viaOther (P.step (P.step ()))
accepted invalid  (P.step ())
