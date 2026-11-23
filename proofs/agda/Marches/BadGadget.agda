{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-
  Marches — Negative artifact: DISAGREE (Agda source of
  `Marches/BadGadget.lean`, namespace `Marches.Disagree`).

  The smallest classical non-convergent policy pair
  (Griffin–Shepherd–Wilfong's DISAGREE): two nodes, one destination, each
  strictly prefers the route THROUGH the other over its own direct route.
  Under synchronous update the system oscillates with period 2 forever.

  The pincer:
    • disagree-improves / disagree-not-inflationary : the DISAGREE table
      VIOLATES the Marches discipline (extension strictly improves).
    • disagree-two-cycle / disagree-moves : the synchronous dynamics
      genuinely oscillate (period-2 orbit, not a fixed point).

  State: `Bool × Bool`; component i is `true` iff node i is on the
  indirect route (via the other node).
-}
module Marches.BadGadget where

open import Marches.Prelude hiding (step)

-- Synchronous update of DISAGREE.
step : Bool × Bool → Bool × Bool
step s = not (proj₂ s) , not (proj₁ s)

-- The dynamics are a period-≤2 orbit from every state.
disagree-two-cycle : ∀ (s : Bool × Bool) → step (step s) ≡ s
disagree-two-cycle (false , false) = refl
disagree-two-cycle (false , true)  = refl
disagree-two-cycle (true  , false) = refl
disagree-two-cycle (true  , true)  = refl

-- From (direct, direct) the system genuinely moves: not a fixed point.
disagree-moves : step (false , false) ≢ (false , false)
disagree-moves ()

-- The oscillation from (direct, direct), the list the Lean file `#eval`s.
orbit : List (Bool × Bool)
orbit = (false , false) ∷ step (false , false) ∷ step (step (false , false))
      ∷ step (step (step (false , false))) ∷ []

-- The value that Lean's `#eval orbit` prints, as a theorem. Agda-only: the
-- Lean side has this as a TESTED `#eval`, not as a theorem.
orbit-value : orbit ≡ (false , false) ∷ (true , true) ∷ (false , false) ∷ (true , true) ∷ []
orbit-value = refl

-- One node's route signatures under DISAGREE preferences:
-- viaOther ≺ direct ≺ invalid (it PREFERS the indirect route).
data DRoute : Set where
  direct viaOther invalid : DRoute

drank : DRoute → ℕ
drank viaOther = 0
drank direct   = 1
drank invalid  = 2

-- Extension over the peer arc: hearing the other's direct route yields
-- the (preferred!) indirect route.
dext : DRoute → DRoute
dext direct   = viaOther
dext viaOther = invalid
dext invalid  = invalid

-- DISAGREE extension strictly IMPROVES on the witness.
disagree-improves : drank (dext direct) < drank direct
disagree-improves = refl

-- Hence DISAGREE is not even (non-strictly) inflationary.
disagree-not-inflationary : ¬ (∀ (r : DRoute) → ¬ (drank (dext r) < drank r))
disagree-not-inflationary h = h direct disagree-improves
