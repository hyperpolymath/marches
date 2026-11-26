{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-
  Marches — Negative artifact: falsifier F2 discharged (Agda source of
  `Marches/Freewheel.lean`, namespace `Marches.F2`).

  F2: "the composite theorem is vacuous — stratification (`ab`) does all
  the work and within-region strictness is decorative." Refuted by the
  identity-extension algebra `Freewheel`: inflationary but NOT strictly
  inflationary, and over it a well-typed NON-EMPTY returning trace exists.
  So the strictness hypotheses of `wt-cycles-are-empty` are load-bearing.
-}
module Marches.Freewheel where

open import Marches.Prelude
open import Marches.Basic
open import Marches.Compose

-- The freewheel algebra: one signature, extension is the identity, the
-- strict order is empty.
Freewheel : PathAlgebra
Freewheel = record
  { Carrier = ⊤
  ; Label   = ⊤
  ; better  = λ _ _ → ⊥
  ; ext     = λ _ a → a
  ; trans   = λ h _ → h
  ; irrefl  = λ _ h → h
  }

-- Freewheel never improves a route: the NON-strict discipline holds.
freewheel-inflationary : Inflationary Freewheel
freewheel-inflationary _ _ h = h

-- Freewheel is NOT strictly inflationary.
freewheel-not-strict : ¬ StrictlyInflationary Freewheel
freewheel-not-strict h = h tt tt

-- A typed interface Freewheel → Freewheel.
FreewheelInterface : Interface Freewheel Freewheel
FreewheelInterface = record { τ = λ x → x }

-- A well-typed, NON-EMPTY, returning trace.
returning-trace : Trace Freewheel Freewheel FreewheelInterface (inA tt) (la tt ∷ []) (inA tt)
returning-trace = cons la nil

-- F2 DISCHARGED: without strictness, `wt-cycles-are-empty` is false.
f2-discharged : Σ (List (CLabel Freewheel Freewheel))
  (λ ls → (ls ≢ []) × Trace Freewheel Freewheel FreewheelInterface (inA tt) ls (inA tt))
f2-discharged = (la tt ∷ []) , ((λ ()) , returning-trace)
