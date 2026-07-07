/-
  Marches — Negative artifact: falsifier F2 discharged (rung 1).

  F2 (FALSIFIERS.adoc): "the composite theorem is vacuous —
  stratification (`ab`) does all the work and within-region strictness
  is decorative."

  Refutation by counterexample instance: `Freewheel`, the
  identity-extension algebra. It is (non-strictly) inflationary but
  NOT strictly inflationary — precisely the hypothesis `hA` that
  `wt_cycles_are_empty` demands. Over it, a well-typed NON-EMPTY
  returning trace exists (`f2_discharged`): drop `hA` and the
  conclusion of `wt_cycles_are_empty` is false. Hence `hA`/`hB` are
  load-bearing; stratification alone proves nothing about within-region
  loops.

  Everything here is PROVEN by `lake build`; no convergence claim is
  made or implied (that ground is agda-routing's — LIMITATIONS.adoc).
-/

import Marches.Basic
import Marches.Compose

namespace Marches
namespace F2

/-- The freewheel algebra: one signature, extension is the identity.
    A legal `PathAlgebra` (the strict order is empty), inflationary,
    but NOT strictly inflationary. -/
def Freewheel : PathAlgebra where
  Carrier := Unit
  Label   := Unit
  better  := fun _ _ => False
  ext     := fun _ a => a
  trans   := fun h _ => h.elim
  irrefl  := fun _ h => h

/-- Freewheel never improves a route: it satisfies the NON-strict
    discipline. -/
theorem freewheel_inflationary : Inflationary Freewheel :=
  fun _ _ h => h

/-- Freewheel is NOT strictly inflationary — the exact hypothesis the
    composite theorems consume. -/
theorem freewheel_not_strict : ¬ StrictlyInflationary Freewheel :=
  fun h => h () ()

/-- A typed interface Freewheel → Freewheel (strictness is vacuous:
    the order is empty). -/
def FreewheelInterface : Interface Freewheel Freewheel where
  τ := id
  strict := fun h => h.elim

/-- A well-typed, NON-EMPTY, returning trace: one within-region label
    fires and the state is unchanged. Well-typedness does not blink. -/
theorem returning_trace :
    Trace Freewheel Freewheel FreewheelInterface
      (.inA ()) [.la ()] (.inA ()) :=
  .cons .la .nil

/-- F2 DISCHARGED: without `hA`, `wt_cycles_are_empty` is false —
    here is a well-typed non-empty trace returning to its start.
    Within-region strictness is load-bearing; `ab` stratification is
    not decorative-proof on its own. -/
theorem f2_discharged :
    ∃ ls : List (CLabel Freewheel Freewheel),
      ls ≠ [] ∧
      Trace Freewheel Freewheel FreewheelInterface (.inA ()) ls (.inA ()) :=
  ⟨[.la ()], List.cons_ne_nil _ _, returning_trace⟩

end F2
end Marches
