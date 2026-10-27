/-
  Marches — the estate's tropical proofs, imported (rung 3d).

  `TropicalAdapterPath` is hyperpolymath/tropical-types' fully proved
  min-max ("bottleneck") transport semiring, required in `lakefile.toml`
  at a pinned commit and imported here UNPARAPHRASED: nothing below
  re-states or re-proves its contents. This file only connects it to
  marches' own machinery, through upstream's own theorems.

    • TropicalAdapter.bottleneck     : upstream's `⊗` (`tcMul` = max, unit
                                       `tcOne` = 0) is a marches `Grade`; all
                                       three laws are upstream's.
    • TropicalAdapter.pathCost_eq_accum : upstream's `pathCost` IS marches'
                                       `Grade.accum` of transport grades
                                       under `bottleneck`.
    • TropicalAdapter.carried_floor  : every step on a path floors the grade
                                       the path carries (upstream's
                                       `hub_ceiling`, read as provenance).
    • TropicalAdapter.bottleneck_carries_unit : a NON-empty path can carry
                                       the unit `𝟙` (one Concorde step). So
                                       `bottleneck`, unlike `TropicalGrade`,
                                       is not strictly inflationary as a
                                       grade: `carried_cons_ne_one` has no
                                       analogue, and no loop-freedom follows
                                       from it (the F2 lesson, again).

  The min-max semiring is neither marches' `TropicalNat` (min-plus) nor
  M-2's max-plus; see docs/kcut-correspondence.adoc (KC-13). Delimitation
  unchanged: nothing here is protocol convergence (LIMITATIONS.adoc).
-/

import TropicalAdapterPath
import Marches.Provenance

namespace Marches
namespace TropicalAdapter

open Hyperpolymath.ProtocolSquisher.Tropical

/-- The bottleneck grade: upstream's min-max `⊗` as a marches `Grade`.
    Every law is an upstream theorem. -/
def bottleneck : Grade where
  G := Nat
  seq := tcMul
  one := tcOne
  seq_assoc := tcMul_assoc
  seq_unitl := tcMul_one_left
  seq_unitr := tcMul_one_right

/-- Upstream's path cost is marches' accumulation: the bottleneck grade a
    path of transport steps carries. -/
theorem pathCost_eq_accum : ∀ p : AdapterPath, pathCost p = bottleneck.accum grade p
  | [] => rfl
  | c :: cs =>
    (pathCost_cons c cs).trans (congrArg (Nat.max (grade c)) (pathCost_eq_accum cs))

/-- Upstream's `pathCost_append`, recovered from marches' `accum_append`:
    the two developments agree on concatenation. -/
theorem pathCost_append_via_accum (p q : AdapterPath) :
    pathCost (p ++ q) = tcMul (pathCost p) (pathCost q) := by
  rw [pathCost_eq_accum, pathCost_eq_accum, pathCost_eq_accum]
  exact bottleneck.accum_append grade p q

/-- Every step on a path floors the grade the path carries: upstream's
    `hub_ceiling`, read as provenance. -/
theorem carried_floor (e : TransportClass) (p : AdapterPath) (h : e ∈ p) :
    grade e ≤ bottleneck.accum grade p :=
  pathCost_eq_accum p ▸ hub_ceiling e p h

/-- A non-empty path can carry the unit: one Concorde step carries `𝟙`.
    Contrast `TropicalGrade.carried_cons_ne_one`. -/
theorem bottleneck_carries_unit :
    bottleneck.accum grade [TransportClass.Concorde] = bottleneck.one :=
  rfl

end TropicalAdapter
end Marches
