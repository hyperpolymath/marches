/-
  Marches — Tropical instance.

  The (min, +) shortest-path algebra as a strictly inflationary
  PathAlgebra: signatures are Nat costs, labels are edge weights,
  extension adds weight + 1 (positive weights ⇒ strictness).

  This file is the seam for integrating the estate's existing
  fully proved tropical work (TropicalAdapterPath.lean in
  tropical-resource-typing). Status of that integration: OPEN
  (rung 3 in ROADMAP.adoc). Nothing here fabricates or depends on
  that file's contents.
-/

import Marches.Basic
import Marches.Kernel

namespace Marches

def TropicalNat : PathAlgebra where
  Carrier := Nat
  Label   := Nat
  better  := fun a b => a < b
  ext     := fun w a => a + (w + 1)
  trans   := fun h1 h2 => Nat.lt_trans h1 h2
  irrefl  := fun a => Nat.lt_irrefl a

theorem tropical_strict : StrictlyInflationary TropicalNat :=
  fun w a => Nat.lt_succ_of_le (Nat.le_add_right a w)

/-- The kernel theorem, instantiated: no non-empty word of positive
    weights returns a cost to itself. -/
theorem tropical_no_return (l : Nat) (ls : List Nat) (a : Nat) :
    run TropicalNat (l :: ls) a ≠ a :=
  no_return TropicalNat tropical_strict l ls a

end Marches
