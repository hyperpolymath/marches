/-
  Marches — Tropical instance.

  The (min, +) shortest-path algebra as a strictly inflationary
  PathAlgebra: signatures are Nat costs, labels are edge weights,
  extension adds weight + 1 (positive weights ⇒ strictness).

  This file is the seam for integrating the estate's existing
  fully proved tropical work. `TropicalAdapterPath.lean` lives in
  hyperpolymath/tropical-types (lake package `tropical-resource-typing`),
  required in lakefile.toml at a pinned commit and imported unparaphrased
  by `Marches/TropicalAdapter.lean` (rung 3d). Nothing in THIS file
  depends on it: `TropicalNat` (min-plus) is not upstream's min-max
  transport semiring.

  The cross-prover bridge is resource-algebra's M-2 (pinned in scripts/fetch-siblings.sh):
  Agda `MaxPlus` vs tropical-types' Lean `CommSemiring Tropical`, OPEN,
  port-and-reprove, with no mechanical link. `TropicalNat` below is
  min-plus, not max-plus, so it is not one of M-2's two objects; see
  docs/kcut-correspondence.adoc (KC-7, KC-8).
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

/-! ### The grade at a crossing (rung 3)

  `TropicalNat` read as a (min, +) grade, in the path algebra's own terms:
  alternatives keep the cheaper route (`better` is `<`), sequencing adds
  costs, and the unit of sequencing is cost `0`, the grade of the empty
  word. choreographic-types (pinned in scripts/fetch-siblings.sh) records that K-CUT-LOSS
  uses exactly two laws, `𝟙 ⊗ x ≡ x` and `x ⊕ x ≡ x` (K-4, TESTED there
  by `scripts/minimal-laws.sh`). Both hold here. Whether this reading
  agrees with any Agda instance is a cross-prover question: ASSUMED,
  port-and-reprove (resource-algebra M-2 idiom). -/

namespace TropicalGrade

/-- Alternatives (`⊕`): keep the cheaper of two routes. -/
def alt (a b : Nat) : Nat := min a b

/-- Sequencing (`⊗`): costs add along a path. -/
def seq (a b : Nat) : Nat := a + b

/-- The unit of sequencing (`𝟙`): the cost of the empty word. -/
def one : Nat := 0

/-- K-4, first law: `𝟙 ⊗ x ≡ x`. -/
theorem seq_unitl (x : Nat) : seq one x = x := Nat.zero_add x

/-- K-4, second law: `x ⊕ x ≡ x`. -/
theorem alt_idem (x : Nat) : alt x x = x := ite_self x

/-- Extension is sequencing with the label's cost `w + 1`. -/
theorem ext_eq_seq (w a : Nat) : TropicalNat.ext w a = seq a (w + 1) := rfl

/-- The unit belongs to the empty word only: no label costs `𝟙`. This is
    strict inflation, read as a grade. -/
theorem label_cost_ne_one (w : Nat) : w + 1 ≠ one := fun h => Nat.noConfusion h

/-- `alt` selects the `better` route. -/
theorem alt_of_better {a b : Nat} (h : TropicalNat.better a b) : alt a b = a :=
  Nat.min_eq_left (Nat.le_of_lt h)

/-- The order `alt` induces, in resource-algebra's convention (read at
    cf9235c, 2026-10-14: `a ≼ b` when `b` absorbs `a`). It is defined here for
    marches' own grade; it is NOT the Agda `_≼_`, and no link between them is claimed. -/
def altLe (a b : Nat) : Prop := alt a b = b

/-- S-3 inside marches: `better` runs WITH cost, the induced order runs
    AGAINST it. A better route sits ABOVE a worse one in `altLe`, as in
    resource-algebra's Loss and opposite to its MaxPlus. Any K-CUT-WARRANT
    bound ported here must be checked for direction (W-4). -/
theorem better_reverses_altLe {a b : Nat} (h : TropicalNat.better a b) : altLe b a :=
  ite_eq_right (Nat.not_le_of_gt h)

/-- `𝟙` is the TOP of `altLe`: every grade is below it (as Loss's `fin 0`). -/
theorem altLe_one : ∀ x : Nat, altLe x one
  | 0 => rfl
  | _ + 1 => rfl

/-- Computed witness, the same numbers as resource-algebra's S-3:
    `1` is better than `2`, and `2 ≼ 1`. -/
theorem s3_witness : TropicalNat.better (1 : Nat) (2 : Nat) ∧ altLe 2 1 :=
  ⟨Nat.lt_succ_self 1, rfl⟩

end TropicalGrade

end Marches
