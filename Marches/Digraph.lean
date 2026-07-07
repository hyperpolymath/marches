/-
  Marches — Digraphs: paths and acyclicity (rung 2 foundation).

  The explicit acyclicity hypothesis, lifted out of the Gao–Rexford
  module so that BOTH the customer→provider hierarchy (rung 1,
  `GRHierarchy.lean`) and the region DAG (rung 2, `Reassembly.lean`)
  consume ONE definition. This is the point: "the customer→provider
  hierarchy is acyclic" and "the region DAG is acyclic" are literally
  the same notion, `Marches.Acyclic`.

  Acyclicity is never PROVEN here for any real structure; it is the
  hypothesis threaded, explicitly, through every conditional
  loop-freedom theorem in the estate. (Falsifier F5.)
-/

namespace Marches

/-- Non-empty paths in a relation `R`. -/
inductive RPath {V : Type} (R : V → V → Prop) : V → V → Prop where
  | single {u v : V} : R u v → RPath R u v
  | cons   {u v w : V} : R u v → RPath R v w → RPath R u w

namespace RPath

variable {V : Type} {R : V → V → Prop}

/-- Extend a path by one arc on the right. -/
theorem snoc : ∀ {u v w : V}, RPath R u v → R v w → RPath R u w := by
  intro u v w h
  induction h with
  | single h1 => intro h2; exact .cons h1 (.single h2)
  | cons h1 _ ih => intro h2; exact .cons h1 (ih h2)

/-- Paths concatenate. -/
theorem trans : ∀ {u v w : V}, RPath R u v → RPath R v w → RPath R u w := by
  intro u v w h
  induction h with
  | single h1 => intro p2; exact .cons h1 p2
  | cons h1 _ ih => intro p2; exact .cons h1 (ih p2)

/-- A path in the reversed relation reverses into a path proper. -/
theorem flip : ∀ {u v : V}, RPath (fun a b => R b a) u v → RPath R v u := by
  intro u v h
  induction h with
  | single h1 => exact .single h1
  | cons h1 _ ih => exact snoc ih h1

end RPath

/-- Acyclicity: no non-empty cycle. THE explicit hypothesis threaded
    through the estate's conditional loop-freedom theorems. Never proven
    here for any real structure — it is what a topology (or a region
    DAG) is ASSUMED to satisfy. -/
def Acyclic {V : Type} (R : V → V → Prop) : Prop := ∀ v : V, ¬ RPath R v v

end Marches
