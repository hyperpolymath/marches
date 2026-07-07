/-
  Marches — n regions and reassembly (rung 2).

  A `Discipline` abstracts the invariant every Marches system shares: a
  strict preference order and a typed step judgment whose every step
  strictly worsens. The worsening OBLIGATION is a field — a Discipline is
  a system in which that obligation is ALREADY discharged. Loop-freedom
  is then proven ONCE, generically (`Discipline.no_loop`).

  The kernel is an instance (`PathAlgebra.toDiscipline`). The headline is
  closure under composition: a finite ACYCLIC DAG of disciplines is
  itself a discipline (`DiscSys.compose`). The composite worsening
  obligation is discharged purely from the componentwise ones plus
  acyclicity of the DAG — no global re-proof. That is the
  by-construction counterpart of Kirigami's cut soundness (see
  LIMITATIONS.adoc), and because `compose` returns a `Discipline`, a
  composite may itself be a region of a larger system: reassembly is
  closure, not a one-shot.

  Delimitation unchanged: loop-freedom of the typed judgment is NOT
  protocol convergence. Mechanised convergence for policy-rich routing
  is agda-routing's ground (Daggitt–Griffin); see LIMITATIONS.adoc.
-/

import Marches.Basic
import Marches.Kernel
import Marches.Digraph
import Marches.Tropical

namespace Marches

/-- A routing discipline: positions with a strict preference order and a
    typed step judgment whose every step strictly worsens. `step_worsens`
    is the discharged obligation; composition must preserve exactly it. -/
structure Discipline where
  Pos : Type
  Lab : Type
  Better : Pos → Pos → Prop
  Step : Lab → Pos → Pos → Prop
  btrans : ∀ {p q r : Pos}, Better p q → Better q r → Better p r
  birrefl : ∀ p : Pos, ¬ Better p p
  step_worsens : ∀ {l : Lab} {p q : Pos}, Step l p q → Better p q

namespace Discipline

/-- Well-typed traces of a discipline. -/
inductive Trace (D : Discipline) : D.Pos → List D.Lab → D.Pos → Prop where
  | nil  {p : D.Pos} : Trace D p [] p
  | cons {p q r : D.Pos} {l : D.Lab} {ls : List D.Lab} :
      D.Step l p q → Trace D q ls r → Trace D p (l :: ls) r

/-- A well-typed trace worsens-or-stays. -/
theorem trace_ge (D : Discipline) :
    ∀ {p : D.Pos} {ls : List D.Lab} {q : D.Pos},
      Trace D p ls q → D.Better p q ∨ p = q := by
  intro p ls q ht
  induction ht with
  | nil => exact Or.inr rfl
  | cons hs _ ih =>
    have h1 := D.step_worsens hs
    cases ih with
    | inl h2 => exact Or.inl (D.btrans h1 h2)
    | inr he => exact Or.inl (he ▸ h1)

/-- Every well-typed NON-EMPTY trace strictly worsens. -/
theorem trace_worsens (D : Discipline) {p q : D.Pos} {l : D.Lab}
    {ls : List D.Lab} (ht : Trace D p (l :: ls) q) : D.Better p q := by
  cases ht with
  | cons hs ht' =>
    have h1 := D.step_worsens hs
    cases trace_ge D ht' with
    | inl h2 => exact D.btrans h1 h2
    | inr he => exact he ▸ h1

/-- Loop-freedom, once and for all: a well-typed trace returning to its
    start is empty. -/
theorem no_loop (D : Discipline) {p : D.Pos} {ls : List D.Lab}
    (ht : Trace D p ls p) : ls = [] := by
  cases ls with
  | nil => rfl
  | cons _ _ => exact absurd (trace_worsens D ht) (D.birrefl p)

end Discipline

/-- Every strictly inflationary path algebra IS a discipline; the
    strictness hypothesis is consumed here, explicitly. -/
def PathAlgebra.toDiscipline (A : PathAlgebra) (h : StrictlyInflationary A) :
    Discipline where
  Pos := A.Carrier
  Lab := A.Label
  Better := A.better
  Step := fun l p q => q = A.ext l p
  btrans := A.trans
  birrefl := A.irrefl
  step_worsens := by intro l p q hq; subst hq; exact h l p

/-- Sanity: the single-region kernel loop-freedom is recovered as an
    instance of the generic discipline theorem. -/
theorem toDiscipline_no_loop (A : PathAlgebra) (h : StrictlyInflationary A)
    {a : A.Carrier} {ls : List A.Label}
    (ht : Discipline.Trace (A.toDiscipline h) a ls a) : ls = [] :=
  Discipline.no_loop _ ht

/-! ### The region DAG -/

/-- A finite DAG of disciplines: an index type `R` of regions, an edge
    relation `E`, a discipline per region, and a crossing map along each
    edge. (Order-preservation of the crossing maps is NOT required —
    see `Compose.Interface`.) -/
structure DiscSys where
  R : Type
  E : R → R → Prop
  D : R → Discipline
  τ : ∀ {r r' : R}, E r r' → (D r).Pos → (D r').Pos

namespace DiscSys

variable (S : DiscSys)

/-- Composite position: a local position tagged by its region. -/
abbrev Pos := Σ r : S.R, (S.D r).Pos

/-- Stratified composite preference: local within a region; across
    regions, anything strictly upstream in the DAG beats anything
    downstream. The cross-region order is DAG reachability — so the
    composite order is strict exactly when the DAG is `Acyclic`. -/
inductive Better : S.Pos → S.Pos → Prop where
  | loc {r : S.R} {x y : (S.D r).Pos} :
      (S.D r).Better x y → Better ⟨r, x⟩ ⟨r, y⟩
  | cross {r r' : S.R} {x : (S.D r).Pos} {y : (S.D r').Pos} :
      RPath S.E r r' → Better ⟨r, x⟩ ⟨r', y⟩

/-- Composite labels: a region's own label, or a crossing along an edge. -/
inductive Lab where
  | loc   : (r : S.R) → (S.D r).Lab → Lab
  | cross : (r r' : S.R) → S.E r r' → Lab

/-- One well-typed composite step. -/
inductive Step : S.Lab → S.Pos → S.Pos → Prop where
  | sloc {r : S.R} {l : (S.D r).Lab} {x y : (S.D r).Pos} :
      (S.D r).Step l x y → Step (.loc r l) ⟨r, x⟩ ⟨r, y⟩
  | scross {r r' : S.R} (e : S.E r r') {x : (S.D r).Pos} :
      Step (.cross r r' e) ⟨r, x⟩ ⟨r', S.τ e x⟩

/-- Composite preference is transitive (uses `RPath.trans`; no acyclicity
    needed). -/
theorem btrans : ∀ {p q r : S.Pos}, S.Better p q → S.Better q r → S.Better p r := by
  intro p q r h1 h2
  cases h1 with
  | loc a =>
    cases h2 with
    | loc b => exact .loc ((S.D _).btrans a b)
    | cross e => exact .cross e
  | cross e1 =>
    cases h2 with
    | loc _ => exact .cross e1
    | cross e2 => exact .cross (e1.trans e2)

/-- Composite preference is irreflexive EXACTLY because the DAG is
    acyclic — this is the honest n-region home of the assumption. -/
theorem birrefl (hacyc : Acyclic S.E) : ∀ p : S.Pos, ¬ S.Better p p := by
  rintro ⟨r, x⟩ h
  cases h with
  | loc a => exact (S.D r).birrefl x a
  | cross e => exact hacyc r e

/-- Every well-typed composite step strictly worsens — discharged from
    the componentwise obligations (`sloc`) and DAG stratification
    (`scross`), with no global re-proof. Crossing maps are unconstrained. -/
theorem cstep_worsens : ∀ {l : S.Lab} {p q : S.Pos}, S.Step l p q → S.Better p q := by
  intro l p q h
  cases h with
  | sloc hs => exact .loc ((S.D _).step_worsens hs)
  | scross e => exact .cross (.single e)

/-! ### Negative theorems: the ill-typed n-region moves are underivable -/

/-- A region's own label cannot fire from a different region. -/
theorem no_foreign_local {r r' : S.R} (hne : r ≠ r')
    {l : (S.D r).Lab} {x : (S.D r').Pos} {q : S.Pos} :
    ¬ S.Step (.loc r l) ⟨r', x⟩ q := by
  intro h
  cases h with
  | sloc _ => exact hne rfl

/-- Under acyclicity, no region crosses to itself: a self-edge is
    unconstructible (any `e : E r r` refutes the hypothesis). -/
theorem no_self_cross (hacyc : Acyclic S.E) {r : S.R} (e : S.E r r) : False :=
  hacyc r (.single e)

/-- THE reassembly theorem: a finite acyclic DAG of disciplines is itself
    a discipline. Because the result has exactly the type `DiscSys.D`
    consumes, composites nest — reassembly is closure under composition,
    the by-construction counterpart of Kirigami cut soundness. -/
def compose (hacyc : Acyclic S.E) : Discipline where
  Pos := S.Pos
  Lab := S.Lab
  Better := S.Better
  Step := S.Step
  btrans := S.btrans
  birrefl := S.birrefl hacyc
  step_worsens := S.cstep_worsens

/-- Composite loop-freedom, as a corollary of the generic theorem: no
    well-typed n-region trace returns to its start (given an acyclic
    DAG). Not a convergence result — agda-routing owns that ground. -/
theorem compose_no_loop (hacyc : Acyclic S.E)
    {p : (S.compose hacyc).Pos} {ls : List (S.compose hacyc).Lab}
    (ht : Discipline.Trace (S.compose hacyc) p ls p) : ls = [] :=
  Discipline.no_loop _ ht

end DiscSys

/-! ### Concrete exhibit + reassembly demonstration -/

namespace Reassembly

/-- The "up" edge on `Bool`: `false → true`, nothing else. A minimal
    acyclic DAG shape. -/
def boolUp : Bool → Bool → Prop := fun a b => a = false ∧ b = true

/-- Every `boolUp` path runs `false → true`, and no further. -/
theorem boolUp_path : ∀ {a b : Bool}, RPath boolUp a b → a = false ∧ b = true := by
  intro a b h
  induction h with
  | single e => exact e
  | cons e _ ih =>
    obtain ⟨_, hm⟩ := e
    obtain ⟨hm', _⟩ := ih
    rw [hm] at hm'
    exact absurd hm' (by decide)

theorem boolUp_acyclic : Acyclic boolUp := by
  intro v h
  obtain ⟨hf, ht⟩ := boolUp_path h
  rw [hf] at ht
  exact absurd ht (by decide)

/-- A concrete two-region system: two tropical regions joined by a single
    DAG edge, crossing by identity on costs. -/
def twoTropical : DiscSys where
  R := Bool
  E := boolUp
  D := fun _ => TropicalNat.toDiscipline tropical_strict
  τ := fun _ x => x

/-- The composite is a discipline — its loop-freedom is `no_loop`. -/
def twoTropicalComposed : Discipline := twoTropical.compose boolUp_acyclic

/-- REASSEMBLY: a composite discipline used as a region inside another
    system. This elaborates and composes — closure under composition
    holds by construction, not by re-proof. -/
def nested : DiscSys where
  R := Bool
  E := boolUp
  D := fun _ => twoTropicalComposed
  τ := fun _ x => x

/-- A composite of composites: reassembly demonstrated concretely. -/
def nestedComposed : Discipline := nested.compose boolUp_acyclic

/-- Closure, stated at the type level: `compose`'s output has exactly the
    type a region slot expects, for any system and any acyclicity proof. -/
example (S : DiscSys) (h : Acyclic S.E) : Discipline := S.compose h

end Reassembly
end Marches
