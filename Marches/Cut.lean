/-
  Marches — cuts of the region DAG (rung 3).

  A *cut* is a set of regions closed under DAG predecessors: if a region
  is in the cut, so is every region that can cross into it. Read along the
  causal order of announcements (a route is in a region before it crosses
  out), a cut is a frontier, and its regions are the prefix before that
  frontier. This is the classical downward-closure condition on a cut. It
  is NOT the party-indexed `Consistent` of choreographic-types, a merge
  condition at choices (see the correspondence table). Being a cut needs
  no acyclicity; *crossing* one does (`edge_crosses_past`).

  Headline theorems:
    • Cut.edge_crosses_past        : in an acyclic graph every edge r → r'
                                     leaves the principal cut ↓r.
    • Cut.path_back_crosses_no_cut : an edge on a cycle crosses NO cut —
                                     acyclicity is load-bearing.
    • DiscSys.trace_cross_crosses_cut : every crossing in a well-typed
                                     composite trace crosses a cut that
                                     holds the trace's start and not its end.
    • DiscSys.trace_mem_back       : a trace ending inside a cut was inside
                                     it all along (`trace_inside`: every
                                     label fired inside it).
    • DiscSys.no_reentry           : a trace that has left a cut never
                                     re-enters it — `no_back_cross`, lifted
                                     from one interface to every cut.
    • DiscSys.composeCut           : `compose` restricted to a cut prefix
                                     is a `Discipline` (prefix-closure). Its
                                     traces are exactly the composite traces
                                     that end in the prefix
                                     (`composeCut_trace_embed`,
                                     `composeCut_trace_reflect`).
    • trace_cross_crosses_cut      : the same, for the two-region
                                     `Interface` of `Compose.lean` (the
                                     2-node DAG `Reassembly.boolUp`).

  Provenance. choreographic-types (pinned in scripts/fetch-siblings.sh) proves the cut side
  for global choreographies in Agda: `Choreographic.Global.Cut`,
  `KCut.proj-cut`, `KCut.cut-projectable`. The relation between those
  names and these is a table, not a link (docs/kcut-correspondence.adoc).
  No row there is more than ASSUMED (port-and-reprove). Nothing in this
  file imports or re-declares the Agda definitions.

  Delimitation: prefix-closure and loop-freedom of the typed judgment are
  not protocol convergence; agda-routing owns that ground (LIMITATIONS.adoc).
-/

import Marches.Compose
import Marches.Digraph
import Marches.Reassembly

namespace Marches

/-- A cut of a region graph `E`: a set of regions closed under
    predecessors. Every region that can cross into the cut is in it. -/
structure Cut {R : Type} (E : R → R → Prop) where
  mem    : R → Prop
  closed : ∀ {r r' : R}, E r r' → mem r' → mem r

namespace Cut

variable {R : Type} {E : R → R → Prop}

/-- An edge `r → r'` crosses the cut `C` when it leaves it. -/
def Crosses (C : Cut E) (r r' : R) : Prop := C.mem r ∧ ¬ C.mem r'

/-- Closure lifts from edges to paths. -/
theorem closed_path (C : Cut E) :
    ∀ {r r' : R}, RPath E r r' → C.mem r' → C.mem r := by
  intro r r' h
  induction h with
  | single e => exact C.closed e
  | cons e _ ih => intro hm; exact C.closed e (ih hm)

/-- The principal cut below `r`: `r` and every region with a path to it. -/
def past (r : R) : Cut E where
  mem x := x = r ∨ RPath E x r
  closed := by
    intro x y e hy
    cases hy with
    | inl h => subst h; exact Or.inr (.single e)
    | inr p => exact Or.inr (.cons e p)

/-- In an acyclic graph every edge crosses the principal cut of its source:
    the source is inside, the target outside. -/
theorem edge_crosses_past (hacyc : Acyclic E) {r r' : R} (e : E r r') :
    (past (E := E) r).Crosses r r' := by
  refine ⟨Or.inl rfl, ?_⟩
  intro h
  cases h with
  | inl h => subst h; exact hacyc _ (.single e)
  | inr p => exact hacyc r (.cons e p)

/-- Negative: if `r'` reaches back to `r`, no cut separates them. So an edge
    `r → r'` on a cycle crosses no cut at all: without `Acyclic`,
    `edge_crosses_past` fails, and so does every theorem below that uses it. -/
theorem path_back_crosses_no_cut {r r' : R} (p : RPath E r' r) (C : Cut E) :
    ¬ C.Crosses r r' :=
  fun ⟨h, hn⟩ => hn (C.closed_path p h)

end Cut

/-! ### Traces of a discipline, split at a label -/

/-- A trace containing a label splits into a prefix, that step, and a suffix. -/
theorem Discipline.trace_split (D : Discipline) :
    ∀ {p : D.Pos} {ls : List D.Lab} {q : D.Pos}, Discipline.Trace D p ls q →
      ∀ {l : D.Lab}, l ∈ ls →
        ∃ ls₁ ls₂ m m', ls = ls₁ ++ l :: ls₂ ∧ Discipline.Trace D p ls₁ m ∧
          D.Step l m m' ∧ Discipline.Trace D m' ls₂ q := by
  intro p ls q ht
  induction ht with
  | nil => intro l hl; cases hl
  | @cons p q₀ _ l₀ ls hs ht' ih =>
    intro l hl
    cases hl with
    | head => exact ⟨[], ls, p, q₀, rfl, .nil, hs, ht'⟩
    | tail _ hl' =>
      obtain ⟨ls₁, ls₂, m, m', he, h₁, hm, h₂⟩ := ih hl'
      exact ⟨l₀ :: ls₁, ls₂, m, m', by rw [he]; rfl, .cons hs h₁, hm, h₂⟩

/-! ### Cuts of a composed region DAG -/

namespace DiscSys

variable (S : DiscSys)

/-- One composite step stays in its region or crosses one DAG edge. -/
theorem step_region :
    ∀ {l : S.Lab} {p q : S.Pos}, S.Step l p q → p.1 = q.1 ∨ S.E p.1 q.1 := by
  intro l p q h
  cases h with
  | sloc _ => exact Or.inl rfl
  | scross e => exact Or.inr e

/-- A crossing step leaves exactly the edge's source for its target. -/
theorem cross_step_regions {r r' : S.R} {e : S.E r r'} {m m' : S.Pos}
    (h : S.Step (.cross r r' e) m m') : m.1 = r ∧ m'.1 = r' := by
  cases h with
  | scross _ => exact ⟨rfl, rfl⟩

/-- A trace ends in its start region or downstream of it. -/
theorem trace_region (hacyc : Acyclic S.E) :
    ∀ {p : (S.compose hacyc).Pos} {ls : List (S.compose hacyc).Lab} {q : (S.compose hacyc).Pos},
      Discipline.Trace (S.compose hacyc) p ls q → p.1 = q.1 ∨ RPath S.E p.1 q.1 := by
  intro p ls q ht
  induction ht with
  | nil => exact Or.inl rfl
  | cons hs _ ih =>
    cases S.step_region hs with
    | inl h₁ =>
      cases ih with
      | inl h₂ => exact Or.inl (h₁.trans h₂)
      | inr p₂ => exact Or.inr (by rw [h₁]; exact p₂)
    | inr e =>
      cases ih with
      | inl h₂ => exact Or.inr (.single (by rw [← h₂]; exact e))
      | inr p₂ => exact Or.inr (.cons e p₂)

/-- PREFIX: a trace ending inside a cut started inside it. What happens
    after the frontier cannot reach back into the prefix. -/
theorem trace_mem_back (hacyc : Acyclic S.E) (C : Cut S.E)
    {p : (S.compose hacyc).Pos} {ls : List (S.compose hacyc).Lab} {q : (S.compose hacyc).Pos}
    (ht : Discipline.Trace (S.compose hacyc) p ls q) (hq : C.mem q.1) : C.mem p.1 := by
  cases S.trace_region hacyc ht with
  | inl h => rw [h]; exact hq
  | inr p => exact C.closed_path p hq

/-- `no_back_cross`, lifted from one interface to every cut of the DAG:
    a trace that starts outside a cut never enters it. -/
theorem no_reentry (hacyc : Acyclic S.E) (C : Cut S.E)
    {p : (S.compose hacyc).Pos} {ls : List (S.compose hacyc).Lab} {q : (S.compose hacyc).Pos}
    (ht : Discipline.Trace (S.compose hacyc) p ls q) (hp : ¬ C.mem p.1) :
    ¬ C.mem q.1 :=
  fun hq => hp (S.trace_mem_back hacyc C ht hq)

/-- A composite label lies inside a cut when it fires from a region of the
    cut and, if a crossing, lands in one. -/
def LabInside (C : Cut S.E) : S.Lab → Prop
  | .loc r _ => C.mem r
  | .cross r r' _ => C.mem r ∧ C.mem r'

/-- A trace ending inside a cut fires every one of its labels inside it. -/
theorem trace_inside (hacyc : Acyclic S.E) (C : Cut S.E) :
    ∀ {p : (S.compose hacyc).Pos} {ls : List (S.compose hacyc).Lab} {q : (S.compose hacyc).Pos},
      Discipline.Trace (S.compose hacyc) p ls q → C.mem q.1 →
        ∀ l ∈ ls, S.LabInside C l := by
  intro p ls q ht
  induction ht with
  | nil => intro _ l hl; cases hl
  | cons hs ht' ih =>
    intro hq l hl
    have hq₀ := S.trace_mem_back hacyc C ht' hq
    cases hl with
    | head =>
      cases hs with
      | sloc _ => exact hq₀
      | scross e => exact ⟨C.closed e hq₀, hq₀⟩
    | tail _ hl' => exact ih hq l hl'

/-- Every crossing in a well-typed composite trace crosses a cut — the
    principal cut of its source — which holds the trace's start and not its
    end: the trace leaves that cut at this step and never comes back. -/
theorem trace_cross_crosses_cut (hacyc : Acyclic S.E)
    {p : (S.compose hacyc).Pos} {ls : List (S.compose hacyc).Lab} {q : (S.compose hacyc).Pos}
    (ht : Discipline.Trace (S.compose hacyc) p ls q)
    {r r' : S.R} {e : S.E r r'} (hl : Lab.cross r r' e ∈ ls) :
    ∃ C : Cut S.E, C.Crosses r r' ∧ C.mem p.1 ∧ ¬ C.mem q.1 := by
  obtain ⟨_, _, m, m', _, h₁, hm, h₂⟩ := Discipline.trace_split _ ht hl
  obtain ⟨hmr, hmr'⟩ := S.cross_step_regions hm
  have hc := Cut.edge_crosses_past hacyc e
  refine ⟨Cut.past r, hc, ?_, ?_⟩
  · cases S.trace_region hacyc h₁ with
    | inl h => exact Or.inl (h.trans hmr)
    | inr p => exact Or.inr (by rw [← hmr]; exact p)
  · exact S.no_reentry hacyc (Cut.past r) h₂ (by rw [hmr']; exact hc.2)

/-! ### Prefix-closure: `compose` restricted to a cut is a discipline -/

/-- The system restricted to the regions of a cut. -/
def restrict (C : Cut S.E) : DiscSys where
  R := {r : S.R // C.mem r}
  E := fun a b => S.E a.1 b.1
  D := fun a => S.D a.1
  τ := fun e x => S.τ e x

/-- Paths in the restriction are paths in the system. -/
theorem restrict_path (C : Cut S.E) :
    ∀ {a b : (S.restrict C).R}, RPath (S.restrict C).E a b → RPath S.E a.1 b.1 := by
  intro a b h
  induction h with
  | single e => exact .single e
  | cons e _ ih => exact .cons e ih

/-- The restriction of an acyclic DAG is acyclic. -/
theorem restrict_acyclic (hacyc : Acyclic S.E) (C : Cut S.E) :
    Acyclic (S.restrict C).E :=
  fun a h => hacyc a.1 (S.restrict_path C h)

/-- PREFIX-CLOSURE: `compose` restricted to a cut prefix is a `Discipline`.
    Its loop-freedom is `Discipline.no_loop`, with no new proof. -/
def composeCut (hacyc : Acyclic S.E) (C : Cut S.E) : Discipline :=
  (S.restrict C).compose (S.restrict_acyclic hacyc C)

/-- Positions of the prefix, read as positions of the whole system. -/
def posEmb (C : Cut S.E) : (S.restrict C).Pos → S.Pos := fun p => ⟨p.1.1, p.2⟩

/-- Labels of the prefix, read as labels of the whole system. -/
def labEmb (C : Cut S.E) : (S.restrict C).Lab → S.Lab
  | .loc a l => .loc a.1 l
  | .cross a b e => .cross a.1 b.1 e

theorem step_embed (C : Cut S.E) :
    ∀ {l : (S.restrict C).Lab} {p q : (S.restrict C).Pos},
      (S.restrict C).Step l p q → S.Step (S.labEmb C l) (S.posEmb C p) (S.posEmb C q) := by
  intro l p q h
  cases h with
  | sloc hs => exact .sloc hs
  | @scross a b e _ => exact DiscSys.Step.scross (S := S) (r := a.1) (r' := b.1) e

/-- Every trace of the prefix is a trace of the whole composite. -/
theorem composeCut_trace_embed (hacyc : Acyclic S.E) (C : Cut S.E) :
    ∀ {p : (S.composeCut hacyc C).Pos} {ls : List (S.composeCut hacyc C).Lab}
      {q : (S.composeCut hacyc C).Pos},
      Discipline.Trace (S.composeCut hacyc C) p ls q →
        Discipline.Trace (S.compose hacyc) (S.posEmb C p) (ls.map (S.labEmb C))
          (S.posEmb C q) := by
  intro p ls q ht
  induction ht with
  | nil => exact .nil
  | cons hs _ ih => exact .cons (S.step_embed C hs) ih

/-- Conversely, every composite trace that starts and ends in the prefix is
    a trace of the prefix, label for label. -/
theorem composeCut_trace_reflect_of (hacyc : Acyclic S.E) (C : Cut S.E) :
    ∀ {p : (S.compose hacyc).Pos} {ls : List (S.compose hacyc).Lab} {q : (S.compose hacyc).Pos},
      Discipline.Trace (S.compose hacyc) p ls q →
        ∀ (hp : C.mem p.1) (hq : C.mem q.1),
          ∃ ls' : List (S.restrict C).Lab, ls'.map (S.labEmb C) = ls ∧
            Discipline.Trace (S.composeCut hacyc C) ⟨⟨p.1, hp⟩, p.2⟩ ls'
              ⟨⟨q.1, hq⟩, q.2⟩ := by
  intro p ls q ht
  induction ht with
  | nil => intro _ _; exact ⟨[], rfl, .nil⟩
  | cons hs ht' ih =>
    intro hp hq
    have hq₀ := S.trace_mem_back hacyc C ht' hq
    obtain ⟨ls', hmap, ht''⟩ := ih hq₀ hq
    cases hs with
    | sloc hl =>
      exact ⟨.loc ⟨_, hp⟩ _ :: ls', by rw [List.map_cons, hmap] <;> rfl,
        .cons (.sloc hl) ht''⟩
    | scross e =>
      exact ⟨.cross ⟨_, hp⟩ ⟨_, hq₀⟩ e :: ls', by rw [List.map_cons, hmap] <;> rfl,
        .cons (DiscSys.Step.scross (S := S.restrict C) (r := ⟨_, hp⟩) (r' := ⟨_, hq₀⟩) e)
          ht''⟩

/-- THE prefix-closure theorem: a composite trace that ENDS in a cut prefix
    is a trace of the prefix alone — whatever lies beyond the frontier is
    irrelevant to it. With `composeCut_trace_embed`, the prefix's traces
    are exactly the composite's traces that end in the prefix. -/
theorem composeCut_trace_reflect (hacyc : Acyclic S.E) (C : Cut S.E)
    {p : (S.compose hacyc).Pos} {ls : List (S.compose hacyc).Lab} {q : (S.compose hacyc).Pos}
    (ht : Discipline.Trace (S.compose hacyc) p ls q) (hq : C.mem q.1) :
    ∃ ls' : List (S.restrict C).Lab, ls'.map (S.labEmb C) = ls ∧
      Discipline.Trace (S.composeCut hacyc C)
        ⟨⟨p.1, S.trace_mem_back hacyc C ht hq⟩, p.2⟩ ls' ⟨⟨q.1, hq⟩, q.2⟩ :=
  S.composeCut_trace_reflect_of hacyc C ht _ hq

/-- The prefix has no well-typed loop: an instance of the generic theorem. -/
theorem composeCut_no_loop (hacyc : Acyclic S.E) (C : Cut S.E)
    {p : (S.composeCut hacyc C).Pos} {ls : List (S.composeCut hacyc C).Lab}
    (ht : Discipline.Trace (S.composeCut hacyc C) p ls p) : ls = [] :=
  Discipline.no_loop _ ht

end DiscSys

/-! ### The two-region interface of `Compose.lean` as a cut crossing

  The interface `A → B` is the single edge of the 2-node DAG
  `Reassembly.boolUp` (`false → true`); A is the region `false`, B is
  `true`. Its crossing leaves the principal cut `↓false` = the A side. -/

/-- The region of a two-region position: `false` for A, `true` for B. -/
def Pos.region {A B : PathAlgebra} : Pos A B → Bool
  | .inA _ => false
  | .inB _ => true

/-- The A side of the interface, as a cut of `boolUp`. -/
abbrev aSide : Cut Reassembly.boolUp := Cut.past false

/-- The interface crossing crosses the A-side cut. -/
theorem cross_crosses_aSide (A B : PathAlgebra) (I : Interface A B)
    {p q : Pos A B} (h : Step A B I .cross p q) :
    aSide.Crosses p.region q.region := by
  cases h with
  | cross => exact Cut.edge_crosses_past Reassembly.boolUp_acyclic ⟨rfl, rfl⟩

/-- A two-region trace containing a label splits at it. -/
theorem trace_split (A B : PathAlgebra) (I : Interface A B) :
    ∀ {p : Pos A B} {ls : List (CLabel A B)} {q : Pos A B}, Trace A B I p ls q →
      ∀ {l : CLabel A B}, l ∈ ls →
        ∃ ls₁ ls₂ m m', ls = ls₁ ++ l :: ls₂ ∧ Trace A B I p ls₁ m ∧
          Step A B I l m m' ∧ Trace A B I m' ls₂ q := by
  intro p ls q ht
  induction ht with
  | nil => intro l hl; cases hl
  | @cons p q₀ _ l₀ ls hs ht' ih =>
    intro l hl
    cases hl with
    | head => exact ⟨[], ls, p, q₀, rfl, .nil, hs, ht'⟩
    | tail _ hl' =>
      obtain ⟨ls₁, ls₂, m, m', he, h₁, hm, h₂⟩ := ih hl'
      exact ⟨l₀ :: ls₁, ls₂, m, m', by rw [he]; rfl, .cons hs h₁, hm, h₂⟩

/-- `no_back_cross`, lifted from one step to whole traces: a trace that
    starts in B ends in B. -/
theorem trace_stays_in_B (A B : PathAlgebra) (I : Interface A B) :
    ∀ {p : Pos A B} {ls : List (CLabel A B)} {q : Pos A B},
      Trace A B I p ls q → p.region = true → q.region = true := by
  intro p ls q ht
  induction ht with
  | nil => exact id
  | cons hs _ ih =>
    intro hp
    apply ih
    cases hs with
    | la => cases hp
    | lb => rfl
    | cross => cases hp

/-- Every interface crossing in a well-typed two-region trace crosses the
    A-side cut, which holds the trace's start and not its end. -/
theorem trace_cross_crosses_cut (A B : PathAlgebra) (I : Interface A B)
    {p q : Pos A B} {ls : List (CLabel A B)}
    (ht : Trace A B I p ls q) (hl : CLabel.cross ∈ ls) :
    aSide.Crosses false true ∧ aSide.mem p.region ∧ ¬ aSide.mem q.region := by
  obtain ⟨_, _, m, m', _, h₁, hm, h₂⟩ := trace_split A B I ht hl
  have hc :=
    Cut.edge_crosses_past Reassembly.boolUp_acyclic (r := false) (r' := true) ⟨rfl, rfl⟩
  refine ⟨hc, ?_, ?_⟩
  · cases hm with
    | cross =>
      cases hpr : p.region with
      | false => exact Or.inl rfl
      | true => exact absurd (trace_stays_in_B A B I h₁ hpr) (fun h => by cases h)
  · cases hm with
    | cross =>
      rw [trace_stays_in_B A B I h₂ rfl]
      exact hc.2

/-! ### Concrete exhibit: the theorems are not vacuous -/

namespace CutExhibit

open Reassembly

/-- The one edge of `boolUp`. -/
theorem e₀ : boolUp false true := ⟨rfl, rfl⟩

/-- A concrete trace of `twoTropical`: a hop of weight 2 in region `false`
    (cost 0 → 3), the crossing (identity on cost), a hop of weight 0 in
    region `true` (cost 3 → 4). -/
theorem trace₀ :
    Discipline.Trace (twoTropical.compose boolUp_acyclic) ⟨false, (0 : Nat)⟩
      [.loc false (2 : Nat), .cross false true e₀, .loc true (0 : Nat)] ⟨true, (4 : Nat)⟩ :=
  .cons (.sloc rfl) (.cons (.scross e₀) (.cons (.sloc rfl) .nil))

/-- Its crossing leaves a cut that holds the start region and not the end. -/
example : ∃ C : Cut boolUp, C.Crosses false true ∧ C.mem false ∧ ¬ C.mem true :=
  twoTropical.trace_cross_crosses_cut boolUp_acyclic trace₀ (.tail _ (.head _))

/-- The prefix of `trace₀` that stays in region `false` is a trace of the
    cut prefix `↓false` alone. -/
example : ∃ ls' : List (twoTropical.restrict (Cut.past false)).Lab,
    ls'.map (twoTropical.labEmb (Cut.past false)) = [.loc false (2 : Nat)] ∧
    Discipline.Trace (twoTropical.composeCut boolUp_acyclic (Cut.past false))
      ⟨⟨false, Or.inl rfl⟩, (0 : Nat)⟩ ls' ⟨⟨false, Or.inl rfl⟩, (3 : Nat)⟩ :=
  twoTropical.composeCut_trace_reflect_of boolUp_acyclic (Cut.past false)
    (.cons (.sloc rfl) .nil) (Or.inl rfl) (Or.inl rfl)

/-- Negative control: on a self-loop no cut is crossed. -/
example (C : Cut (fun _ _ : Unit => True)) : ¬ C.Crosses () () :=
  Cut.path_back_crosses_no_cut (.single trivial) C

end CutExhibit

end Marches
