/-
  Marches — path provenance as graded accumulation (rung 3e).

  `Cut.lean` answers WHERE a well-typed trace may go: every crossing
  crosses a cut, and a trace never re-enters a cut it has left. This file
  answers WHAT a trace carries. A word of labels accumulates a grade
  (`Grade.accum`: `𝟙` for the empty word, `⊗` along the word), and:

    • TropicalGrade.run_eq_seq_carried : in one tropical region the end
                                     signature is `start ⊗ carried(word)`.
                                     The signature IS the accumulated grade.
    • TropicalGrade.carried_cons_ne_one : a non-empty word carries a
                                     non-unit grade — strict inflation,
                                     read as provenance. `no_return` follows.
    • trace_cross_shape              : a well-typed two-region trace that
                                     crosses has one shape: an A-word from
                                     an A-start, the crossing, a B-word.
                                     Typing alone; no strictness needed.
    • Interface.fibre, Interface.carried : what crosses is the A-signature
                                     at the crossing; the B side sees it only
                                     through `τ`. The fibre of `τ` over the
                                     landing point is what was carried and
                                     cannot be seen from B.
    • DiscSys.carried_to_cross_in_past : in the region DAG, the grade that
                                     reaches a crossing `r → r'` was
                                     accumulated by a trace of the cut
                                     prefix `↓r` alone.
    • DiscSys.carried_in_cut         : the grade that reaches a point inside
                                     a cut was accumulated by a trace of the
                                     prefix alone — the graded reading of
                                     `composeCut_trace_reflect`.

  Provenance of the bridge. echo-types (pinned in scripts/fetch-siblings.sh)
  proves, in Agda, that a forgetful projection collapses records that differ
  in a provenance tag while the fibre `Echo f y := Σ x, f x ≡ y` keeps them
  apart (`EchoProvenance.agda`). `Interface.fibre` is that fibre for the
  crossing map, stated here in marches' own terms; nothing in this file
  imports or re-declares the Agda. The pairing is a table row
  (docs/kcut-correspondence.adoc), ASSUMED, port-and-reprove, under
  falsifier F6.

  On the laws. Accumulation is a monoid homomorphism from label words, so
  it uses `⊗`-associativity and BOTH units. K-4 (`𝟙 ⊗ x ≡ x`, `x ⊕ x ≡ x`,
  the two laws K-CUT-LOSS uses) does not supply those: provenance needs the
  `⊗`-monoid, not `⊕`-idempotence. `TropicalGrade.grade` has all three.

  Delimitation unchanged: nothing here is protocol convergence; that ground
  is agda-routing's (LIMITATIONS.adoc).
-/

import Marches.Basic
import Marches.Kernel
import Marches.Compose
import Marches.Tropical
import Marches.Cut

namespace Marches

/-! ### Grades: what a word of labels accumulates -/

/-- A grade monoid: `seq` is `⊗`, `one` is `𝟙`. Three laws, not K-4's two. -/
structure Grade where
  G : Type
  seq : G → G → G
  one : G
  seq_assoc : ∀ a b c : G, seq (seq a b) c = seq a (seq b c)
  seq_unitl : ∀ a : G, seq one a = a
  seq_unitr : ∀ a : G, seq a one = a

namespace Grade

/-- The grade a word of labels accumulates, label by label from the left. -/
def accum (g : Grade) {L : Type} (cost : L → g.G) : List L → g.G
  | [] => g.one
  | l :: ls => g.seq (cost l) (accum g cost ls)

theorem accum_nil (g : Grade) {L : Type} (cost : L → g.G) : g.accum cost [] = g.one := rfl

theorem accum_cons (g : Grade) {L : Type} (cost : L → g.G) (l : L) (ls : List L) :
    g.accum cost (l :: ls) = g.seq (cost l) (g.accum cost ls) := rfl

theorem accum_singleton (g : Grade) {L : Type} (cost : L → g.G) (l : L) :
    g.accum cost [l] = cost l :=
  g.seq_unitr (cost l)

/-- Accumulation is a monoid homomorphism from label words: the grade of a
    concatenation is the sequencing of the grades. Uses `seq_assoc` and
    `seq_unitl`. -/
theorem accum_append (g : Grade) {L : Type} (cost : L → g.G) :
    ∀ ls₁ ls₂ : List L, g.accum cost (ls₁ ++ ls₂) = g.seq (g.accum cost ls₁) (g.accum cost ls₂)
  | [], _ => (g.seq_unitl _).symm
  | l :: ls₁, ls₂ =>
    (congrArg (g.seq (cost l)) (accum_append g cost ls₁ ls₂)).trans
      (g.seq_assoc (cost l) (g.accum cost ls₁) (g.accum cost ls₂)).symm

/-- Accumulation reads through a relabelling: grading the image of a word
    is grading the word by the composed cost. -/
theorem accum_map (g : Grade) {L L' : Type} (cost : L → g.G) (f : L' → L) :
    ∀ ls : List L', g.accum cost (ls.map f) = g.accum (fun l => cost (f l)) ls
  | [] => rfl
  | l :: ls => congrArg (g.seq (cost (f l))) (accum_map g cost f ls)

end Grade

/-! ### The tropical grade: provenance in one region -/

namespace TropicalGrade

/-- The (min, +) grade as a monoid: `⊗` is `+`, `𝟙` is `0`. Associativity
    and the right unit are beyond K-4; accumulation needs them. -/
def grade : Grade where
  G := Nat
  seq := seq
  one := one
  seq_assoc := Nat.add_assoc
  seq_unitl := seq_unitl
  seq_unitr := Nat.add_zero

/-- The cost a label carries: `w + 1`, as `ext_eq_seq` reads extension. -/
def cost (w : Nat) : Nat := w + 1

/-- The grade a tropical word carries. -/
def carried (ls : List Nat) : Nat := grade.accum cost ls

theorem carried_nil : carried [] = one := rfl

theorem carried_cons (w : Nat) (ls : List Nat) : carried (w :: ls) = seq (cost w) (carried ls) := rfl

theorem carried_append (ls₁ ls₂ : List Nat) :
    carried (ls₁ ++ ls₂) = seq (carried ls₁) (carried ls₂) :=
  grade.accum_append cost ls₁ ls₂

/-- PROVENANCE, one region: running a word from `a` lands at
    `a ⊗ carried(word)`. The end signature is the start plus what the word
    carried, and nothing else. -/
theorem run_eq_seq_carried : ∀ (ls : List Nat) (a : Nat), run TropicalNat ls a = seq a (carried ls)
  | [], a => (Nat.add_zero a).symm
  | w :: ls, a =>
    (run_eq_seq_carried ls (a + (w + 1))).trans (Nat.add_assoc a (w + 1) (carried ls))

/-- A non-empty word carries a non-unit grade: strict inflation, read as
    provenance. `label_cost_ne_one` lifted from one label to a word. -/
theorem carried_cons_ne_one (w : Nat) (ls : List Nat) : carried (w :: ls) ≠ one :=
  Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.succ_pos w) (Nat.le_add_right (w + 1) (carried ls)))

/-- Loop-freedom recovered from provenance: a word returning to its start
    carries the unit, and a non-empty word does not. The same statement as
    `tropical_no_return`, reached through the grade. -/
theorem no_return_of_carried (w : Nat) (ls : List Nat) (a : Nat) :
    run TropicalNat (w :: ls) a ≠ a :=
  fun h =>
    Nat.ne_of_gt
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self a)
        (Nat.add_le_add_left
          (Nat.succ_le_of_lt
            (Nat.lt_of_lt_of_le (Nat.succ_pos w) (Nat.le_add_right (w + 1) (carried ls))))
          a))
      ((run_eq_seq_carried (w :: ls) a).symm.trans h)

end TropicalGrade

/-! ### What crosses the interface: the shape of a crossing trace -/

/-- A trace that starts in B is a B-word, and ends where that word runs to. -/
theorem trace_from_B (A B : PathAlgebra) (I : Interface A B) :
    ∀ {p : Pos A B} {ls : List (CLabel A B)} {q : Pos A B}, Trace A B I p ls q →
      ∀ x : B.Carrier, p = .inB x →
        ∃ bs : List B.Label, ls = bs.map CLabel.lb ∧ q = .inB (run B bs x) := by
  intro p ls q ht
  induction ht with
  | nil => intro x hx; exact ⟨[], rfl, hx⟩
  | cons hs _ ih =>
    intro x hx
    cases hs with
    | la => cases hx
    | @lb l x' =>
      cases hx
      obtain ⟨bs, hls, hq⟩ := ih _ rfl
      exact ⟨l :: bs, by rw [hls]; rfl, hq⟩
    | cross => cases hx

/-- SHAPE: a well-typed two-region trace that crosses is an A-word from an
    A-start, the crossing, then a B-word; it ends where the B-word runs to
    from `τ` of where the A-word ran to. Typing alone gives this; no
    strictness is used. What the trace carries across the interface is
    `run A as a₀`, and the B side sees it only through `τ`. -/
theorem trace_cross_shape (A B : PathAlgebra) (I : Interface A B) :
    ∀ {p : Pos A B} {ls : List (CLabel A B)} {q : Pos A B}, Trace A B I p ls q →
      CLabel.cross ∈ ls →
        ∃ (a₀ : A.Carrier) (as : List A.Label) (bs : List B.Label),
          p = .inA a₀ ∧ ls = as.map CLabel.la ++ CLabel.cross :: bs.map CLabel.lb ∧
          q = .inB (run B bs (I.τ (run A as a₀))) := by
  intro p ls q ht
  induction ht with
  | nil => intro hl; cases hl
  | cons hs ht' ih =>
    intro hl
    cases hs with
    | @la l x =>
      cases hl with
      | tail _ hl' =>
        obtain ⟨a₀, as, bs, hp, hls, hq⟩ := ih hl'
        cases hp
        exact ⟨x, l :: as, bs, rfl, by rw [hls]; rfl, hq⟩
    | lb =>
      cases hl with
      | tail _ hl' =>
        obtain ⟨_, _, _, hp, _, _⟩ := ih hl'
        cases hp
    | @cross x =>
      obtain ⟨bs, hls, hq⟩ := trace_from_B A B I ht' _ rfl
      exact ⟨x, [], bs, rfl, by rw [hls]; rfl, hq⟩

/-! ### The fibre of the crossing map (echo-types bridge) -/

/-- The fibre of the crossing map over a B-signature: the A-signatures that
    cross to it. This is the preimage fibre — what echo-types writes
    `Echo τ y := Σ x, τ x ≡ y` — in marches' own terms. The B side cannot
    tell its points apart; a trace's provenance lives here. -/
def Interface.fibre {A B : PathAlgebra} (I : Interface A B) (y : B.Carrier) : Type :=
  {x : A.Carrier // I.τ x = y}

/-- What a crossing trace carries: the A-signature at the crossing, as a
    point of the fibre over where it lands. (echo-types' `echo-intro`,
    applied to `run A as a₀`.) -/
def Interface.carried {A B : PathAlgebra} (I : Interface A B) (a₀ : A.Carrier) (as : List A.Label) :
    I.fibre (I.τ (run A as a₀)) :=
  ⟨run A as a₀, rfl⟩

/-- Every crossing trace lands in the image of `τ`, at the point its
    carried signature crosses to — the shape theorem, read on the fibre. -/
theorem trace_cross_lands (A B : PathAlgebra) (I : Interface A B)
    {p : Pos A B} {ls : List (CLabel A B)} {q : Pos A B}
    (ht : Trace A B I p ls q) (hl : CLabel.cross ∈ ls) :
    ∃ (a₀ : A.Carrier) (as : List A.Label) (bs : List B.Label),
      q = .inB (run B bs (I.τ (I.carried a₀ as).1)) := by
  obtain ⟨a₀, as, bs, _, _, hq⟩ := trace_cross_shape A B I ht hl
  exact ⟨a₀, as, bs, hq⟩

/-! ### Cuts of the region DAG: what reaches a crossing is accumulated in the prefix -/

namespace DiscSys

variable (S : DiscSys)

/-- The grade that reaches a point inside a cut was accumulated by a trace
    of the cut prefix alone, label for label: the graded reading of
    `composeCut_trace_reflect`. Whatever lies beyond the frontier
    contributes nothing to it. -/
theorem carried_in_cut (hacyc : Acyclic S.E) (C : Cut S.E) (g : Grade) (cost : S.Lab → g.G)
    {p : (S.compose hacyc).Pos} {ls : List (S.compose hacyc).Lab} {q : (S.compose hacyc).Pos}
    (ht : Discipline.Trace (S.compose hacyc) p ls q) (hq : C.mem q.1) :
    ∃ ls' : List (S.restrict C).Lab,
      ls'.map (S.labEmb C) = ls ∧
      g.accum cost ls = g.accum (fun l => cost (S.labEmb C l)) ls' ∧
      Discipline.Trace (S.composeCut hacyc C)
        ⟨⟨p.1, S.trace_mem_back hacyc C ht hq⟩, p.2⟩ ls' ⟨⟨q.1, hq⟩, q.2⟩ := by
  obtain ⟨ls', hmap, ht'⟩ := S.composeCut_trace_reflect hacyc C ht hq
  exact ⟨ls', hmap, by rw [← hmap, g.accum_map], ht'⟩

/-- The grade that reaches a crossing `r → r'` was accumulated inside the
    principal cut `↓r`: the word splits as prefix, crossing, suffix; its
    grade factors the same way; and the prefix is a trace of
    `composeCut (past r)` from the trace's start, ending in `r`. -/
theorem carried_to_cross_in_past (hacyc : Acyclic S.E) (g : Grade) (cost : S.Lab → g.G)
    {p : (S.compose hacyc).Pos} {ls : List (S.compose hacyc).Lab} {q : (S.compose hacyc).Pos}
    (ht : Discipline.Trace (S.compose hacyc) p ls q)
    {r r' : S.R} {e : S.E r r'} (hl : Lab.cross r r' e ∈ ls) :
    ∃ ls₁ ls₂ : List S.Lab,
      ls = ls₁ ++ Lab.cross r r' e :: ls₂ ∧
      g.accum cost ls = g.seq (g.accum cost ls₁) (g.seq (cost (.cross r r' e)) (g.accum cost ls₂)) ∧
      ∃ (ls₁' : List (S.restrict (Cut.past r)).Lab)
        (p' m' : (S.composeCut hacyc (Cut.past r)).Pos),
        S.posEmb (Cut.past r) p' = p ∧ (S.posEmb (Cut.past r) m').1 = r ∧
        ls₁'.map (S.labEmb (Cut.past r)) = ls₁ ∧
        g.accum cost ls₁ = g.accum (fun l => cost (S.labEmb (Cut.past r) l)) ls₁' ∧
        Discipline.Trace (S.composeCut hacyc (Cut.past r)) p' ls₁' m' := by
  obtain ⟨ls₁, ls₂, m, _, he, h₁, hm, _⟩ := Discipline.trace_split _ ht hl
  obtain ⟨hmr, _⟩ := S.cross_step_regions hm
  have hmC : (Cut.past (E := S.E) r).mem m.1 := Or.inl hmr
  have hp : (Cut.past (E := S.E) r).mem p.1 := S.trace_mem_back hacyc (Cut.past r) h₁ hmC
  obtain ⟨ls₁', hmap, ht'⟩ := S.composeCut_trace_reflect_of hacyc (Cut.past r) h₁ hp hmC
  subst he
  refine ⟨ls₁, ls₂, rfl, g.accum_append cost ls₁ (Lab.cross r r' e :: ls₂),
    ls₁', ⟨⟨p.1, hp⟩, p.2⟩, ⟨⟨m.1, hmC⟩, m.2⟩, rfl, hmr, hmap, ?_, ht'⟩
  rw [← hmap, g.accum_map]

end DiscSys

/-! ### Concrete exhibits: the theorems are not vacuous -/

namespace ProvenanceExhibit

open TropicalGrade

/-- One region: the word `[2, 0]` carries `3 + 1 = 4`, and running it from
    cost `0` lands at `4`. -/
example : carried [2, 0] = 4 ∧
    run TropicalNat ([2, 0] : List Nat) (0 : Nat) = seq 0 (carried [2, 0]) :=
  ⟨rfl, run_eq_seq_carried [2, 0] 0⟩

/-- The identity crossing between two tropical regions (the interface form
    of `Reassembly.twoTropical`). -/
def idI : Interface TropicalNat TropicalNat where
  τ := fun x => x

/-- A collapsing crossing: every A-signature crosses to cost `0`. -/
def zeroI : Interface TropicalNat TropicalNat where
  τ := fun _ => (0 : Nat)

/-- Under the identity crossing the grade crosses intact: the end cost is
    the start plus what BOTH words carried, as one word. -/
theorem id_carries (a₀ : Nat) (as bs : List Nat) :
    run TropicalNat bs (idI.τ (run TropicalNat as a₀)) = seq a₀ (carried (as ++ bs)) := by
  show run TropicalNat bs (run TropicalNat as a₀) = seq a₀ (carried (as ++ bs))
  rw [run_eq_seq_carried, run_eq_seq_carried, carried_append]
  exact Nat.add_assoc a₀ (carried as) (carried bs)

/-- Under the collapsing crossing the A-grade is forgotten: the end cost does
    not depend on the A-word at all. (echo-types' `provenance-collapses-at`,
    in marches' terms.) -/
theorem zero_forgets (a₀ : Nat) (as as' bs : List Nat) :
    run TropicalNat bs (zeroI.τ (run TropicalNat as a₀)) =
      run TropicalNat bs (zeroI.τ (run TropicalNat as' a₀)) :=
  rfl

/-- ...and the fibre over the landing point still tells the two apart: the
    words `[0]` and `[1]` carry `1` and `2`. (echo-types'
    `echoes-distinguish-tag`.) -/
theorem zero_fibre_distinguishes :
    (zeroI.carried (0 : Nat) [(0 : Nat)]).1 ≠ (zeroI.carried (0 : Nat) [(1 : Nat)]).1 := by
  show (1 : Nat) ≠ 2
  decide

/-- Two well-typed traces over the collapsing crossing, from the same start,
    with different A-words, to the SAME end: the B side cannot tell them
    apart. -/
theorem collapse₀ :
    Trace TropicalNat TropicalNat zeroI (.inA (0 : Nat)) [.la (0 : Nat), .cross, .lb (0 : Nat)]
      (.inB (1 : Nat)) :=
  .cons .la (.cons .cross (.cons .lb .nil))

theorem collapse₁ :
    Trace TropicalNat TropicalNat zeroI (.inA (0 : Nat)) [.la (1 : Nat), .cross, .lb (0 : Nat)]
      (.inB (1 : Nat)) :=
  .cons .la (.cons .cross (.cons .lb .nil))

/-- The shape theorem on `collapse₀`: it is `[0]`, the crossing, `[0]`. -/
example : ∃ (a₀ : TropicalNat.Carrier) (as bs : List TropicalNat.Label),
    Pos.inA (A := TropicalNat) (B := TropicalNat) (0 : Nat) = .inA a₀ ∧
    [CLabel.la (A := TropicalNat) (B := TropicalNat) (0 : Nat), .cross, .lb (0 : Nat)] =
      as.map CLabel.la ++ CLabel.cross :: bs.map CLabel.lb ∧
    Pos.inB (A := TropicalNat) (B := TropicalNat) (1 : Nat) =
      .inB (run TropicalNat bs (zeroI.τ (run TropicalNat as a₀))) :=
  trace_cross_shape TropicalNat TropicalNat zeroI collapse₀ (.tail _ (.head _))

/-- The composite exhibit of `Cut.lean`, graded: local labels cost `w + 1`,
    the crossing costs `𝟙`. -/
def cost₀ : Reassembly.twoTropical.Lab → Nat
  | .loc _ w => cost w
  | .cross _ _ _ => one

/-- The word of `CutExhibit.trace₀`: a hop of weight 2 in region `false`,
    the crossing, a hop of weight 0 in region `true`. -/
def word₀ : List Reassembly.twoTropical.Lab :=
  [.loc false (2 : Nat), .cross false true CutExhibit.e₀, .loc true (0 : Nat)]

/-- `trace₀` runs cost 0 → 4, and its word carries `3 + 0 + 1 = 4`. -/
example : grade.accum cost₀ word₀ = (4 : Nat) := rfl

/-- `carried_to_cross_in_past` on `trace₀`: the grade before the crossing is
    accumulated by a trace of `↓false` alone. -/
example : ∃ ls₁ ls₂ : List Reassembly.twoTropical.Lab,
    word₀ = ls₁ ++ .cross false true CutExhibit.e₀ :: ls₂ ∧
    grade.accum cost₀ word₀ =
      seq (grade.accum cost₀ ls₁) (seq (cost₀ (.cross false true CutExhibit.e₀)) (grade.accum cost₀ ls₂)) ∧
    ∃ (ls₁' : List (Reassembly.twoTropical.restrict (Cut.past false)).Lab)
      (p' m' : (Reassembly.twoTropical.composeCut Reassembly.boolUp_acyclic (Cut.past false)).Pos),
      Reassembly.twoTropical.posEmb (Cut.past false) p' = ⟨false, (0 : Nat)⟩ ∧
      (Reassembly.twoTropical.posEmb (Cut.past false) m').1 = false ∧
      ls₁'.map (Reassembly.twoTropical.labEmb (Cut.past false)) = ls₁ ∧
      grade.accum cost₀ ls₁ =
        grade.accum (fun l => cost₀ (Reassembly.twoTropical.labEmb (Cut.past false) l)) ls₁' ∧
      Discipline.Trace (Reassembly.twoTropical.composeCut Reassembly.boolUp_acyclic (Cut.past false))
        p' ls₁' m' :=
  Reassembly.twoTropical.carried_to_cross_in_past Reassembly.boolUp_acyclic grade cost₀
    CutExhibit.trace₀ (.tail _ (.head _))

end ProvenanceExhibit

end Marches
