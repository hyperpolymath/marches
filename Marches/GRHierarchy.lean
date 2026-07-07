/-
  Marches — the acyclic customer→provider hierarchy, made explicit
  (rung 1).

  Gao–Rexford stability classically ASSUMES the customer→provider
  digraph is acyclic; the algebra alone cannot supply it
  (`gr_not_strict` in GaoRexford.lean is the PROVEN gap, falsifier F5).
  This module names that assumption as an explicit hypothesis
  (`Acyclic`) and derives loop-freedom UNDER it — the hypothesis is
  threaded, never silently discharged.

  Headline (PROVEN, `lake build`):
    • gr_loop_free : over any topology whose customer→provider
      hierarchy is acyclic, a well-typed trace returning to the same
      (node, signature) state is empty.

  Claim discipline: state-level loop-freedom of well-typed traces is
  NOT protocol convergence. Formally verified convergence of
  policy-rich path-vector protocols (asynchronous, rate results,
  BGPLite) is agda-routing (Daggitt, Zmigrod, van der Stoep, Griffin);
  see LIMITATIONS.adoc. Nothing here re-claims that ground.
-/

import Marches.GRTrace

namespace Marches
namespace GR

variable {V : Type}

/-- Non-empty paths in a relation. -/
inductive RPath (R : V → V → Prop) : V → V → Prop where
  | single {u v : V} : R u v → RPath R u v
  | cons {u v w : V} : R u v → RPath R v w → RPath R u w

/-- THE Gao–Rexford hypothesis, explicit and named: no non-empty cycle
    in the relation (read: in the customer→provider hierarchy). This is
    ASSUMED about real topologies, exactly as in Gao–Rexford 2001; it
    is a hypothesis of `gr_loop_free`, never proven here. -/
def Acyclic (R : V → V → Prop) : Prop := ∀ v : V, ¬ RPath R v v

theorem rpath_snoc {R : V → V → Prop} :
    ∀ {u v w : V}, RPath R u v → R v w → RPath R u w := by
  intro u v w h
  induction h with
  | single h1 => intro h2; exact .cons h1 (.single h2)
  | cons h1 _ ih => intro h2; exact .cons h1 (ih h2)

/-- A cycle in the reversed relation reverses into a cycle proper:
    acyclicity kills provider-chains as well as customer-chains. -/
theorem rpath_flip {R : V → V → Prop} :
    ∀ {u v : V}, RPath (fun a b => R b a) u v → RPath R v u := by
  intro u v h
  induction h with
  | single h1 => exact .single h1
  | cons h1 _ ih => exact rpath_snoc ih h1

/-- An AS-level topology: `custOf u v` reads "u is a customer of v";
    `peerOf u v` reads "u and v peer" (directed as used). -/
structure Topo (V : Type) where
  custOf : V → V → Prop
  peerOf : V → V → Prop

/-- One node-level well-typed step, labelled at the RECEIVER `v`:
    `cust` — v learns from its customer u; `peer` — from its peer u;
    `prov` — from its provider u (so v is u's customer). The signature
    moves by `GStep`, so ill-typed exports remain unconstructible. -/
inductive NStep (T : Topo V) : Rel → V × Sig → V × Sig → Prop where
  | cust {u v : V} {s t : Sig} :
      T.custOf u v → GStep .fromCust s t → NStep T .fromCust (u, s) (v, t)
  | peer {u v : V} {s t : Sig} :
      T.peerOf u v → GStep .fromPeer s t → NStep T .fromPeer (u, s) (v, t)
  | prov {u v : V} {s t : Sig} :
      T.custOf v u → GStep .fromProv s t → NStep T .fromProv (u, s) (v, t)

/-- Well-typed node-level traces. -/
inductive NTrace (T : Topo V) : V × Sig → List Rel → V × Sig → Prop where
  | nil  {ps : V × Sig} : NTrace T ps [] ps
  | cons {ps qt ru : V × Sig} {rel : Rel} {ls : List Rel} :
      NStep T rel ps qt → NTrace T qt ls ru → NTrace T ps (rel :: ls) ru

/-- Every node-level step carries a signature-level step. -/
theorem nstep_gstep {T : Topo V} {rel : Rel} {ps qt : V × Sig}
    (h : NStep T rel ps qt) : GStep rel ps.2 qt.2 := by
  cases h with
  | cust _ hg => exact hg
  | peer _ hg => exact hg
  | prov _ hg => exact hg

/-- Node-level traces project to the typing judgment of GRTrace.lean. -/
theorem ntrace_gtrace {T : Topo V} : ∀ {ps : V × Sig} {ls : List Rel}
    {qt : V × Sig}, NTrace T ps ls qt → GTrace ps.2 ls qt.2 := by
  intro ps ls qt h
  induction h with
  | nil => exact .nil
  | cons hstep _ ih => exact .cons (nstep_gstep hstep) ih

/-- Corollary: every node-level trace of a customer route is a
    valley-free word — the grammar holds over any topology. -/
theorem ntrace_valley_free {T : Topo V} {u v : V} {t : Sig}
    {ls : List Rel} (h : NTrace T (u, .c) ls (v, t)) : ValleyFree ls :=
  gtrace_valley_free (ntrace_gtrace h)

/-! ### Rank monotonicity -/

theorem gstep_rank_le {rel : Rel} {s t : Sig} (h : GStep rel s t) :
    rank s ≤ rank t := by
  cases h <;> decide

theorem nstep_rank_le {T : Topo V} {rel : Rel} {ps qt : V × Sig}
    (h : NStep T rel ps qt) : rank ps.2 ≤ rank qt.2 :=
  gstep_rank_le (nstep_gstep h)

theorem ntrace_rank_le {T : Topo V} : ∀ {ps : V × Sig} {ls : List Rel}
    {qt : V × Sig}, NTrace T ps ls qt → rank ps.2 ≤ rank qt.2 := by
  intro ps ls qt h
  induction h with
  | nil => exact Nat.le_refl _
  | cons hstep _ ih => exact Nat.le_trans (nstep_rank_le hstep) ih

/-! ### Rank-flat traces are hierarchy chains -/

/-- A non-empty `c`-to-`c` trace is a chain in the customer→provider
    hierarchy (every step is a customer-arc self-export). -/
theorem trace_c_path {T : Topo V} :
    ∀ {ls : List Rel} {u v : V},
      NTrace T (u, .c) ls (v, .c) → ls ≠ [] → RPath T.custOf u v := by
  intro ls
  induction ls with
  | nil => intro u v _ hne; exact absurd rfl hne
  | cons rel ls ih =>
    intro u v h _
    cases h with
    | cons hstep htail =>
      cases hstep with
      | cust harc hg =>
        cases hg
        cases ls with
        | nil => cases htail; exact .single harc
        | cons rel' ls' => exact .cons harc (ih htail (List.cons_ne_nil _ _))
      | peer harc hg =>
        cases hg
        exact absurd (ntrace_rank_le htail)
          (show ¬ rank Sig.r ≤ rank Sig.c by decide)
      | prov harc hg =>
        cases hg
        exact absurd (ntrace_rank_le htail)
          (show ¬ rank Sig.p ≤ rank Sig.c by decide)

/-- A non-empty `p`-to-`p` trace is a provider chain: a path in the
    REVERSED hierarchy. -/
theorem trace_p_path {T : Topo V} :
    ∀ {ls : List Rel} {u v : V},
      NTrace T (u, .p) ls (v, .p) → ls ≠ [] →
      RPath (fun a b => T.custOf b a) u v := by
  intro ls
  induction ls with
  | nil => intro u v _ hne; exact absurd rfl hne
  | cons rel ls ih =>
    intro u v h _
    cases h with
    | cons hstep htail =>
      cases hstep with
      | cust _ hg => cases hg
      | peer _ hg => cases hg
      | prov harc hg =>
        cases hg
        cases ls with
        | nil => cases htail; exact .single harc
        | cons rel' ls' => exact .cons harc (ih htail (List.cons_ne_nil _ _))

/-- HEADLINE: loop-freedom for Gao–Rexford, UNDER the explicit
    acyclicity hypothesis. A well-typed trace over an acyclic
    customer→provider hierarchy that returns to the same
    (node, signature) state is empty.

    Delimitation: this is loop-freedom of the typed propagation
    judgment, by construction — NOT a convergence theorem for BGP or
    any protocol. Mechanised convergence (asynchronous, policy-rich)
    is agda-routing (Daggitt–Griffin); see LIMITATIONS.adoc. The
    acyclicity hypothesis itself remains ASSUMED about real
    topologies, exactly as in Gao–Rexford 2001. -/
theorem gr_loop_free {T : Topo V} (hacyc : Acyclic T.custOf)
    {v : V} {s : Sig} {ls : List Rel}
    (h : NTrace T (v, s) ls (v, s)) : ls = [] := by
  cases ls with
  | nil => rfl
  | cons rel ls' =>
    exfalso
    cases s with
    | c => exact hacyc v (trace_c_path h (List.cons_ne_nil _ _))
    | p => exact hacyc v (rpath_flip (trace_p_path h (List.cons_ne_nil _ _)))
    | r =>
      cases h with
      | cons hstep htail =>
        cases hstep with
        | cust _ hg => cases hg
        | peer _ hg => cases hg
        | prov _ hg =>
          cases hg
          exact absurd (ntrace_rank_le htail)
            (show ¬ rank Sig.p ≤ rank Sig.r by decide)
    | bot =>
      cases h with
      | cons hstep _ =>
        cases hstep with
        | cust _ hg => cases hg
        | peer _ hg => cases hg
        | prov _ hg => cases hg

end GR
end Marches
