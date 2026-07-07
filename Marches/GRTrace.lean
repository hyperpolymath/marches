/-
  Marches — Gao–Rexford wired into Trace (rung 1).

  The crossing label is generalised to the three GR relationships:
  a step of route propagation is TYPED by (relationship, signature),
  and only the five legal moves are constructors of `GStep`. The
  ill-typed moves — re-exporting a provider- or peer-learned route
  upward (the valley), a second peer hop, any move from ⊥ — have NO
  constructor: unconstructible, not filtered.

  Headline (PROVEN, `lake build`):
    • gtrace_iff_valley_free : derivations of the typing judgment from
      `c` are EXACTLY the valley-free words Cust* Peer? Prov*.
    • valley_free_iff_gwalk  : the grammar coincides with non-⊥
      evaluation of the rung-0 extension table `gext`.
    • no_valley_step, no_peer_reexport_up, no_second_peer,
      no_step_from_bot : the ill-typed moves are underivable.

  Claim discipline: these are statements about the typing judgment and
  the finite GR table. Nothing here is a convergence result; mechanised
  convergence for path-vector routing is agda-routing's ground
  (Daggitt–Griffin et al.) — see LIMITATIONS.adoc.
-/

import Marches.GaoRexford

namespace Marches
namespace GR

/-- One well-typed GR step: route with signature `s`, learned over an
    arc of relationship `rel`, becomes signature `t`. Exactly the five
    non-⊥ entries of `gext` are constructors; everything else is
    unconstructible. -/
inductive GStep : Rel → Sig → Sig → Prop where
  | custCust : GStep .fromCust .c .c
  | peerCust : GStep .fromPeer .c .r
  | provCust : GStep .fromProv .c .p
  | provPeer : GStep .fromProv .r .p
  | provProv : GStep .fromProv .p .p

/-- Well-typed GR traces: the typing judgment on relationship words. -/
inductive GTrace : Sig → List Rel → Sig → Prop where
  | nil  {s : Sig} : GTrace s [] s
  | cons {s t u : Sig} {rel : Rel} {ls : List Rel} :
      GStep rel s t → GTrace t ls u → GTrace s (rel :: ls) u

/-! ### Negative theorems: the ill-typed moves are underivable -/

/-- The valley is unconstructible: a provider-learned route cannot be
    exported upward (over a customer arc). -/
theorem no_valley_step (t : Sig) : ¬ GStep .fromCust .p t := by
  intro h; cases h

/-- A peer-learned route likewise cannot travel upward. -/
theorem no_peer_reexport_up (t : Sig) : ¬ GStep .fromCust .r t := by
  intro h; cases h

/-- A second peer hop is unconstructible. -/
theorem no_second_peer (t : Sig) : ¬ GStep .fromPeer .r t := by
  intro h; cases h

/-- Nothing steps out of ⊥. -/
theorem no_step_from_bot (rel : Rel) (t : Sig) : ¬ GStep rel .bot t := by
  intro h; cases h

/-! ### Agreement with the rung-0 extension table -/

/-- Soundness: a typed step lands exactly where `gext` says. -/
theorem gstep_gext {rel : Rel} {s t : Sig} (h : GStep rel s t) :
    t = gext rel s := by
  cases h <;> rfl

/-- A typed step never produces ⊥. -/
theorem gstep_target_ne_bot {rel : Rel} {s t : Sig} (h : GStep rel s t) :
    t ≠ .bot := by
  cases h <;> decide

/-- Completeness: every non-⊥ entry of the table is a typed step. -/
theorem gstep_complete (rel : Rel) (s : Sig) (h : gext rel s ≠ .bot) :
    GStep rel s (gext rel s) := by
  cases rel <;> cases s <;>
    first
      | exact .custCust
      | exact .peerCust
      | exact .provCust
      | exact .provPeer
      | exact .provProv
      | exact absurd rfl h

/-- Evaluate a relationship word through the table (the `run` of GR). -/
def gwalk : List Rel → Sig → Sig
  | [],        s => s
  | rel :: ls, s => gwalk ls (gext rel s)

theorem gext_bot (rel : Rel) : gext rel .bot = .bot := by
  cases rel <;> rfl

theorem gwalk_bot : ∀ ls : List Rel, gwalk ls .bot = .bot := by
  intro ls
  induction ls with
  | nil => rfl
  | cons rel ls ih => simpa [gwalk, gext_bot] using ih

/-- A derivation evaluates to what the table says. -/
theorem gtrace_gwalk : ∀ {s : Sig} {ls : List Rel} {t : Sig},
    GTrace s ls t → gwalk ls s = t := by
  intro s ls t h
  induction h with
  | nil => rfl
  | cons hstep _ ih => cases hstep <;> simpa [gwalk, gext] using ih

/-- Typed traces preserve non-⊥ness. -/
theorem gtrace_target_ne_bot : ∀ {s : Sig} {ls : List Rel} {t : Sig},
    GTrace s ls t → s ≠ .bot → t ≠ .bot := by
  intro s ls t h
  induction h with
  | nil => exact id
  | cons hstep _ ih =>
    intro _
    apply ih
    cases hstep <;> decide

/-- Non-⊥ evaluation yields a derivation. -/
theorem gwalk_gtrace : ∀ (ls : List Rel) (s : Sig),
    gwalk ls s ≠ .bot → GTrace s ls (gwalk ls s) := by
  intro ls
  induction ls with
  | nil => intro s _; exact .nil
  | cons rel ls ih =>
    intro s h
    have hne : gext rel s ≠ .bot := by
      intro hb
      apply h
      show gwalk ls (gext rel s) = .bot
      rw [hb]; exact gwalk_bot ls
    exact .cons (gstep_complete rel s hne) (ih (gext rel s) h)

/-- Derivability from a live signature ⟺ non-⊥ evaluation. -/
theorem gtrace_exists_iff {s : Sig} (hs : s ≠ .bot) (ls : List Rel) :
    (∃ t, GTrace s ls t) ↔ gwalk ls s ≠ .bot := by
  constructor
  · intro h
    cases h with
    | intro t ht =>
      rw [gtrace_gwalk ht]
      exact gtrace_target_ne_bot ht hs
  · intro h
    exact ⟨gwalk ls s, gwalk_gtrace ls s h⟩

/-! ### The valley-freedom grammar

    `Trace` becomes the grammar: valid words are Cust* Peer? Prov*,
    read from the origin outward. -/

/-- All-provider suffix: Prov*. -/
inductive Downhill : List Rel → Prop where
  | nil : Downhill []
  | cons {ls : List Rel} : Downhill ls → Downhill (.fromProv :: ls)

/-- The Gao–Rexford valley-free words: Cust* Peer? Prov*. -/
inductive ValleyFree : List Rel → Prop where
  | down {ls : List Rel} : Downhill ls → ValleyFree ls
  | peer {ls : List Rel} : Downhill ls → ValleyFree (.fromPeer :: ls)
  | cust {ls : List Rel} : ValleyFree ls → ValleyFree (.fromCust :: ls)

/-- From `p` only Prov* continues. -/
theorem gtrace_p_downhill : ∀ {ls : List Rel} {t : Sig},
    GTrace .p ls t → Downhill ls := by
  intro ls
  induction ls with
  | nil => intro t _; exact .nil
  | cons rel ls ih =>
    intro t h
    cases h with
    | cons hstep htail =>
      cases hstep
      exact .cons (ih htail)

/-- From `r` only Prov* continues. -/
theorem gtrace_r_downhill {ls : List Rel} {t : Sig}
    (h : GTrace .r ls t) : Downhill ls := by
  cases h with
  | nil => exact .nil
  | cons hstep htail =>
    cases hstep
    exact .cons (gtrace_p_downhill htail)

/-- Every derivation from `c` is a valley-free word. -/
theorem gtrace_valley_free : ∀ {ls : List Rel} {t : Sig},
    GTrace .c ls t → ValleyFree ls := by
  intro ls
  induction ls with
  | nil => intro t _; exact .down .nil
  | cons rel ls ih =>
    intro t h
    cases h with
    | cons hstep htail =>
      cases hstep with
      | custCust => exact .cust (ih htail)
      | peerCust => exact .peer (gtrace_r_downhill htail)
      | provCust => exact .down (.cons (gtrace_p_downhill htail))

theorem downhill_gtrace_p : ∀ {ls : List Rel},
    Downhill ls → GTrace .p ls .p := by
  intro ls h
  induction h with
  | nil => exact .nil
  | cons _ ih => exact .cons .provProv ih

theorem downhill_gtrace_r {ls : List Rel} (h : Downhill ls) :
    ∃ t, GTrace .r ls t := by
  cases h with
  | nil => exact ⟨.r, .nil⟩
  | cons h' => exact ⟨.p, .cons .provPeer (downhill_gtrace_p h')⟩

/-- Every valley-free word is derivable from `c`. -/
theorem valley_free_gtrace : ∀ {ls : List Rel},
    ValleyFree ls → ∃ t, GTrace .c ls t := by
  intro ls h
  induction h with
  | down hd =>
    cases hd with
    | nil => exact ⟨.c, .nil⟩
    | cons hd' => exact ⟨.p, .cons .provCust (downhill_gtrace_p hd')⟩
  | peer hd =>
    cases downhill_gtrace_r hd with
    | intro t ht => exact ⟨t, .cons .peerCust ht⟩
  | cust _ ih =>
    cases ih with
    | intro t ht => exact ⟨t, .cons .custCust ht⟩

/-- HEADLINE: the typing judgment from `c` IS the valley-freedom
    grammar. (A statement about derivability, not convergence —
    convergence is agda-routing's ground; see LIMITATIONS.adoc.) -/
theorem gtrace_iff_valley_free (ls : List Rel) :
    (∃ t, GTrace .c ls t) ↔ ValleyFree ls := by
  constructor
  · intro h
    cases h with
    | intro t ht => exact gtrace_valley_free ht
  · exact valley_free_gtrace

/-- Corollary: grammar ⟺ non-⊥ evaluation of the rung-0 table. -/
theorem valley_free_iff_gwalk (ls : List Rel) :
    ValleyFree ls ↔ gwalk ls .c ≠ .bot := by
  rw [← gtrace_iff_valley_free]
  exact gtrace_exists_iff (by decide) ls

end GR
end Marches
