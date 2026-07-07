/-
  Marches — Negative artifact: DISAGREE.

  The smallest classical non-convergent policy pair
  (Griffin–Shepherd–Wilfong's DISAGREE): two nodes, one destination,
  each strictly prefers the route THROUGH the other over its own
  direct route. Under synchronous update the system oscillates with
  period 2 forever.

  Two machine-checked facts form the pincer:
    • disagree_improves / disagree_not_inflationary :
        the DISAGREE preference table VIOLATES the Marches discipline
        (extension strictly improves) — so it is unconstructible as a
        StrictlyInflationary algebra: the types reject exactly the
        policies that oscillate.
    • disagree_two_cycle / disagree_moves :
        the synchronous dynamics genuinely oscillate (period-2 orbit,
        not a fixed point) — the rejected thing really is bad.

  State encoding: (Bool × Bool); component i is `true` iff node i is
  currently using the indirect route (via the other node). A node
  adopts the indirect route exactly when the other node is on its
  direct route (otherwise the path through the other loops back).
-/

import Marches.Basic

namespace Marches
namespace Disagree

/-- Synchronous update of DISAGREE. -/
def step (s : Bool × Bool) : Bool × Bool := (!s.2, !s.1)

/-- The dynamics are a period-≤2 orbit from every state. -/
theorem disagree_two_cycle : ∀ s : Bool × Bool, step (step s) = s := by
  intro s
  obtain ⟨a, b⟩ := s
  cases a <;> cases b <;> rfl

/-- From (direct, direct) the system genuinely moves: not a fixed point. -/
theorem disagree_moves : step (false, false) ≠ (false, false) := by decide

/-- Trace of the oscillation for the README (evaluates to the 2-cycle). -/
def orbit : List (Bool × Bool) :=
  [ (false, false), step (false, false), step (step (false, false)),
    step (step (step (false, false))) ]

#eval orbit  -- [(false,false),(true,true),(false,false),(true,true)]

/-- One node's route signatures under DISAGREE preferences:
    viaOther ≺ direct ≺ invalid (it PREFERS the indirect route). -/
inductive DRoute where
  | direct | viaOther | invalid
  deriving DecidableEq, Repr

def drank : DRoute → Nat
  | .viaOther => 0 | .direct => 1 | .invalid => 2

/-- Extension over the peer arc: hearing the other's direct route
    yields the (preferred!) indirect route. -/
def dext : DRoute → DRoute
  | .direct => .viaOther
  | .viaOther => .invalid
  | .invalid => .invalid

/-- DISAGREE extension strictly IMPROVES on the witness — the exact
    negation of the Marches requirement. -/
theorem disagree_improves : drank (dext .direct) < drank .direct := by decide

/-- Hence DISAGREE is not even (non-strictly) inflationary:
    the discipline rejects it. -/
theorem disagree_not_inflationary :
    ¬ ∀ r : DRoute, ¬ drank (dext r) < drank r := by
  intro h
  exact h .direct (by decide)

end Disagree
end Marches
