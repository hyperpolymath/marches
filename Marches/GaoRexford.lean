/-
  Marches — Gao–Rexford finite exhibit.

  The classical commercial-relationship algebra: route signatures
  {customer-route c, peer-route r, provider-route p, invalid ⊥} with
  extension over the three arc relationships (route learned FROM a
  customer / peer / provider), encoding the standard export rules:
    • a customer exports only its customer routes upward;
    • a peer exports only its customer routes sideways;
    • a provider exports everything downward.

  Machine-checked facts (all by `decide` over the finite tables):
    • gr_inflationary : extension NEVER improves.
    • gr_not_strict   : extension is NOT strictly worsening —
                        the (fromCust, c) fixed point. This is the
                        classical gap: Gao–Rexford convergence needs
                        the ASSUMED acyclicity of the customer→provider
                        hierarchy on top of the algebra. Status ASSUMED,
                        recorded, not hidden.
    • valley_dies     : re-exporting a provider-learned route upward
                        is typed to ⊥ — the valley dies at the type
                        level rather than being filtered at runtime.
-/

import Marches.Basic

namespace Marches
namespace GR

inductive Sig where
  | c | r | p | bot
  deriving DecidableEq, Repr

inductive Rel where
  | fromCust | fromPeer | fromProv
  deriving DecidableEq, Repr

def rank : Sig → Nat
  | .c => 0 | .r => 1 | .p => 2 | .bot => 3

/-- Extension table encoding Gao–Rexford export rules. -/
def gext : Rel → Sig → Sig
  | .fromCust, .c => .c
  | .fromCust, _  => .bot
  | .fromPeer, .c => .r
  | .fromPeer, _  => .bot
  | .fromProv, .c => .p
  | .fromProv, .r => .p
  | .fromProv, .p => .p
  | .fromProv, .bot => .bot

/-- Extension never improves (12 cases, machine-checked). -/
theorem gr_inflationary : ∀ (l : Rel) (s : Sig), ¬ rank (gext l s) < rank s := by
  intro l s
  cases l <;> cases s <;> decide

/-- Extension is NOT strictly worsening: witness (fromCust, c). -/
theorem gr_not_strict : ¬ ∀ (l : Rel) (s : Sig), rank s < rank (gext l s) := by
  intro h
  exact absurd (h .fromCust .c) (by decide)

/-- The valley dies at the type level: provider-learned then exported
    upward over a customer arc is ⊥. -/
theorem valley_dies : gext .fromCust (gext .fromProv .c) = .bot := by decide

/-- Peer-learned routes likewise never travel upward. -/
theorem peer_route_not_upward : gext .fromCust (gext .fromPeer .c) = .bot := by decide

end GR
end Marches
