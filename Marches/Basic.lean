/-
  Marches — Basic definitions.

  A *path algebra*: route signatures with a strict preference order,
  policy labels, and an extension action (applying an arc's policy to
  a route). `better a b` reads "a is strictly preferred to b"
  (min-selection convention: lower is better).

  Claim discipline: everything in this file is a DEFINITION.
  Theorems live in Kernel.lean / Compose.lean and carry status PROVEN
  iff `lake build` succeeds.
-/

namespace Marches

structure PathAlgebra where
  Carrier : Type
  Label   : Type
  /-- Strict preference: `better a b` means `a` strictly preferred to `b`. -/
  better  : Carrier → Carrier → Prop
  /-- Policy extension: apply arc label `l` to route signature `a`. -/
  ext     : Label → Carrier → Carrier
  trans   : ∀ {a b c : Carrier}, better a b → better b c → better a c
  irrefl  : ∀ a : Carrier, ¬ better a a

/-- Sobrinho-style strictness: extension strictly worsens every route.
    (In Sobrinho's notation: a ≺ l ⊕ a.) -/
def StrictlyInflationary (A : PathAlgebra) : Prop :=
  ∀ (l : A.Label) (a : A.Carrier), A.better a (A.ext l a)

/-- Non-strict variant: extension never improves a route. -/
def Inflationary (A : PathAlgebra) : Prop :=
  ∀ (l : A.Label) (a : A.Carrier), ¬ A.better (A.ext l a) a

/-- Run a word of labels left-to-right from a starting signature. -/
def run (A : PathAlgebra) : List A.Label → A.Carrier → A.Carrier
  | [],      a => a
  | l :: ls, a => run A ls (A.ext l a)

theorem strict_implies_inflationary (A : PathAlgebra)
    (h : StrictlyInflationary A) : Inflationary A := by
  intro l a hbad
  exact A.irrefl a (A.trans (h l a) hbad)

end Marches
