/-
  Marches — Typed region composition.

  Two regions (path algebras) A and B, joined by ONE typed crossing
  morphism τ : A → B. The composite carries a STRATIFIED preference:
  within-region preference is inherited; every A-position is strictly
  preferred to every B-position (Gao–Rexford-style stratification,
  here taken as the interface type's meaning).

  The well-formedness of a cross-region trace is a TYPING JUDGMENT
  (`Trace`). Ill-typed moves — an A-label fired from B, or a crossing
  fired from B back into A — have NO constructor: they are
  unconstructible, not detected.

  Headline theorems:
    • trace_worsens        : every well-typed non-empty trace strictly worsens.
    • wt_cycles_are_empty  : a well-typed trace that returns to its start
                             is empty — no well-typed routing loop exists.
    • no_back_cross, no_a_label_in_B : the ill-typed moves are underivable.
-/

import Marches.Basic

namespace Marches

/-- Positions of the composite system: inside A or inside B. -/
inductive Pos (A B : PathAlgebra) where
  | inA : A.Carrier → Pos A B
  | inB : B.Carrier → Pos A B

/-- Labels of the composite system: A-labels, B-labels, one crossing. -/
inductive CLabel (A B : PathAlgebra) where
  | la    : A.Label → CLabel A B
  | lb    : B.Label → CLabel A B
  | cross : CLabel A B

/-- A typed interface: the crossing morphism. (Preference-preservation
    `strict` is recorded for downstream use; the kernel theorems below
    need only stratification, which is built into `CBetter`.) -/
structure Interface (A B : PathAlgebra) where
  τ : A.Carrier → B.Carrier
  strict : ∀ {a b : A.Carrier}, A.better a b → B.better (τ a) (τ b)

/-- Stratified preference on the composite. -/
inductive CBetter (A B : PathAlgebra) : Pos A B → Pos A B → Prop where
  | aa {x y : A.Carrier} : A.better x y → CBetter A B (.inA x) (.inA y)
  | bb {x y : B.Carrier} : B.better x y → CBetter A B (.inB x) (.inB y)
  | ab {x : A.Carrier} {y : B.Carrier} : CBetter A B (.inA x) (.inB y)

theorem ctrans (A B : PathAlgebra) :
    ∀ {p q r : Pos A B}, CBetter A B p q → CBetter A B q r → CBetter A B p r := by
  intro p q r h1 h2
  cases h1 with
  | aa hxy =>
    cases h2 with
    | aa hyz => exact .aa (A.trans hxy hyz)
    | ab => exact .ab
  | bb hxy =>
    cases h2 with
    | bb hyz => exact .bb (B.trans hxy hyz)
  | ab =>
    cases h2 with
    | bb _ => exact .ab

theorem cirrefl (A B : PathAlgebra) :
    ∀ p : Pos A B, ¬ CBetter A B p p := by
  intro p h
  cases h with
  | aa h => exact A.irrefl _ h
  | bb h => exact B.irrefl _ h

/-- One well-typed step of the composite system. -/
inductive Step (A B : PathAlgebra) (I : Interface A B) :
    CLabel A B → Pos A B → Pos A B → Prop where
  | la {l : A.Label} {x : A.Carrier} :
      Step A B I (.la l) (.inA x) (.inA (A.ext l x))
  | lb {l : B.Label} {x : B.Carrier} :
      Step A B I (.lb l) (.inB x) (.inB (B.ext l x))
  | cross {x : A.Carrier} :
      Step A B I .cross (.inA x) (.inB (I.τ x))

/-- Well-typed traces: the typing judgment on label words. -/
inductive Trace (A B : PathAlgebra) (I : Interface A B) :
    Pos A B → List (CLabel A B) → Pos A B → Prop where
  | nil  {p : Pos A B} : Trace A B I p [] p
  | cons {p q r : Pos A B} {l : CLabel A B} {ls : List (CLabel A B)} :
      Step A B I l p q → Trace A B I q ls r → Trace A B I p (l :: ls) r

/-- Negative theorem: crossing back from B is unconstructible. -/
theorem no_back_cross (A B : PathAlgebra) (I : Interface A B)
    (x : B.Carrier) (q : Pos A B) :
    ¬ Step A B I .cross (.inB x) q := by
  intro h; cases h

/-- Negative theorem: an A-label cannot fire from inside B. -/
theorem no_a_label_in_B (A B : PathAlgebra) (I : Interface A B)
    (l : A.Label) (x : B.Carrier) (q : Pos A B) :
    ¬ Step A B I (.la l) (.inB x) q := by
  intro h; cases h

/-- Every well-typed step strictly worsens (given strict regions). -/
theorem step_worsens (A B : PathAlgebra) (I : Interface A B)
    (hA : StrictlyInflationary A) (hB : StrictlyInflationary B) :
    ∀ {l p q}, Step A B I l p q → CBetter A B p q := by
  intro l p q h
  cases h with
  | la => exact .aa (hA _ _)
  | lb => exact .bb (hB _ _)
  | cross => exact .ab

/-- Helper: a well-typed trace worsens-or-stays. -/
theorem trace_cbe (A B : PathAlgebra) (I : Interface A B)
    (hA : StrictlyInflationary A) (hB : StrictlyInflationary B) :
    ∀ {p ls q}, Trace A B I p ls q → CBetter A B p q ∨ p = q := by
  intro p ls q ht
  induction ht with
  | nil => exact Or.inr rfl
  | cons hstep _ ih =>
    have h1 := step_worsens A B I hA hB hstep
    cases ih with
    | inl h2 => exact Or.inl (ctrans A B h1 h2)
    | inr he => exact Or.inl (he ▸ h1)

/-- Headline: every well-typed NON-EMPTY trace strictly worsens. -/
theorem trace_worsens (A B : PathAlgebra) (I : Interface A B)
    (hA : StrictlyInflationary A) (hB : StrictlyInflationary B)
    {p q : Pos A B} {l : CLabel A B} {ls : List (CLabel A B)}
    (ht : Trace A B I p (l :: ls) q) : CBetter A B p q := by
  cases ht with
  | cons hstep htail =>
    have h1 := step_worsens A B I hA hB hstep
    cases trace_cbe A B I hA hB htail with
    | inl h2 => exact ctrans A B h1 h2
    | inr he => exact he ▸ h1

/-- Headline: a well-typed trace returning to its start is empty.
    No well-typed routing loop exists — by construction. -/
theorem wt_cycles_are_empty (A B : PathAlgebra) (I : Interface A B)
    (hA : StrictlyInflationary A) (hB : StrictlyInflationary B)
    {p : Pos A B} {ls : List (CLabel A B)}
    (ht : Trace A B I p ls p) : ls = [] := by
  cases ls with
  | nil => rfl
  | cons l ls =>
    exact absurd (trace_worsens A B I hA hB ht) (cirrefl A B p)

end Marches
