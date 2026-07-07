/-
  Marches — Kernel theorem (single region).

  If a path algebra is strictly inflationary, then running any
  non-empty word of labels strictly worsens the starting signature;
  in particular no non-empty word can return to its start.
  This is the algebraic core of loop-freedom.
-/

import Marches.Basic

namespace Marches

/-- Helper: running any word either strictly worsens or is the identity. -/
theorem run_le (A : PathAlgebra) (h : StrictlyInflationary A) :
    ∀ (ls : List A.Label) (a : A.Carrier),
      A.better a (run A ls a) ∨ run A ls a = a := by
  intro ls
  induction ls with
  | nil => intro a; exact Or.inr rfl
  | cons l ls ih =>
    intro a
    have h1 : A.better a (A.ext l a) := h l a
    cases ih (A.ext l a) with
    | inl h2 =>
      exact Or.inl (A.trans h1 (by simpa [run] using h2))
    | inr he =>
      exact Or.inl (by simpa [run, he] using h1)

/-- Kernel theorem: a non-empty word strictly worsens. -/
theorem run_worsens (A : PathAlgebra) (h : StrictlyInflationary A)
    (l : A.Label) (ls : List A.Label) (a : A.Carrier) :
    A.better a (run A (l :: ls) a) := by
  have h1 : A.better a (A.ext l a) := h l a
  cases run_le A h ls (A.ext l a) with
  | inl h2 => exact A.trans h1 (by simpa [run] using h2)
  | inr he => exact (by simpa [run, he] using h1)

/-- No non-empty word returns to its start: loop-freedom. -/
theorem no_return (A : PathAlgebra) (h : StrictlyInflationary A)
    (l : A.Label) (ls : List A.Label) (a : A.Carrier) :
    run A (l :: ls) a ≠ a := by
  intro he
  have hw := run_worsens A h l ls a
  rw [he] at hw
  exact A.irrefl a hw

end Marches
