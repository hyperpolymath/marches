{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-
  Marches — Typed region composition (Agda source of
  `Marches/Compose.lean`).

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
    • trace-worsens        : every well-typed non-empty trace strictly worsens.
    • wt-cycles-are-empty  : a well-typed trace that returns to its start
                             is empty — no well-typed routing loop exists.
    • no-back-cross, no-a-label-in-B : the ill-typed moves are underivable.
-}
module Marches.Compose where

open import Marches.Prelude
open import Marches.Basic

-- Positions of the composite system: inside A or inside B.
data Pos (A B : PathAlgebra) : Set where
  inA : Carrier A → Pos A B
  inB : Carrier B → Pos A B

-- Labels of the composite system: A-labels, B-labels, one crossing.
data CLabel (A B : PathAlgebra) : Set where
  la    : Label A → CLabel A B
  lb    : Label B → CLabel A B
  cross : CLabel A B

-- A typed interface: just the crossing morphism. Order-preservation of
-- `τ` is deliberately not required (rung 2; see the Lean file).
record Interface (A B : PathAlgebra) : Set where
  field
    τ : Carrier A → Carrier B

open Interface public

-- Stratified preference on the composite.
data CBetter (A B : PathAlgebra) : Pos A B → Pos A B → Set where
  aa : ∀ {x y} → better A x y → CBetter A B (inA x) (inA y)
  bb : ∀ {x y} → better B x y → CBetter A B (inB x) (inB y)
  ab : ∀ {x y} → CBetter A B (inA x) (inB y)

ctrans : (A B : PathAlgebra) → ∀ {p q r : Pos A B} →
  CBetter A B p q → CBetter A B q r → CBetter A B p r
ctrans A B (aa hxy) (aa hyz) = aa (trans A hxy hyz)
ctrans A B (aa hxy) ab       = ab
ctrans A B (bb hxy) (bb hyz) = bb (trans B hxy hyz)
ctrans A B ab       (bb _)   = ab

cirrefl : (A B : PathAlgebra) → ∀ (p : Pos A B) → ¬ CBetter A B p p
cirrefl A B (inA x) (aa h) = irrefl A x h
cirrefl A B (inB x) (bb h) = irrefl B x h

-- One well-typed step of the composite system.
data Step (A B : PathAlgebra) (I : Interface A B) :
    CLabel A B → Pos A B → Pos A B → Set where
  la    : ∀ {l x} → Step A B I (la l) (inA x) (inA (ext A l x))
  lb    : ∀ {l x} → Step A B I (lb l) (inB x) (inB (ext B l x))
  cross : ∀ {x}   → Step A B I cross  (inA x) (inB (τ I x))

-- Well-typed traces: the typing judgment on label words.
data Trace (A B : PathAlgebra) (I : Interface A B) :
    Pos A B → List (CLabel A B) → Pos A B → Set where
  nil  : ∀ {p} → Trace A B I p [] p
  cons : ∀ {p q r l ls} →
    Step A B I l p q → Trace A B I q ls r → Trace A B I p (l ∷ ls) r

-- Negative theorem: crossing back from B is unconstructible.
no-back-cross : (A B : PathAlgebra) (I : Interface A B)
  (x : Carrier B) (q : Pos A B) → ¬ Step A B I cross (inB x) q
no-back-cross A B I x q ()

-- Negative theorem: an A-label cannot fire from inside B.
no-a-label-in-B : (A B : PathAlgebra) (I : Interface A B)
  (l : Label A) (x : Carrier B) (q : Pos A B) → ¬ Step A B I (la l) (inB x) q
no-a-label-in-B A B I l x q ()

-- Every well-typed step strictly worsens (given strict regions).
step-worsens : (A B : PathAlgebra) (I : Interface A B) →
  StrictlyInflationary A → StrictlyInflationary B →
  ∀ {l p q} → Step A B I l p q → CBetter A B p q
step-worsens A B I hA hB (la {l} {x}) = aa (hA l x)
step-worsens A B I hA hB (lb {l} {x}) = bb (hB l x)
step-worsens A B I hA hB cross        = ab

-- Helper: a well-typed trace worsens-or-stays.
trace-cbe : (A B : PathAlgebra) (I : Interface A B) →
  StrictlyInflationary A → StrictlyInflationary B →
  ∀ {p ls q} → Trace A B I p ls q → CBetter A B p q ⊎ p ≡ q
trace-cbe A B I hA hB nil = inj₂ refl
trace-cbe A B I hA hB (cons hstep htail) with trace-cbe A B I hA hB htail
... | inj₁ h2 = inj₁ (ctrans A B (step-worsens A B I hA hB hstep) h2)
... | inj₂ he = inj₁ (subst (CBetter A B _) he (step-worsens A B I hA hB hstep))

-- Headline: every well-typed NON-EMPTY trace strictly worsens.
trace-worsens : (A B : PathAlgebra) (I : Interface A B) →
  StrictlyInflationary A → StrictlyInflationary B →
  ∀ {p q : Pos A B} {l : CLabel A B} {ls : List (CLabel A B)} →
  Trace A B I p (l ∷ ls) q → CBetter A B p q
trace-worsens A B I hA hB (cons hstep htail) with trace-cbe A B I hA hB htail
... | inj₁ h2 = ctrans A B (step-worsens A B I hA hB hstep) h2
... | inj₂ he = subst (CBetter A B _) he (step-worsens A B I hA hB hstep)

-- Headline: a well-typed trace returning to its start is empty.
-- No well-typed routing loop exists — by construction.
wt-cycles-are-empty : (A B : PathAlgebra) (I : Interface A B) →
  StrictlyInflationary A → StrictlyInflationary B →
  ∀ {p : Pos A B} {ls : List (CLabel A B)} →
  Trace A B I p ls p → ls ≡ []
wt-cycles-are-empty A B I hA hB {ls = []}    ht = refl
wt-cycles-are-empty A B I hA hB {p} {ls = l ∷ ls} ht =
  ⊥-elim (cirrefl A B p (trace-worsens A B I hA hB ht))
