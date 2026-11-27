{-# OPTIONS --safe --without-K --cubical-compatible #-}
-- Expected rejection: reassembly needs the acyclicity hypothesis. Two
-- tropical regions with an edge each way (`a ≡ not b`) have the cycle
-- false → true → false, and the composite judgment derives a non-empty
-- trace from `(false , 0)` back to itself (`two-cycle`). Composing that
-- system and applying `compose-no-loop` to the trace would prove `⊥`.
-- `compose` refuses the system, because no acyclicity proof is supplied:
-- the file must be rejected where `compose` is used as a discipline. If
-- `compose` or `compose-no-loop` stopped asking for `Acyclic`, this file
-- would check and prove `⊥`, and the gate would fail. This pins that
-- `Acyclic` is load-bearing in `Marches.Reassembly.compose`.
-- expect: → Discipline !=< Discipline
module CyclicRegions where

open import Marches.Prelude
open import Marches.Digraph
open import Marches.Tropical
open import Marches.Reassembly

bothWays : Bool → Bool → Set
bothWays a b = a ≡ not b

cyc : DiscSys
cyc = record
  { R = Bool
  ; E = bothWays
  ; D = λ _ → toDiscipline TropicalNat tropical-strict
  ; τ = λ _ x → x
  }

cycComposed : Discipline
cycComposed = compose cyc bool-set

two-cycle : Trace cycComposed (false , 0) (cross false true refl ∷ cross true false refl ∷ []) (false , 0)
two-cycle = cons (scross refl) (cons (scross refl) nil)

boom : ⊥
boom with compose-no-loop cyc bool-set two-cycle
... | ()
