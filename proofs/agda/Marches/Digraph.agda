{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-
  Marches — Digraphs: paths and acyclicity (Agda source of
  `Marches/Digraph.lean`).

  The explicit acyclicity hypothesis, shared by the customer→provider
  hierarchy (`GRHierarchy`) and the region DAG (`Reassembly`): both consume
  ONE definition, `Acyclic`. Acyclicity is never proven here for any real
  structure; it is the hypothesis threaded through every conditional
  loop-freedom theorem, and it stays ASSUMED (falsifier F5).
-}
module Marches.Digraph where

open import Marches.Prelude

-- Non-empty paths in a relation `R`.
data RPath {V : Set} (R : V → V → Set) : V → V → Set where
  single : ∀ {u v}   → R u v → RPath R u v
  cons   : ∀ {u v w} → R u v → RPath R v w → RPath R u w

-- Lean's `RPath.snoc`: extend a path by one arc on the right.
rpath-snoc : ∀ {V : Set} {R : V → V → Set} {u v w} → RPath R u v → R v w → RPath R u w
rpath-snoc (single h1)  h2 = cons h1 (single h2)
rpath-snoc (cons h1 p)  h2 = cons h1 (rpath-snoc p h2)

-- Lean's `RPath.trans`: paths concatenate.
rpath-trans : ∀ {V : Set} {R : V → V → Set} {u v w} → RPath R u v → RPath R v w → RPath R u w
rpath-trans (single h1) p2 = cons h1 p2
rpath-trans (cons h1 p) p2 = cons h1 (rpath-trans p p2)

-- Lean's `RPath.flip`: a path in the reversed relation reverses into a path.
rpath-flip : ∀ {V : Set} {R : V → V → Set} {u v} → RPath (λ a b → R b a) u v → RPath R v u
rpath-flip (single h1) = single h1
rpath-flip (cons h1 p) = rpath-snoc (rpath-flip p) h1

-- Acyclicity: no non-empty cycle. Never proven here for any real structure.
Acyclic : ∀ {V : Set} → (V → V → Set) → Set
Acyclic {V} R = ∀ (v : V) → ¬ RPath R v v
