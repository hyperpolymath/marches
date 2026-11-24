{-# OPTIONS --safe --without-K --cubical-compatible #-}
-- Expected rejection: reassembly needs the acyclicity hypothesis. Two
-- regions with an edge each way (`a ≡ not b`) have the cycle
-- false → true → false. Claiming that no path returns to `false` must be
-- refused: the edge true → false is there, so its equation is inhabited.
-- With `boolUp` (false → true only) the matching clauses are accepted. This
-- pins that `Acyclic` is load-bearing in `Marches.Reassembly.compose`.
-- expect: true ≡ not false should be empty
module CyclicRegions where

open import Marches.Prelude
open import Marches.Digraph

bothWays : Bool → Bool → Set
bothWays a b = a ≡ not b

no-return : ¬ RPath bothWays false false
no-return (single ())
no-return (cons {v = false} () _)
no-return (cons {v = true} refl (single ()))
