{-# OPTIONS --safe --without-K --cubical-compatible #-}
-- Expected rejection: loop-freedom needs the acyclicity hypothesis. Over a
-- one-node topology whose node is its own customer, the customer-arc step
-- from `(tt , c)` back to `(tt , c)` exists, so a returning trace is not
-- empty. Claiming that no such step can start the trace must be refused:
-- the step `custCust` is there. This pins that `Acyclic` is load-bearing in
-- `Marches.GRHierarchy.gr-loop-free` (falsifier F5).
-- expect: custCust
module SelfLoopReturns where

open import Marches.Prelude
open import Marches.GaoRexford
open import Marches.GRTrace
open import Marches.GRHierarchy

self : Topo ⊤
self = record { custOf = λ _ _ → ⊤ ; peerOf = λ _ _ → ⊥ }

no-loop : ∀ {ls} → NTrace self (tt , c) ls (tt , c) → ls ≡ []
no-loop nil                     = refl
no-loop (cons (cust _ ()) _)
no-loop (cons (peer () _) _)
no-loop (cons (prov _ ()) _)
