{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-
  Marches — the acyclic customer→provider hierarchy, made explicit, rung 1
  (Agda source of `Marches/GRHierarchy.lean`, namespace `Marches.GR`).

  Gao–Rexford stability classically ASSUMES the customer→provider digraph
  is acyclic; the algebra alone cannot supply it (`gr-not-strict`). This
  module names that assumption as an explicit hypothesis, `Acyclic` from
  `Digraph`, and derives loop-freedom UNDER it.

  Headline:
    • gr-loop-free : over any topology whose customer→provider hierarchy
      is acyclic, a well-typed trace returning to the same
      (node, signature) state is empty.

  State-level loop-freedom of well-typed traces is NOT protocol
  convergence; that is agda-routing's ground (see LIMITATIONS.adoc).
-}
module Marches.GRHierarchy where

open import Marches.Prelude
open import Marches.Digraph
open import Marches.GaoRexford
open import Marches.GRTrace

-- An AS-level topology: `custOf u v` reads "u is a customer of v";
-- `peerOf u v` reads "u and v peer" (directed as used).
record Topo (V : Set) : Set₁ where
  field
    custOf : V → V → Set
    peerOf : V → V → Set

open Topo public

-- One node-level well-typed step, labelled at the RECEIVER `v`.
data NStep {V : Set} (T : Topo V) : Rel → V × Sig → V × Sig → Set where
  cust : ∀ {u v s t} → custOf T u v → GStep fromCust s t → NStep T fromCust (u , s) (v , t)
  peer : ∀ {u v s t} → peerOf T u v → GStep fromPeer s t → NStep T fromPeer (u , s) (v , t)
  prov : ∀ {u v s t} → custOf T v u → GStep fromProv s t → NStep T fromProv (u , s) (v , t)

-- Well-typed node-level traces.
data NTrace {V : Set} (T : Topo V) : V × Sig → List Rel → V × Sig → Set where
  nil  : ∀ {ps} → NTrace T ps [] ps
  cons : ∀ {ps qt ru rel ls} → NStep T rel ps qt → NTrace T qt ls ru → NTrace T ps (rel ∷ ls) ru

module _ {V : Set} {T : Topo V} where

  -- Every node-level step carries a signature-level step.
  nstep-gstep : ∀ {rel ps qt} → NStep T rel ps qt → GStep rel (proj₂ ps) (proj₂ qt)
  nstep-gstep (cust _ hg) = hg
  nstep-gstep (peer _ hg) = hg
  nstep-gstep (prov _ hg) = hg

  -- Node-level traces project to the typing judgment of GRTrace.
  ntrace-gtrace : ∀ {ps ls qt} → NTrace T ps ls qt → GTrace (proj₂ ps) ls (proj₂ qt)
  ntrace-gtrace nil         = nil
  ntrace-gtrace (cons st h) = cons (nstep-gstep st) (ntrace-gtrace h)

  -- Every node-level trace of a customer route is a valley-free word.
  ntrace-valley-free : ∀ {u v t ls} → NTrace T (u , c) ls (v , t) → ValleyFree ls
  ntrace-valley-free h = gtrace-valley-free (ntrace-gtrace h)

-- Rank monotonicity.

gstep-rank-le : ∀ {rel s t} → GStep rel s t → rank s ≤ rank t
gstep-rank-le custCust = refl
gstep-rank-le peerCust = step refl
gstep-rank-le provCust = step (step refl)
gstep-rank-le provPeer = step refl
gstep-rank-le provProv = refl

module _ {V : Set} {T : Topo V} where

  nstep-rank-le : ∀ {rel ps qt} → NStep T rel ps qt → rank (proj₂ ps) ≤ rank (proj₂ qt)
  nstep-rank-le st = gstep-rank-le (nstep-gstep st)

  ntrace-rank-le : ∀ {ps ls qt} → NTrace T ps ls qt → rank (proj₂ ps) ≤ rank (proj₂ qt)
  ntrace-rank-le nil         = refl
  ntrace-rank-le (cons st h) = ≤-trans (nstep-rank-le st) (ntrace-rank-le h)

  -- Rank-flat traces are hierarchy chains.

  private
    r≰c : ¬ (rank r ≤ rank c)
    r≰c ()
    p≰c : ¬ (rank p ≤ rank c)
    p≰c ()
    p≰r : ¬ (rank p ≤ rank r)
    p≰r (step ())

  -- A non-empty `c`-to-`c` trace is a chain in the customer→provider
  -- hierarchy.
  trace-c-path : ∀ {ls u v} → NTrace T (u , c) ls (v , c) → ls ≢ [] → RPath (custOf T) u v
  trace-c-path nil                                   hne = ⊥-elim (hne refl)
  trace-c-path (cons (cust harc custCust) nil)        _   = single harc
  trace-c-path (cons (cust harc custCust) (cons st h)) _  = cons harc (trace-c-path (cons st h) (λ ()))
  trace-c-path (cons (peer _ peerCust) h)             _   = ⊥-elim (r≰c (ntrace-rank-le h))
  trace-c-path (cons (prov _ provCust) h)             _   = ⊥-elim (p≰c (ntrace-rank-le h))

  -- A non-empty `p`-to-`p` trace is a provider chain: a path in the
  -- REVERSED hierarchy.
  trace-p-path : ∀ {ls u v} → NTrace T (u , p) ls (v , p) → ls ≢ [] →
    RPath (λ a b → custOf T b a) u v
  trace-p-path nil                                    hne = ⊥-elim (hne refl)
  trace-p-path (cons (prov harc provProv) nil)         _   = single harc
  trace-p-path (cons (prov harc provProv) (cons st h)) _   = cons harc (trace-p-path (cons st h) (λ ()))

  -- HEADLINE: loop-freedom for Gao–Rexford, UNDER the explicit acyclicity
  -- hypothesis. Not a convergence theorem; the hypothesis stays ASSUMED
  -- about real topologies, as in Gao–Rexford 2001.
  gr-loop-free : Acyclic (custOf T) → ∀ {v s ls} → NTrace T (v , s) ls (v , s) → ls ≡ []
  gr-loop-free hacyc {ls = []}    h = refl
  gr-loop-free hacyc {v} {c}   {ls = _ ∷ _} h = ⊥-elim (hacyc v (trace-c-path h (λ ())))
  gr-loop-free hacyc {v} {p}   {ls = _ ∷ _} h = ⊥-elim (hacyc v (rpath-flip (trace-p-path h (λ ()))))
  gr-loop-free hacyc {v} {r}   {ls = _ ∷ _} (cons (prov _ provPeer) h) = ⊥-elim (p≰r (ntrace-rank-le h))
  gr-loop-free hacyc {v} {bot} {ls = _ ∷ _} (cons (cust _ ()) _)
  gr-loop-free hacyc {v} {bot} {ls = _ ∷ _} (cons (peer _ ()) _)
  gr-loop-free hacyc {v} {bot} {ls = _ ∷ _} (cons (prov _ ()) _)
