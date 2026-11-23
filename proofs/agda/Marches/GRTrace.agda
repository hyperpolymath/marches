{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-
  Marches — Gao–Rexford wired into Trace, rung 1 (Agda source of
  `Marches/GRTrace.lean`, namespace `Marches.GR`).

  A step of route propagation is TYPED by (relationship, signature), and
  only the five legal moves are constructors of `GStep`. The ill-typed
  moves — re-exporting a provider- or peer-learned route upward (the
  valley), a second peer hop, any move from ⊥ — have NO constructor.

  Headlines:
    • gtrace-iff-valley-free : derivations of the typing judgment from `c`
      are EXACTLY the valley-free words Cust* Peer? Prov*.
    • valley-free-iff-gwalk  : the grammar coincides with non-⊥ evaluation
      of the rung-0 extension table `gext`.
    • no-valley-step, no-peer-reexport-up, no-second-peer,
      no-step-from-bot : the ill-typed moves are underivable.

  Nothing here is a convergence result; that is agda-routing's ground
  (see LIMITATIONS.adoc).
-}
module Marches.GRTrace where

open import Marches.Prelude
open import Marches.GaoRexford

-- One well-typed GR step: exactly the five non-⊥ entries of `gext`.
data GStep : Rel → Sig → Sig → Set where
  custCust : GStep fromCust c c
  peerCust : GStep fromPeer c r
  provCust : GStep fromProv c p
  provPeer : GStep fromProv r p
  provProv : GStep fromProv p p

-- Well-typed GR traces: the typing judgment on relationship words.
data GTrace : Sig → List Rel → Sig → Set where
  nil  : ∀ {s} → GTrace s [] s
  cons : ∀ {s t u rel ls} → GStep rel s t → GTrace t ls u → GTrace s (rel ∷ ls) u

-- Negative theorems: the ill-typed moves are underivable.

no-valley-step : (t : Sig) → ¬ GStep fromCust p t
no-valley-step t ()

no-peer-reexport-up : (t : Sig) → ¬ GStep fromCust r t
no-peer-reexport-up t ()

no-second-peer : (t : Sig) → ¬ GStep fromPeer r t
no-second-peer t ()

no-step-from-bot : (rel : Rel) (t : Sig) → ¬ GStep rel bot t
no-step-from-bot rel t ()

-- Agreement with the rung-0 extension table.

-- Soundness: a typed step lands exactly where `gext` says.
gstep-gext : ∀ {rel s t} → GStep rel s t → t ≡ gext rel s
gstep-gext custCust = refl
gstep-gext peerCust = refl
gstep-gext provCust = refl
gstep-gext provPeer = refl
gstep-gext provProv = refl

-- A typed step never produces ⊥.
gstep-target-ne-bot : ∀ {rel s t} → GStep rel s t → t ≢ bot
gstep-target-ne-bot custCust ()
gstep-target-ne-bot peerCust ()
gstep-target-ne-bot provCust ()
gstep-target-ne-bot provPeer ()
gstep-target-ne-bot provProv ()

-- Completeness: every non-⊥ entry of the table is a typed step.
gstep-complete : (rel : Rel) (s : Sig) → gext rel s ≢ bot → GStep rel s (gext rel s)
gstep-complete fromCust c   h = custCust
gstep-complete fromCust r   h = ⊥-elim (h refl)
gstep-complete fromCust p   h = ⊥-elim (h refl)
gstep-complete fromCust bot h = ⊥-elim (h refl)
gstep-complete fromPeer c   h = peerCust
gstep-complete fromPeer r   h = ⊥-elim (h refl)
gstep-complete fromPeer p   h = ⊥-elim (h refl)
gstep-complete fromPeer bot h = ⊥-elim (h refl)
gstep-complete fromProv c   h = provCust
gstep-complete fromProv r   h = provPeer
gstep-complete fromProv p   h = provProv
gstep-complete fromProv bot h = ⊥-elim (h refl)

-- Evaluate a relationship word through the table (the `run` of GR).
gwalk : List Rel → Sig → Sig
gwalk []         s = s
gwalk (rel ∷ ls) s = gwalk ls (gext rel s)

gext-bot : (rel : Rel) → gext rel bot ≡ bot
gext-bot fromCust = refl
gext-bot fromPeer = refl
gext-bot fromProv = refl

gwalk-bot : (ls : List Rel) → gwalk ls bot ≡ bot
gwalk-bot []         = refl
gwalk-bot (rel ∷ ls) = subst (λ x → gwalk ls x ≡ bot) (sym (gext-bot rel)) (gwalk-bot ls)

-- A derivation evaluates to what the table says.
gtrace-gwalk : ∀ {s ls t} → GTrace s ls t → gwalk ls s ≡ t
gtrace-gwalk nil                  = refl
gtrace-gwalk (cons custCust tl)   = gtrace-gwalk tl
gtrace-gwalk (cons peerCust tl)   = gtrace-gwalk tl
gtrace-gwalk (cons provCust tl)   = gtrace-gwalk tl
gtrace-gwalk (cons provPeer tl)   = gtrace-gwalk tl
gtrace-gwalk (cons provProv tl)   = gtrace-gwalk tl

-- Typed traces preserve non-⊥ness.
gtrace-target-ne-bot : ∀ {s ls t} → GTrace s ls t → s ≢ bot → t ≢ bot
gtrace-target-ne-bot nil           hs = hs
gtrace-target-ne-bot (cons st tl)  hs = gtrace-target-ne-bot tl (gstep-target-ne-bot st)

-- Non-⊥ evaluation yields a derivation.
gwalk-gtrace : (ls : List Rel) (s : Sig) → gwalk ls s ≢ bot → GTrace s ls (gwalk ls s)
gwalk-gtrace []         s h = nil
gwalk-gtrace (rel ∷ ls) s h = cons (gstep-complete rel s hne) (gwalk-gtrace ls (gext rel s) h)
  where
    hne : gext rel s ≢ bot
    hne hb = h (subst (λ x → gwalk ls x ≡ bot) (sym hb) (gwalk-bot ls))

-- Derivability from a live signature ⟺ non-⊥ evaluation.
gtrace-exists-iff : ∀ {s} → s ≢ bot → (ls : List Rel) →
  ∃ (λ t → GTrace s ls t) ↔ gwalk ls s ≢ bot
gtrace-exists-iff {s} hs ls = mk↔ to from
  where
    to : ∃ (λ t → GTrace s ls t) → gwalk ls s ≢ bot
    to (t , ht) = subst (λ x → x ≢ bot) (sym (gtrace-gwalk ht)) (gtrace-target-ne-bot ht hs)
    from : gwalk ls s ≢ bot → ∃ (λ t → GTrace s ls t)
    from h = gwalk ls s , gwalk-gtrace ls s h

-- The valley-freedom grammar: valid words are Cust* Peer? Prov*.

-- All-provider suffix: Prov*.
data Downhill : List Rel → Set where
  nil  : Downhill []
  cons : ∀ {ls} → Downhill ls → Downhill (fromProv ∷ ls)

-- The Gao–Rexford valley-free words: Cust* Peer? Prov*.
data ValleyFree : List Rel → Set where
  down : ∀ {ls} → Downhill ls → ValleyFree ls
  peer : ∀ {ls} → Downhill ls → ValleyFree (fromPeer ∷ ls)
  cust : ∀ {ls} → ValleyFree ls → ValleyFree (fromCust ∷ ls)

-- From `p` only Prov* continues.
gtrace-p-downhill : ∀ {ls t} → GTrace p ls t → Downhill ls
gtrace-p-downhill nil                = nil
gtrace-p-downhill (cons provProv tl) = cons (gtrace-p-downhill tl)

-- From `r` only Prov* continues.
gtrace-r-downhill : ∀ {ls t} → GTrace r ls t → Downhill ls
gtrace-r-downhill nil                = nil
gtrace-r-downhill (cons provPeer tl) = cons (gtrace-p-downhill tl)

-- Every derivation from `c` is a valley-free word.
gtrace-valley-free : ∀ {ls t} → GTrace c ls t → ValleyFree ls
gtrace-valley-free nil                = down nil
gtrace-valley-free (cons custCust tl) = cust (gtrace-valley-free tl)
gtrace-valley-free (cons peerCust tl) = peer (gtrace-r-downhill tl)
gtrace-valley-free (cons provCust tl) = down (cons (gtrace-p-downhill tl))

downhill-gtrace-p : ∀ {ls} → Downhill ls → GTrace p ls p
downhill-gtrace-p nil      = nil
downhill-gtrace-p (cons h) = cons provProv (downhill-gtrace-p h)

downhill-gtrace-r : ∀ {ls} → Downhill ls → ∃ (λ t → GTrace r ls t)
downhill-gtrace-r nil      = r , nil
downhill-gtrace-r (cons h) = p , cons provPeer (downhill-gtrace-p h)

-- Every valley-free word is derivable from `c`.
valley-free-gtrace : ∀ {ls} → ValleyFree ls → ∃ (λ t → GTrace c ls t)
valley-free-gtrace (down nil)      = c , nil
valley-free-gtrace (down (cons h)) = p , cons provCust (downhill-gtrace-p h)
valley-free-gtrace (peer hd) with downhill-gtrace-r hd
... | t , ht = t , cons peerCust ht
valley-free-gtrace (cust v) with valley-free-gtrace v
... | t , ht = t , cons custCust ht

-- HEADLINE: the typing judgment from `c` IS the valley-freedom grammar.
gtrace-iff-valley-free : (ls : List Rel) → ∃ (λ t → GTrace c ls t) ↔ ValleyFree ls
gtrace-iff-valley-free ls = mk↔ (λ { (t , ht) → gtrace-valley-free ht }) valley-free-gtrace

-- Corollary: grammar ⟺ non-⊥ evaluation of the rung-0 table.
valley-free-iff-gwalk : (ls : List Rel) → ValleyFree ls ↔ gwalk ls c ≢ bot
valley-free-iff-gwalk ls =
  ↔-trans (↔-sym (gtrace-iff-valley-free ls)) (gtrace-exists-iff (λ ()) ls)
