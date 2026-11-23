{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-
  Marches — Gao–Rexford finite exhibit (Agda source of
  `Marches/GaoRexford.lean`, namespace `Marches.GR`).

  The classical commercial-relationship algebra: route signatures
  {customer-route c, peer-route r, provider-route p, invalid ⊥} with
  extension over the three arc relationships (route learned FROM a
  customer / peer / provider), encoding the standard export rules:
    • a customer exports only its customer routes upward;
    • a peer exports only its customer routes sideways;
    • a provider exports everything downward.

  Facts, each by case analysis over the finite tables:
    • gr-inflationary : extension NEVER improves.
    • gr-not-strict   : extension is NOT strictly worsening — the
                        (fromCust, c) fixed point. Gao–Rexford convergence
                        needs the ASSUMED acyclicity of the
                        customer→provider hierarchy on top of the algebra.
    • valley-dies     : re-exporting a provider-learned route upward is
                        typed to ⊥.
-}
module Marches.GaoRexford where

open import Marches.Prelude

data Sig : Set where
  c r p bot : Sig

data Rel : Set where
  fromCust fromPeer fromProv : Rel

rank : Sig → ℕ
rank c   = 0
rank r   = 1
rank p   = 2
rank bot = 3

-- Extension table encoding Gao–Rexford export rules (all twelve cases,
-- as in the Lean file).
gext : Rel → Sig → Sig
gext fromCust c   = c
gext fromCust r   = bot
gext fromCust p   = bot
gext fromCust bot = bot
gext fromPeer c   = r
gext fromPeer r   = bot
gext fromPeer p   = bot
gext fromPeer bot = bot
gext fromProv c   = p
gext fromProv r   = p
gext fromProv p   = p
gext fromProv bot = bot

-- Extension never improves (12 cases). Each clause refutes
-- `rank (gext l s) < rank s` by exhausting the order's constructors: the
-- depth of `step` is `rank s`, after which no constructor fits.
gr-inflationary : ∀ (l : Rel) (s : Sig) → ¬ (rank (gext l s) < rank s)
gr-inflationary fromCust c   ()
gr-inflationary fromCust r   (step ())
gr-inflationary fromCust p   (step (step ()))
gr-inflationary fromCust bot (step (step (step ())))
gr-inflationary fromPeer c   ()
gr-inflationary fromPeer r   (step ())
gr-inflationary fromPeer p   (step (step ()))
gr-inflationary fromPeer bot (step (step (step ())))
gr-inflationary fromProv c   ()
gr-inflationary fromProv r   (step ())
gr-inflationary fromProv p   (step (step ()))
gr-inflationary fromProv bot (step (step (step ())))

-- Extension is NOT strictly worsening: witness (fromCust, c).
gr-not-strict : ¬ (∀ (l : Rel) (s : Sig) → rank s < rank (gext l s))
gr-not-strict h with h fromCust c
... | ()

-- The valley dies at the type level: provider-learned then exported
-- upward over a customer arc is ⊥.
valley-dies : gext fromCust (gext fromProv c) ≡ bot
valley-dies = refl

-- Peer-learned routes likewise never travel upward.
peer-route-not-upward : gext fromCust (gext fromPeer c) ≡ bot
peer-route-not-upward = refl
