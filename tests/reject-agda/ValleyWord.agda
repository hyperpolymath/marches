{-# OPTIONS --safe --without-K --cubical-compatible #-}
-- Expected rejection: the word provider-then-customer is a valley, and the
-- typing judgment has no derivation for it. Offering the customer-arc
-- step for a route that is already a provider route must be refused,
-- which pins that `Marches.GRTrace.gtrace-iff-valley-free` excludes the
-- valley by construction.
-- expect: c != p
module ValleyWord where

open import Marches.Prelude
open import Marches.GaoRexford
open import Marches.GRTrace

valley : ∃ (λ t → GTrace c (fromProv ∷ fromCust ∷ []) t)
valley = c , cons provCust (cons custCust nil)
