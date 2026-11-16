{-# OPTIONS --safe #-}
-- Expected rejection: axiom K (every self-equality is refl) is not
-- provable without K. The pragma deliberately sets --safe alone, not
-- --without-K or --cubical-compatible (which implies it): Agda's default
-- has K, and this file checks without the gate's flags. So the refusal
-- comes from the gate's own command line, and shows that
-- scripts/check-agda.sh runs with --without-K in force.
-- expect: because K has been disabled
module UsesK where

open import Marches.Prelude

K : {X : Set} {x : X} (p : x ≡ x) → p ≡ refl
K refl = refl
