-- Expected rejection: axiom K (every self-equality is refl) is not
-- provable without K. This file deliberately has no OPTIONS pragma, so the
-- refusal comes from the gate's own command line: it shows that
-- scripts/check-agda.sh runs with --without-K in force.
-- expect: because K has been disabled
module UsesK where

open import Marches.Prelude

K : {X : Set} {x : X} (p : x ≡ x) → p ≡ refl
K refl = refl
