{-# OPTIONS --safe --without-K --cubical-compatible #-}
-- Expected rejection: a crossing fired from B back into A has no
-- constructor, so no term of that step type can be written. The `cross`
-- constructor only starts in A; offering it for a start in B must be
-- refused. This pins that `Marches.Compose.no-back-cross` is a fact about
-- the typing judgment, not a vacuous negation.
-- expect: != inB x of type Pos A B
module BackCross where

open import Marches.Prelude
open import Marches.Basic
open import Marches.Compose

back : (A B : PathAlgebra) (I : Interface A B) (x : Carrier B) (y : Carrier A) →
  Step A B I cross (inB x) (inA y)
back A B I x y = cross
