{-# OPTIONS --safe --without-K --cubical-compatible #-}
-- Expected rejection: without K, composite irreflexivity needs the region
-- index to be a set (residual R5). Lean proves `DiscSys.birrefl` from
-- acyclicity alone by matching `Better ⟨r, x⟩ ⟨r, x⟩` directly. The same
-- match in Agda must eliminate the reflexive equation `r = r`, which is K,
-- so it must be refused. This pins that the `IsSet` hypothesis of
-- `Marches.Reassembly.c-birrefl` is not decoration.
-- expect: Cannot eliminate reflexive equation r = r of type DiscSys.R S because K has been disabled
module ReflexiveRegion where

open import Marches.Prelude
open import Marches.Digraph
open import Marches.Reassembly

module _ (S : DiscSys) where
  open DiscSys S

  irr : Acyclic E → ∀ p → ¬ CBetter S p p
  irr hacyc (r , x) (loc a)   = Discipline.birrefl (D r) x a
  irr hacyc (r , x) (cross e) = hacyc r e
