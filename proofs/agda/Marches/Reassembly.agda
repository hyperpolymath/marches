{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-
  Marches — n regions and reassembly (Agda source of
  `Marches/Reassembly.lean`, rung 2).

  A `Discipline` abstracts the invariant every Marches system shares: a
  strict preference order and a typed step judgment whose every step
  strictly worsens. The worsening obligation is a field, so a Discipline
  is a system in which that obligation is already discharged.
  Loop-freedom is then proven once, generically (`no-loop`).

  The kernel is an instance (`toDiscipline`). The headline is closure
  under composition: a finite acyclic DAG of disciplines is itself a
  discipline (`Composite.compose`). The composite worsening obligation is
  discharged from the componentwise ones and the stratification of the
  DAG, with no global re-proof. Because `compose` returns a `Discipline`,
  a composite may itself be a region of a larger system: reassembly is
  closure, not a one-shot.

  One hypothesis is explicit here and not in Lean: the region index is a
  set (`IsSet`). Lean's equality has proof irrelevance by definition, so
  every Lean type is a set and Lean needs no such hypothesis. Without K
  the composite order is irreflexive only when it holds; see residual R5
  in `docs/agda-lean-correspondence.adoc`.

  Delimitation unchanged: loop-freedom of the typed judgment is NOT
  protocol convergence. Mechanised convergence for policy-rich routing is
  agda-routing's ground (Daggitt–Griffin); see LIMITATIONS.adoc.
-}
module Marches.Reassembly where

open import Marches.Prelude
open import Marches.Basic
open import Marches.Digraph
open import Marches.Tropical

-- A routing discipline: positions with a strict preference order and a
-- typed step judgment whose every step strictly worsens.
record Discipline : Set₁ where
  field
    Pos          : Set
    Lab          : Set
    Better       : Pos → Pos → Set
    Step         : Lab → Pos → Pos → Set
    btrans       : ∀ {p q r} → Better p q → Better q r → Better p r
    birrefl      : ∀ p → ¬ Better p p
    step-worsens : ∀ {l p q} → Step l p q → Better p q

open Discipline

-- Well-typed traces of a discipline.
data Trace (D : Discipline) : Pos D → List (Lab D) → Pos D → Set where
  nil  : ∀ {p} → Trace D p [] p
  cons : ∀ {p q r l ls} → Step D l p q → Trace D q ls r → Trace D p (l ∷ ls) r

-- A well-typed trace worsens or stays.
trace-ge : (D : Discipline) → ∀ {p ls q} → Trace D p ls q → Better D p q ⊎ p ≡ q
trace-ge D nil = inj₂ refl
trace-ge D (cons hs ht) with trace-ge D ht
... | inj₁ h2 = inj₁ (btrans D (step-worsens D hs) h2)
... | inj₂ he = inj₁ (subst (Better D _) he (step-worsens D hs))

-- Every well-typed non-empty trace strictly worsens.
trace-worsens : (D : Discipline) → ∀ {p q l ls} → Trace D p (l ∷ ls) q → Better D p q
trace-worsens D (cons hs ht) with trace-ge D ht
... | inj₁ h2 = btrans D (step-worsens D hs) h2
... | inj₂ he = subst (Better D _) he (step-worsens D hs)

-- Loop-freedom, once and for all: a well-typed trace returning to its
-- start is empty.
no-loop : (D : Discipline) → ∀ {p ls} → Trace D p ls p → ls ≡ []
no-loop D {ls = []}    ht = refl
no-loop D {p} {_ ∷ _} ht = ⊥-elim (birrefl D p (trace-worsens D ht))

-- Every strictly inflationary path algebra is a discipline; the strictness
-- hypothesis is consumed here, explicitly.
toDiscipline : (A : PathAlgebra) → StrictlyInflationary A → Discipline
toDiscipline A h = record
  { Pos          = Carrier A
  ; Lab          = Label A
  ; Better       = better A
  ; Step         = λ l p q → q ≡ ext A l p
  ; btrans       = trans A
  ; birrefl      = irrefl A
  ; step-worsens = λ {l} {p} hq → subst (better A p) (sym hq) (h l p)
  }

-- Sanity: single-region loop-freedom recovered from the generic theorem.
toDiscipline-no-loop : (A : PathAlgebra) (h : StrictlyInflationary A) →
  ∀ {a ls} → Trace (toDiscipline A h) a ls a → ls ≡ []
toDiscipline-no-loop A h ht = no-loop (toDiscipline A h) ht

------------------------------------------------------------------------
-- The region DAG

-- A finite DAG of disciplines: regions `R`, an edge relation `E`, a
-- discipline per region, and a crossing map along each edge.
-- (Order-preservation of the crossing maps is NOT required.)
record DiscSys : Set₁ where
  field
    R : Set
    E : R → R → Set
    D : R → Discipline
    τ : ∀ {r r'} → E r r' → Pos (D r) → Pos (D r')

-- Lean's namespace `DiscSys`, for one system `S`.
module Composite (S : DiscSys) where
  open DiscSys S

  -- Composite position: a local position tagged by its region.
  CPos : Set
  CPos = Σ R (λ r → Pos (D r))

  -- Stratified composite preference: local within a region; across
  -- regions, anything strictly upstream in the DAG beats anything
  -- downstream.
  data CBetter : CPos → CPos → Set where
    loc   : ∀ {r x y} → Better (D r) x y → CBetter (r , x) (r , y)
    cross : ∀ {r r' x y} → RPath E r r' → CBetter (r , x) (r' , y)

  -- Composite labels: a region's own label, or a crossing along an edge.
  data CLab : Set where
    loc   : (r : R) → Lab (D r) → CLab
    cross : (r r' : R) → E r r' → CLab

  -- One well-typed composite step.
  data CStep : CLab → CPos → CPos → Set where
    sloc   : ∀ {r l x y} → Step (D r) l x y → CStep (loc r l) (r , x) (r , y)
    scross : ∀ {r r'} (e : E r r') {x} → CStep (cross r r' e) (r , x) (r' , τ e x)

  -- Composite preference is transitive (no acyclicity needed).
  c-btrans : ∀ {p q s} → CBetter p q → CBetter q s → CBetter p s
  c-btrans (loc a)    (loc b)    = loc (btrans (D _) a b)
  c-btrans (loc a)    (cross e)  = cross e
  c-btrans (cross e1) (loc b)    = cross e1
  c-btrans (cross e1) (cross e2) = cross (rpath-trans e1 e2)

  -- The second components of equal pairs agree, after transport along
  -- the equation of first components. Only J is used.
  snd-transport : ∀ {u v : CPos} (e : u ≡ v) →
    subst (λ r → Pos (D r)) (cong proj₁ e) (proj₂ u) ≡ proj₂ v
  snd-transport refl = refl

  -- Irreflexivity, stated for any two equal positions so that no
  -- reflexive equation has to be eliminated.
  c-birrefl-≡ : IsSet R → Acyclic E → ∀ {p q} → CBetter p q → p ≡ q → ⊥
  c-birrefl-≡ hset hacyc {r , x} {.r , y} (loc a) e =
    birrefl (D r) x (subst (Better (D r) x) (sym x≡y) a)
    where
      x≡y : x ≡ y
      x≡y = ≡-trans (sym (cong (λ ℓ → subst (λ r → Pos (D r)) ℓ x) (hset (cong proj₁ e) refl)))
                    (snd-transport e)
  c-birrefl-≡ hset hacyc {r , x} {r' , y} (cross pth) e =
    hacyc r (subst (RPath E r) (sym (cong proj₁ e)) pth)

  -- Composite preference is irreflexive because the DAG is acyclic (and,
  -- without K, because the region index is a set: residual R5).
  c-birrefl : IsSet R → Acyclic E → ∀ p → ¬ CBetter p p
  c-birrefl hset hacyc p h = c-birrefl-≡ hset hacyc h refl

  -- Every well-typed composite step strictly worsens: discharged from the
  -- componentwise obligations (`sloc`) and DAG stratification (`scross`).
  cstep-worsens : ∀ {l p q} → CStep l p q → CBetter p q
  cstep-worsens (sloc hs)  = loc (step-worsens (D _) hs)
  cstep-worsens (scross e) = cross (single e)

  -- Negative theorems: the ill-typed n-region moves are underivable.

  -- A region's own label cannot fire from a different region.
  no-foreign-local : ∀ {r r'} → r ≢ r' →
    ∀ {l : Lab (D r)} {x : Pos (D r')} {q} → ¬ CStep (loc r l) (r' , x) q
  no-foreign-local hne (sloc _) = hne refl

  -- Under acyclicity, no region crosses to itself.
  no-self-cross : Acyclic E → ∀ {r} → E r r → ⊥
  no-self-cross hacyc {r} e = hacyc r (single e)

  -- THE reassembly theorem: a finite acyclic DAG of disciplines is itself
  -- a discipline. The result has exactly the type `DiscSys.D` consumes, so
  -- composites nest.
  compose : IsSet R → Acyclic E → Discipline
  compose hset hacyc = record
    { Pos          = CPos
    ; Lab          = CLab
    ; Better       = CBetter
    ; Step         = CStep
    ; btrans       = c-btrans
    ; birrefl      = c-birrefl hset hacyc
    ; step-worsens = cstep-worsens
    }

  -- Composite loop-freedom, as a corollary of the generic theorem. Not a
  -- convergence result: agda-routing owns that ground.
  compose-no-loop : (hset : IsSet R) (hacyc : Acyclic E) →
    ∀ {p ls} → Trace (compose hset hacyc) p ls p → ls ≡ []
  compose-no-loop hset hacyc ht = no-loop (compose hset hacyc) ht

open Composite public

------------------------------------------------------------------------
-- Concrete exhibit and reassembly demonstration (Lean namespace
-- `Marches.Reassembly`).

-- The "up" edge on Bool: false → true, nothing else.
boolUp : Bool → Bool → Set
boolUp a b = (a ≡ false) × (b ≡ true)

-- Every boolUp path runs false → true, and no further.
boolUp-path : ∀ {a b} → RPath boolUp a b → (a ≡ false) × (b ≡ true)
boolUp-path (single e) = e
boolUp-path (cons (_ , refl) p) with boolUp-path p
... | () , _

boolUp-acyclic : Acyclic boolUp
boolUp-acyclic v h with boolUp-path h
... | refl , ()

-- Bool is a set. (In Lean this needs no statement.)
bool-set : IsSet Bool
bool-set {false} {false} refl refl = refl
bool-set {true}  {true}  refl refl = refl

-- A concrete two-region system: two tropical regions joined by a single
-- DAG edge, crossing by identity on costs.
twoTropical : DiscSys
twoTropical = record
  { R = Bool
  ; E = boolUp
  ; D = λ _ → toDiscipline TropicalNat tropical-strict
  ; τ = λ _ x → x
  }

-- The composite is a discipline; its loop-freedom is `no-loop`.
twoTropicalComposed : Discipline
twoTropicalComposed = compose twoTropical bool-set boolUp-acyclic

-- REASSEMBLY: a composite discipline used as a region inside another
-- system.
nested : DiscSys
nested = record
  { R = Bool
  ; E = boolUp
  ; D = λ _ → twoTropicalComposed
  ; τ = λ _ x → x
  }

-- A composite of composites: reassembly demonstrated concretely.
nestedComposed : Discipline
nestedComposed = compose nested bool-set boolUp-acyclic

-- Closure at the type level (Lean's anonymous `example`).
_ : (S : DiscSys) → IsSet (DiscSys.R S) → Acyclic (DiscSys.E S) → Discipline
_ = compose
