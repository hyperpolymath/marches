{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-
  Marches — the little logic the Agda development needs.

  No standard library: the import cone is this repository plus the
  modules Agda ships (Agda.Primitive, Agda.Builtin.*), in step with the
  Lean development, which uses core Lean and no Mathlib. Every
  definition here is the textbook one.
-}
module Marches.Prelude where

open import Agda.Builtin.Equality public using (_≡_; refl)
open import Agda.Builtin.List     public using (List; []; _∷_)

infix  3 ¬_
infixr 1 _⊎_

-- The empty type, and negation as a map into it.
data ⊥ : Set where

¬_ : Set → Set
¬ P = P → ⊥

-- Disjunction (Lean's `Or`).
data _⊎_ (P Q : Set) : Set where
  inj₁ : P → P ⊎ Q
  inj₂ : Q → P ⊎ Q

sym : {X : Set} {x y : X} → x ≡ y → y ≡ x
sym refl = refl

subst : {X : Set} (P : X → Set) {x y : X} → x ≡ y → P x → P y
subst P refl px = px

⊥-elim : {X : Set} → ⊥ → X
⊥-elim ()

-- Natural numbers and their order, defined as Lean's core library defines
-- them: `Nat.le` has the constructors `refl : n ≤ n` and
-- `step : n ≤ m → n ≤ m + 1`, and `n < m` is `n + 1 ≤ m`.
open import Agda.Builtin.Nat public using (zero; suc) renaming (Nat to ℕ)

infix 4 _≤_ _<_

data _≤_ (n : ℕ) : ℕ → Set where
  refl : n ≤ n
  step : ∀ {m} → n ≤ m → n ≤ suc m

_<_ : ℕ → ℕ → Set
n < m = suc n ≤ m

-- Inequality (Lean's `≠`: `a ≠ b` is `a = b → False`).
infix 4 _≢_
_≢_ : {X : Set} → X → X → Set
x ≢ y = ¬ (x ≡ y)

-- Dependent pairs, the counterpart of Lean's `∃` (residual R1: Lean's `∃`
-- is a `Prop`, this is a type with its witness inside).
infixr 4 _,_
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

∃ : {A : Set} → (A → Set) → Set
∃ {A} B = Σ A B

-- Logical equivalence, with Lean's field names for `Iff`.
infix 3 _↔_
record _↔_ (P Q : Set) : Set where
  constructor mk↔
  field
    mp  : P → Q
    mpr : Q → P

open _↔_ public

↔-sym : {P Q : Set} → P ↔ Q → Q ↔ P
↔-sym e = mk↔ (mpr e) (mp e)

↔-trans : {P Q R : Set} → P ↔ Q → Q ↔ R → P ↔ R
↔-trans e f = mk↔ (λ x → mp f (mp e x)) (λ z → mpr e (mpr f z))

-- Non-dependent pairs (Lean's `Prod`, with `.1` and `.2` as `proj₁` and
-- `proj₂`).
infixr 2 _×_
_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

-- The order is transitive (Lean's `Nat.le_trans`), by induction on the
-- second proof, as `Nat.le` is defined.
≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
≤-trans p refl     = p
≤-trans p (step q) = step (≤-trans p q)

-- The unit type (Lean's `Unit`, a structure with one constructor).
record ⊤ : Set where
  constructor tt

-- Booleans (Lean's `Bool`) and negation (Lean's `!`, which is `not`).
open import Agda.Builtin.Bool public using (Bool; true; false)

not : Bool → Bool
not true  = false
not false = true

-- Addition as core Lean defines `Nat.add`: by recursion on the SECOND
-- argument (`a + 0 = a`, `a + (b + 1) = (a + b) + 1`), so `a + (w + 1)`
-- reduces as it does in Lean.
infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
a + zero  = a
a + suc b = suc (a + b)

cong : {X Y : Set} (f : X → Y) {x y : X} → x ≡ y → f x ≡ f y
cong f refl = refl

if_then_else_ : {X : Set} → Bool → X → X → X
if true  then x else y = x
if false then x else y = y

-- Lean's `Nat.ble`, with its three equations; core Lean decides `n ≤ m`
-- (`Nat.decLe`) by computing it.
_≤ᵇ_ : ℕ → ℕ → Bool
zero  ≤ᵇ _     = true
suc _ ≤ᵇ zero  = false
suc n ≤ᵇ suc m = n ≤ᵇ m

-- Lean's `min` on `Nat` (`minOfLe`): `if x ≤ y then x else y`.
min : ℕ → ℕ → ℕ
min x y = if x ≤ᵇ y then x else y

-- Order lemmas (Lean's `Nat.succ_le_succ`, `Nat.zero_le`, `Nat.le_add_right`,
-- `Nat.lt_irrefl`, `Nat.le_of_lt`, `Nat.lt_trans`).
≤-suc : ∀ {m n} → m ≤ n → suc m ≤ suc n
≤-suc refl     = refl
≤-suc (step p) = step (≤-suc p)

z≤n : ∀ n → zero ≤ n
z≤n zero    = refl
z≤n (suc n) = step (z≤n n)

≤-add-right : ∀ a w → a ≤ a + w
≤-add-right a zero    = refl
≤-add-right a (suc w) = step (≤-add-right a w)

<-irrefl : ∀ n → ¬ (n < n)
<-irrefl zero    ()
<-irrefl (suc n) (step p) = <-irrefl n (≤-trans (step refl) p)

≤-of-< : ∀ {a b} → a < b → a ≤ b
≤-of-< h = ≤-trans (step refl) h

<-trans : ∀ {a b c} → a < b → b < c → a < c
<-trans h1 h2 = ≤-trans h1 (≤-of-< h2)

-- `≤ᵇ` reflects `≤` (Lean's `Nat.ble_eq_true_of_le` and
-- `Nat.le_of_ble_eq_true`).
≤ᵇ-refl : ∀ n → n ≤ᵇ n ≡ true
≤ᵇ-refl zero    = refl
≤ᵇ-refl (suc n) = ≤ᵇ-refl n

≤ᵇ-step : ∀ m n → m ≤ᵇ n ≡ true → m ≤ᵇ suc n ≡ true
≤ᵇ-step zero    n       h = refl
≤ᵇ-step (suc m) zero    ()
≤ᵇ-step (suc m) (suc n) h = ≤ᵇ-step m n h

≤→≤ᵇ : ∀ {m n} → m ≤ n → m ≤ᵇ n ≡ true
≤→≤ᵇ {m} refl              = ≤ᵇ-refl m
≤→≤ᵇ {m} {suc n} (step p)  = ≤ᵇ-step m n (≤→≤ᵇ p)

≤ᵇ→≤ : ∀ m n → m ≤ᵇ n ≡ true → m ≤ n
≤ᵇ→≤ zero    n       _ = z≤n n
≤ᵇ→≤ (suc m) zero    ()
≤ᵇ→≤ (suc m) (suc n) h = ≤-suc (≤ᵇ→≤ m n h)
