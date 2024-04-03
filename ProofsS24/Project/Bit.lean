/- Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sina Hazratpour.
-/

import Mathlib.Tactic
import Mathlib.Algebra.Parity

/-!
# The type of bits

In this file we introduce the type `Bit` with two elements `zero` and `one`.

Later, we shall use this type to to define a binary sequence, i.e. a function `ℕ → 𝟚`.

Later, to state that a binary sequence is decreasing, we need to define an order on the type `𝟚` to compare its elemetns. We define define a reflexive order on `𝟚` such that `zero ≤ one`.

We say a binary sequence is decreasing if the value at each index is greater than or equal to the value at the next index.

## Notation

 - `𝟚` : for the type `Bit`.

-/

inductive Bit : Type
  | zero
  | one
  deriving DecidableEq, Inhabited, Repr

namespace Bit

scoped notation "𝟚" => Bit

/-- The constructors of an inductive type are necessarily distinct and `noConfusion` proves this. -/
@[simp]
lemma zero_ne_one : zero ≠ one := by
  exact Bit.noConfusion

#check Bit.ofNat

instance : OfNat Bit n where
  ofNat := Bit.ofNat n

example : (0 : Bit) = zero := by
  rfl

example : (1 : Bit) = one := by
  rfl

/-- To define a function out of `Bit` it is sufficient to define the values of the function on the constructors of `Bit`. -/
def f : Bit → ℕ
  | zero => 1
  | one => 0

-- An order on a type `X` is a relation `≤ : X → X → Prop`. For `x y : X` then `≤ x y` is a proposition which says that `x` is less than or equal to `y`.

/-- The instance for comparing elements of `𝟚`. -/
instance : LE 𝟚 where
  le := fun a b => a = one → b = one

-- The notation `≤` is automatically generated becasue we just constructed an instance of an order on the type `𝟚`.

@[simp]
lemma le_one {a : 𝟚} : a ≤ one := by
  cases a
  · dsimp [LE.le]
    intro
    rfl
  · intro
    rfl

@[simp]
lemma zero_le {a : 𝟚} : zero ≤ a := by
  cases a
  · intro
    assumption
  · intro
    rfl

lemma one_le_eq_one {b : 𝟚} (h : one ≤ b) : b = one := by
  exact h rfl

lemma le_zero_eq_zero {b : 𝟚} (h : b ≤ zero) : b = zero := by
  cases b
  · rfl
  · exact (h rfl).symm

lemma le' {a b : 𝟚} : a ≤ b ↔ (b = zero) → (a = zero) := by
  constructor
  · intro h1 h2
    rw [h2] at h1
    exact le_zero_eq_zero h1
  · intro h1
    intro h2
    rw[h2] at h1
    by_cases h':b=zero
    · rw[h']
      symm
      apply h1
      exact h'
    · cases' b with left right
      · contradiction
      · rfl

lemma eq_zero_one_iff_le (a b : 𝟚) : (a = zero) ∨ (b = one) ↔ (a ≤ b) := by
  constructor
  · rintro (h1 | h1)
    · intro h2
      apply noConfusion (h1.symm.trans h2)
    · intro
      exact h1
  · intro h
    cases a
    cases b
    · trivial
    · trivial
    · right
      exact (h rfl)

/-- A preorder is a reflexive and transitive relation. The order ≤ on `𝟚` defined as
`a ≤ b ↔ a = 1 → b = 1` is reflexive and transitive. -/
instance : Preorder 𝟚 where
  le_refl := by
    -- we are proving a ∀ statement, so we postulate an arbitrary element `a` of `𝟚` and prove
    -- that `a ≤ a`.
    intro a h
    exact h
  le_trans := by
    intro a b c h1 h2
    dsimp [LE.le] at *
    intro h3
    -- apply h1 at h3
    -- apply h2 at h3
    -- exact h3
    exact h3 |> h1 |> h2

@[simp]
lemma zero_lt_one : zero < one := by
  constructor
  · simp
  · intro h
    dsimp[LE.le] at h
    contradiction

instance : PartialOrder 𝟚 where
  le_antisymm := by
    intro a b h1 h2
    cases a
    cases b
    · rfl
    · exact (h2 rfl)
    · simp [one_le_eq_one h1]

-- if a = one then one else b
@[macro_inline] def max (a b : 𝟚) : 𝟚 :=
  match a with
  | one  => one -- the maximum of `one` and anything else is `one`
  | zero => b -- `zero` does not contribute to the maximum.

lemma max_zero (b: 𝟚) : max zero b = b := by
  rfl

lemma max_one (a : 𝟚) : max a one = one := by
  cases' a with left right
  · rfl
  · rfl

/-- `a` is less than or equal to the max of `a` and `b` . -/
theorem le_max_left (a b : 𝟚) : a ≤ max a b := by
  dsimp [LE.le]
  intro h1
  rw [h1]
  rfl

/-- `b` is less than or equal to the max of `a` and `b` . -/
theorem le_max_right (a b : 𝟚) : b ≤ max a b := by
  dsimp [LE.le]
  intro h
  rw [h]
  apply max_one

/-- The max of `a` and `b` is the least upper bound of `a` and `b`. -/
theorem max_le {a b c : 𝟚} (h1 : a ≤ c) (h2 : b ≤ c) : max a b ≤ c := by
  sorry

-- if a = zero then zero else b
@[macro_inline] def min (a b : 𝟚) : 𝟚 :=
  match a with
  | zero  => zero
  | one => b

lemma zero_min (a : 𝟚) : min zero a = zero := by
  rfl

lemma min_zero (a : 𝟚) : min a zero = zero := by
  cases a
  · rfl
  · rfl

lemma one_min (a : 𝟚) : min one a = a := by
  rfl

lemma min_one (a : 𝟚) : min a one = a := by
  cases a
  · rfl
  · rfl

theorem min_respects_le { x y z w : 𝟚 } (h1 : x ≤ y) (h2 : z ≤ w) : min x z ≤ min y w := by
  cases x
  · rw [zero_min]
    apply zero_le
  · rw [one_min]
    apply one_le_eq_one at h1
    rw [h1]
    rw [one_min]
    exact h2

/-- `a` is greater than or equal to the min of `a` and `b` . -/
theorem min_le_left (a b : 𝟚) : min a b ≤ a := by
  nth_rw 2 [← (min_one a)]
  apply min_respects_le
  · rfl
  · apply le_one

theorem min_le_left' (a b : 𝟚) : min a b ≤ a := by
  cases' a with left right
  · rw[zero_min]
  · rw[one_min]
    apply le_one


/-- `b` is greater than or equal to the min of `a` and `b` . -/
theorem min_le_right (a b : 𝟚) : min a b ≤ b := by
  nth_rw 2 [← (one_min b)]
  apply min_respects_le
  · apply le_one
  · rfl

/-- The min of `a` and `b` is the greatest lower bound of `a` and `b`. -/
theorem le_min {a b c : 𝟚} (h1 : c ≤ a) (h2 : c ≤ b) : c ≤ min a b := by
  sorry

instance : Lattice 𝟚 where
  sup := max
  le_sup_left := le_max_left
  le_sup_right := le_max_right
  sup_le := by
    intro a b c h1 h2
    exact max_le h1 h2
  inf := min
  inf_le_left := min_le_left
  inf_le_right := min_le_right
  le_inf := by
    intro a b c h1 h2
    exact le_min h1 h2

@[simp]
def EqZero (b : Bit) := b = zero

@[simp]
def EqOne (b : Bit) := b = one

end Bit
