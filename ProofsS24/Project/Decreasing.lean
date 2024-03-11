/- Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sina Hazratpour.
-/

import Mathlib.Tactic
import ProofsS24.Project.Bit

/-!
# CoNatural Numbers

In this file we define decreasing binary sequences and study their properties.

## Notation

 - `ℕ∞` : for the type `CoNat`.

-/

open Bit

/-- A binary sequence is a function from natural numbers to the type 𝟚. -/
def BinSeq := ℕ → Bit

/-- The constant sequence at zero. -/
@[simp]
def zeroSeq : BinSeq := fun _ => zero

/-- The constant sequence at one. -/
@[simp]
def oneSeq : BinSeq := fun _ => one

/-- The alteranting sequence that is zero at even indices and one at odd indices. -/
@[simp]
def evenOddSeq (n : ℕ) : 𝟚 := if n % 2 = 0 then zero else one

/-- A sequence is decreasing if the value at each index is greater than or equal to the value at the next index. -/
def Decreasing (a : ℕ → 𝟚) := ∀ n, a (n + 1) ≤ a n

namespace Decreasing

@[simp]
lemma iff_zero_succ_zero {a : ℕ → 𝟚} :
    Decreasing a ↔ (∀ n, a n = zero → a (n + 1) = zero) := by
  constructor
  · sorry
  · sorry

lemma iff_antitone {a : ℕ → 𝟚} :
    Decreasing a ↔ (∀ i, ∀ j,  i ≤ j → a j ≤ a i) := by
  constructor
  · intro h
    intro i j hij
    induction' hij with d h1 h2
    · rfl
    · exact (h d).trans h2
  · sorry

/-- A sequence is decreasing if and only if for each index whenever there is a zero at or before that index, the value at that index is zero. -/
lemma iff_zero_of_exists_prior_zero {a : ℕ → 𝟚} :
    Decreasing a ↔ (∀ i : ℕ, (∃ j ≤ i, a j = zero) → a i = zero) := by
  constructor
  · intro h
    intro i hi
    obtain ⟨j, hj, haj⟩ := hi
    apply iff_antitone.mp h at hj
    rw [haj] at *
    apply le_zero_eq_zero hj
  · sorry

/-- Given a sequence we construct a decreasing sequence recursively. -/
def mk (a : ℕ → 𝟚) : ℕ → 𝟚
  | 0 => a 0
  | n + 1 => min (a (n + 1)) (mk a n)

#check mk evenOddSeq
#eval evenOddSeq 1
#eval (mk evenOddSeq) 1

/-- The sequence `mk a` constructed from a sequence `a` is decreasing. -/
lemma decreasing_mk (a : ℕ → 𝟚) : Decreasing (mk a) := by
  intro n
  induction n with
  | zero =>
    sorry
  | succ n ih =>
    sorry



end Decreasing
