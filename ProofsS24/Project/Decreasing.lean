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

/-- `binSeqOf` associates to a natural number `n` the sequence that is one at indices less than `n` and zero at indices greater than or equal to `n`. -/
def binSeqOf (n : ℕ) : BinSeq := fun i => if i < n then one else zero

/-- The constant sequence at zero. -/
def zeroSeq : BinSeq := fun _ => zero

/-- `binSeqOf` associates to `0` the constant sequence at zero. -/
lemma binSeqOf_zero_eq_zeroSeq : binSeqOf 0 = zeroSeq := by
  funext i
  dsimp [binSeqOf, zeroSeq]
  rw [if_neg]
  linarith

/-- The constant sequence at one. -/
def oneSeq : BinSeq := fun _ => one

/-- The alteranting sequence that is zero at even indices and one at odd indices. -/
@[simp]
def evenOddSeq (n : ℕ) : 𝟚 := if n % 2 = 0 then zero else one

/-- Adding a bit `b` to the beginning of a sequence. -/
def BinSeq.cons (b : Bit) (α : BinSeq) : BinSeq := fun n => if n = 0 then b else α (n - 1)

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

/-- The binary sequence `binSeqOf n` is decreasing. -/
lemma binSeqOf_decreasing (n : ℕ) : Decreasing (binSeqOf n) := by
  apply iff_antitone.mpr
  intro i j hij
  dsimp [binSeqOf]
  by_cases h : j < n
  · rw [if_pos h]
    rw [if_pos (lt_of_le_of_lt hij h)]
  · rw [if_neg h]
    exact Bit.zero_le


#check ite
#check if_pos


/-- Given a sequence we construct a decreasing sequence recursively. -/
def mk (a : ℕ → 𝟚) : ℕ → 𝟚
  | 0 => a 0
  | n + 1 => min (a (n + 1)) (mk a n)

lemma mk_zero {a : ℕ → 𝟚} : (mk a) 0 = a 0 := by
  rfl

lemma mk_succ {a : ℕ → 𝟚} :  (mk a) (n + 1) = min (a (n + 1)) (mk a n) := by
  rfl

#check mk evenOddSeq
#eval evenOddSeq 1
#eval (mk evenOddSeq) 1

/-- The sequence `mk a` constructed from a sequence `a` is decreasing. -/
lemma mk_is_decreasing (a : ℕ → 𝟚) : Decreasing (mk a) := by
  -- unfold Decreasing
  intro n
  -- change (min (a (n + 1)) (mk a n)) ≤ mk a n
  apply Bit.min_le_right


lemma mk_eq_self {a : ℕ → 𝟚} (h : Decreasing a) : mk a = a := by
  funext n
  sorry

/-- Decreasing.mk is idempotent. -/
lemma mk_mk_eq_mk {a : ℕ → 𝟚} : mk (mk a) = mk a := by
  rw [mk_eq_self]
  exact mk_is_decreasing a

/-- If a sequence `α` is decreasing, then `cons b α` is decreasing for any `b`. -/
lemma cons (b : Bit) (a : ℕ → 𝟚) (h : Decreasing a) : Decreasing (BinSeq.cons b a) := by
  sorry



end Decreasing
