import Mathlib.Tactic.Ring
import ProofsS24.Tactic.Addarith
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Defs
import Mathlib.Data.Int.Modeq


/-
# Problem 1
The following exercises from Section 3.1.10 of Mechanics of Proofs
(https://hrmacbeth.github.io/math2001/03_Parity_and_Divisibility.html#exercises)

- Ex 6. Prove that if the integers `r` and `s`  are odd, then `3 * r - 5 * s` is even.
- Ex 7. Let `x` be an integer. Show that if `x` is odd then so is `x^3`.
- Ex. 14 Let `a, b` and `c` be integers. Show that at least one of `a - b`, `a + c`  or `b - c` is even.
-/


/-
# Problem 2
This problem is about the concept of divisibility. See Section 3.2. of the Mechanics of Proofs:
https://hrmacbeth.github.io/math2001/03_Parity_and_Divisibility.html#divisibility

Provide as much clear commentary for the steps of proofs as possible.

Note: type the symbol `∣` for divisibility as `\|`.
-/
-- definition of divisibility
example (m n : ℤ) : m ∣ n ↔ ∃ k : ℤ, n = m * k := by trivial

/- 2.1. -/
example (a : ℤ) : a ∣ 0 := by sorry

/- 2.2. -/
example (a : ℤ) : 0 ∣ a ↔ a = 0 := by sorry

/- 2.3. -/
example (a b : ℤ) : a ∣ b ↔ -a ∣ b := by sorry

/- 2.4. -/
example (a : ℤ) : a ∣ 1 ↔ a = 1 ∨ a = -1 := by sorry

/- 2.5. -/
example (a : ℤ) (n : ℕ) (h : n > 0) : a ∣ a^n := by sorry

/- 2.6. -/
example (a b c : ℤ) : a ∣ b → a ∣ c → a ∣ b + c := by sorry

/- 2.7. -/
example {a b : ℕ} (hb : 0 < b) (hab : a ∣ b) : a ≤ b := by sorry

/-
# Problem 3
In this exercise, you will prove the de Morgan laws of propositional logic. One of the laws is non-constructive, which means that it is not possible to prove it without the law of excluded middle. The law of excluded middle states that for any proposition `P`, `P ∨ ¬P` holds.
-/

example : ¬ P ∨ ¬ Q → ¬ (P ∧ Q) := by sorry

example : ¬ (P ∧ Q) → ¬ P ∨ ¬ Q := by sorry

example : ¬ P ∧ ¬ Q → ¬ (P ∨ Q) := by sorry

example : ¬ (P ∨ Q) → ¬ P ∧ ¬ Q := by sorry
