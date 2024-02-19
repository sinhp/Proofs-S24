import Mathlib.Tactic.Ring
import ProofsS24.Tactic.Addarith
import ProofsS24.Tactic.Cancel
import Mathlib.Data.Real.Basic

example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  ring
  constructor
  ring
  constructor
  ring_nf
  ring_nf
  trivial
  trivial


example (n : ℝ) : n^2 ≥ 0 := by
  positivity

example (n : ℝ) : 68 * n ^ 2 ≥ 0 := by
  positivity

example (m : ℝ) : m - m = 0 := by
 exact sub_self m

example (m n : ℝ) (hn : 10 ≤ n) : m + 68 * n ^ 2 ≥ m := by
  refine tsub_le_iff_left.mp ?_
  rw [sub_self]
  positivity

example (m n : ℝ) (hn : 10 ≤ n) : m + 68 * n ^ 2 ≥ m := by
  extra

example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  linarith
