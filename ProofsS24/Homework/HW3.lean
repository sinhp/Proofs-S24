import Mathlib.Tactic.Ring
import ProofsS24.Tactic.Addarith
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Int.Defs
import Mathlib.Data.Int.Modeq
import Mathlib.Data.Real.Basic

/-
Please include as much commentary as possible in your proofs to explain your reasoning even to a reader who does not know how to read Lean code.
-/

/-
# Problem 1
Show that it is not the case that all prime numbers are odd.
-/

example : ¬ (∀ n : ℕ, Prime n → Odd n) := by
  sorry


/-
# Problem 2
Show that for all integers `n`, `n ^ 2` is not congruent to `2` modulo `4`.
-/

example : ∀ n : ℤ, ¬(n ^ 2 ≡ 2 [ZMOD 4]) := by
  sorry


/-
# Problem 3
Show that there is no natural number `n` such that `n ^ 2 = 2`.
-/
example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  sorry


/-
# Problem 4
-/

example : ∀ (a b : ℤ), (a ∣ b) →  a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  sorry

/-
# Problem 5
First give a proof of `my_lemma2` and `my_lemma3`. Then use `my_lemma1`,
`my_lemma2` and `my_lemma3`, `abs_nonneg` and `abs_mul` to prove the theorem `abs_mul_lt`.
-/


lemma my_lemma1 {a b c : ℝ} (h1 : a < b) (h2 : 0 ≤ c) :
    c * a ≤ c * b := by
  refine mul_le_mul_of_nonneg_left ?h h2
  exact LT.lt.le h1

lemma my_lemma2 {a b c : ℝ} (h1 : a < b) (h2 : 0 < c):
    a * c < b * c := by
  sorry

lemma my_lemma3 {a b c : ℝ} (h1 : a ≤ b) (h2 : 0 < c):
    a * c ≤ b * c := by
  sorry

#check abs_nonneg
#check abs_mul

theorem abs_mul_lt :
∀ (x y ε : ℝ), (0 < ε ∧ ε ≤ 1) → (abs x < ε ∧ abs y < ε) → abs (x * y) < ε := by
  sorry
