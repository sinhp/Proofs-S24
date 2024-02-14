import Mathlib.Tactic.Ring
import ProofsS24.Tactic.Addarith
import ProofsS24.Tactic.Cancel
import Mathlib.Data.Real.Basic

example {a b : ℝ} (h₁ : a - 5 * b = 4) (h₂ : b + 2 = 3) : a = 9 := by
  -- let's make an intermediate goal `b = 1`
  have h₃ : b = 1 := by
    calc b = b + 2 - 2 := by rw [add_sub_cancel b 2]
         _ = 3 - 2 := by rw [h₂]
         _ = 1 := by ring --sorry  -- addarith [h₂]
  -- substitute `1` for `b` into `h₁`
  rw [h₃] at h₁
  have h₄ : a = 9 := by sorry
  exact h₄


example {a b : ℝ} (h₁ : a - 5 * b = 4) (h₂ : b + 2 = 3) : a = 9 := by
  -- let's make an intermediate goal `b = 1`
  -- addarith is for additive arithmetic
  have h₃ : b = 1 := by addarith [h₂]
  -- substitute `1` for `b` into `h₁`
  rw [h₃] at h₁
  have h₄ : a = 9 := by addarith [h₁]
  exact h₄

/-- Maybe closer to the way we write proofs in math: https://hrmacbeth.github.io/math2001/02_Proofs_with_Structure.html#example -/
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 := by
  have hb : b = 1 := by addarith [h2]
  calc
    a = a - 5 * b + 5 * b := by ring
    _ = 4 + 5 * 1 := by rw [h1, hb]
    _ = 9 := by ring

example {m n : ℤ} (h1 : m + 3 ≤ 2 * n - 1) (h2 : n = 5) : m ≤ 6 := by
  have h3 : m + 3 ≤ 9 := by
    rw [h2] at h1
    addarith [h1]
  -- addarith works for proving inequlaities as well as long as we use additive method (addition, subtraction)
  addarith [h3]

-- x ≤ y → y ≤ z → x ≤ z
#check le_trans
-- _ ≤ _ , _ ≤ _ ⊢ _ ≤ _

-- a ≤ b → 2 * a ≤ 2 * b

#check mul_le_mul_left

example {a b : ℚ} : a ≤ b → 2 * a ≤ 2 * b := by
  intro h
  exact (mul_le_mul_left rfl).mpr h

example {m n : ℤ} (h1 : m + 3 ≤ 2 * n - 1) (h2 : n ≤ 5) : m ≤ 6 := by
  have h3 : 2 * n ≤ 10 := by sorry -- maybe use `mul_le_mul_left`
  have h4 : 2 * n - 1 ≤ 9 := by addarith [h3]
  have h5 : m + 3 ≤ 9 := by
    apply le_trans
    exact h1
    exact h4
  -- addarith works for proving inequlaities as well as long as we use additive method (addition, subtraction)
  sorry


example {t : ℝ} (h1 : t ^ 2 = 3 * t) (h2 : t ≥ 1) : t ≥ 2 := by
  have h3 :=
    calc t * t = t ^ 2 := by ring
    _ = 3 * t := by rw [h1]
  cancel t at h3
  addarith [h3]
