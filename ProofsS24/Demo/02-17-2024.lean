import Mathlib.Tactic.Ring


/-- Proving the binomial Idenity (sum of squares) only with rewrites -/
example {a b : ℚ} : (a + b)^2 = a^2 + 2 * a * b + b^2 := by
/- simplifying the LHS by using the fact x^2 = x * x -/
  rw [pow_two]
/- distributing the first addition over multiplication -/
  rw [add_mul]
/-  distributing the multiplication over addition -/
  rw [mul_add, mul_add]
/- simplifying the RHS by using the fact x^2 = x * x -/
  rw [pow_two, pow_two]
/- using the fact that 2 * x = x + x -/
  rw [mul_assoc 2 a b, two_mul]
/- Changing b * a by a * b -/
  rw [mul_comm b a]
  rw [add_assoc]
  rw [add_assoc, add_assoc]

example {a b : ℚ} : (a + b)^2 = a^2 + 2 * a * b + b^2 := by
  ring

example {a b c : ℚ} (h : b = c) : a + b = a + c := by
  rw [h]

example {a b c : ℚ} (h : a + b = a + c) : b = c := by
  calc
    b = -a + (a + b) := by exact eq_neg_add_of_add_eq rfl
    _ = -a + (a + c) := by rw [h]
    _ = c := by exact (eq_neg_add_of_add_eq rfl).symm

#check add_assoc -- : (x + y) + z = x + (y + z)
#check Ring
#check Ring ℤ
#synth Ring ℤ

lemma diff_square {a b : ℚ} : (a - b)^2 = a^2 - 2 * a * b + b^2 := by
  ring

/-- use the lemma s`diff_square` above and only the tactic `rw` to prove this. -/
example {a b : ℚ} : (a - b) ^ 2 + 4 * (a * b) = a^2 + 2 * a * b + b^2 := by
 rw [diff_square]
 sorry


example {a b : ℚ} (h1 : a - b = 4) (h2 : a * b = 1) : (a + b) ^ 2 = 20 :=
  calc
    (a + b) ^ 2 = (a - b) ^ 2 + 4 * (a * b) := by ring
    _ = 4 ^ 2 + 4 * 1 := by rw [h1, h2]
    _ = 20 := by rfl
