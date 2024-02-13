--import ProofsS24.Tactic.Addarith
--import ProofsS24.Tactic.Numbers
--import ProofsS24.Tactic.Use

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring

open Real

/-!
# Homework 1
Homework must be done individually.
-/

/-
# Problem 1

Form the following expressions and find/verify their type in Lean using the `#check` command.

1. The sum of the two thirds and the three fifths as a rational number
2. The sum of two thirds and three fifths as a real number
3. The circumference of a circle with radius 1.5
4. The volume of a thetraedron with side length 2.5
-/


/-
Solution to P1.1.
-/

#check 2/(3 : ℚ) + 3/(5 : ℚ)  -- : ℚ





/-
# Problem 2
How Lean parses: In this problem we are going to investigate how Lean binds operators, and what binding priorities are assigned to them.
-/

/-
1. 2 + 3 * 4
2. 3 - 2 + 4
3. 3 / 2 * 4
4. (-3) ^ 2 * 6
5. (-3) ^ 3 ^ 2
6. (-1: ℚ) / 2 ^ 3 * 5
-/

/- Solution to P2.1:
In Lean multiplication binds more strictly than addition and therefore Lean parases the expression `2 + 3 * 4` as `2 + (3 * 4)`.
 -/
#eval 2 + 3 * 4
#eval 2 + (3 * 4)
example : 2 + 3 * 4 = 2 + (3 * 4) := rfl





/-
# Problem 3
In this exercise you will define some terms of given types in Lean. If possible, provide a term of the specified type. If not, explain why not.
-/

/-
1. `List (ℕ × ℚ)`
2. `List (Unit ⊕ ℕ)`
3. `List ℕ × ℕ`
4. `List (List ℕ)`
5. `List Empty`
6. `Empty × ℕ`
7. `Bool ⊕ Empty × ℕ`
8. `Empty ⊕ Empty`
-/

/-
Solution to P3.1:
-/
#check [(2, 1/(2 : ℚ)), (1, 0)]



/-
# Problem 4
Choose 5 distinct problems from [Mechanics of Proofs, Exercises of Chapter 2](https://hrmacbeth.github.io/math2001/02_Proofs_with_Structure.html#id38)
-/


-- x ≤ y := ∃ z, x + z = y
-- x ≤ x = ∃ x, x + z = x

example (x : ℕ) : ∃ z, x + z = x  := by
  use 0
  rw [add_zero]

#check abs
#check fun (n : ℤ) => abs n
/-
P 4.8.
-/
#check abs_nonneg
#check if_pos
#check ite
example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  -- since RHS depends on `n` the LHS also must depend on `n` and therefore `a` has to depend on `n`.
  use |n| + 2
  rcases le_or_gt 0 n with hpos | hneg
  rw [abs_of_nonneg hpos]
  ring
  sorry

#check CovariantClass
