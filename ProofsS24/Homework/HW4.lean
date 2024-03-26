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

open Function

/-
# Problem 1
Let `f : ℤ → ℤ` be the function `f(x) = x + 5`. Prove that there exists a function `g : ℤ → ℤ` such that `(g ∘ f) x = x + 2`.
-/

example (f : ℤ → ℤ := fun x ↦ x + 5) :
    ∃ (g : ℤ → ℤ), (g ∘ f) x = x + 2 := by
  sorry


/-
# Problem 2
Show that the function `f : ℤ → ℤ` defined by `f(x) = x + 1` is bijective.
-/

example : Bijective (fun (x : ℤ) ↦ x + 1) := by
  sorry


/-
# Problem 3
We say a function `f` is an inverse of a function `g` if `g ∘ f = id` and `f ∘ g = id`. In this exercise you show that `f` is an inverse of `g` if and only if  `f` is both a left and a right inverse of `g`.
-/

def Inverse (f : X → Y) (g : Y → X) : Prop := g ∘ f = id ∧ f ∘ g = id

example {f : X → Y} {g : Y → X} :  Inverse f g ↔  (LeftInverse f g) ∧ (RightInverse f g) := by
  sorry


/-
# Problem 4
Let `f` be a surjective function. Show that there exists a function `g` such that `f ∘ g = id`.
-/

example {f : X → Y} (hf : Surjective f) : ∃ g : Y → X, f ∘ g = id := by
  sorry


/-
# Problem 5
Show that for all integers `n`, `n ^ 2` is not congruent to `2` modulo `4`.
-/

example : Bijective (fun ((r, s) : ℚ × ℚ) ↦ (s, r - s)) := by
  unfold Bijective
  sorry


/-
# Problem 6
Let `f : ℚ → ℚ` be a function which is strictly monotone; that is, for all real numbers `x` and `y` with `x < y`, it is true that `f x < f y`. Prove that `f` is injective.

Hint: You may wish to use the lemma `lt_trichotomy` from mathlib
`lemma lt_trichotomy (x y : ℚ) : x < y ∨ x = y ∨ x < y := `
-/

example {f : ℚ → ℚ} (hf : ∀ x y, x < y → f x < f y) : Injective f := by
  sorry


/-
# Problem 7 (Bonus)
Suppose `M` is an additive commutative monoid. This means that `M` is a type with an associative addition operation `+` which has an identity element `0` and is commutative. In more detail, we have the following data and properties:
- a binary operation `+ : M → M → M`
- an element `0 : M`
- a property that `+` is associative: `∀ a b c : M, (a + b) + c = a + (b + c)`
- a property that `0` is the identity element of `+`: `∀ a : M, a + 0 = a` and `∀ a : M, 0 + a = a`
- a property that `+` is commutative: `∀ a b : M, a + b = b + a`


We say a sequence `f : ℕ → M` is __periodic__ if there exist some nonzero `T`, called the period of the function, such that for all `n`, we have `f (n + T) = f n`.  Show that if `f` and `g` are eventually periodic sequences, then so is their sum `f + g`.
-/

variable {M : Type*} [AddCommMonoid M]

section
#check (. + . : M → M → M)
#check (0 : M)
#check zero_add
#check add_zero
#check add_assoc
#check add_comm
end

def Periodic (f : ℕ → M) := ∃ T ≠ 0, ∀ n : ℕ, f (n + T) = f n

theorem eventually_periodic_add {f g : ℕ → M}
    (hf : Periodic f) (hg : Periodic g) : Periodic (f + g) := by
  unfold Periodic at *
  simp only [Pi.add_apply]
  sorry
