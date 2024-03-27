import Mathlib.Tactic.Ring
import ProofsS24.Tactic.Addarith
import ProofsS24.Tactic.Cancel
import ProofsS24.Tactic.ModCases
import ProofsS24.Tactic.Induction

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Parity
import Mathlib.Algebra.BigOperators.Fin

open Function BigOperators Finset Nat

-- A function from reals to reals which assigns to every `x : ℝ` the value `abs (x - 1)`.
def adhoc_fun : ℝ → ℝ := fun (x : ℝ) ↦ abs (x - 1)

def adhoc_fun' : ℝ → ℝ := fun x  ↦ abs (x - 1)

def adhoc_fun'' := fun (x : ℝ)  ↦ abs (x - 1)

def adhoc_fun''' := fun x  ↦ abs ((x : ℝ) - 1)

def adhoc_fun'''' : ℕ → ℝ := fun x ↦ abs ( (x : ℝ) - 1)

#check @adhoc_fun'''
#check @adhoc_fun''''

-- equality of functions
section
-- Function extensionality says that two functions `f` and `g` are equal if they assign the same output `f x` and `g x`  to each input `x`.
example {f g : X → Y} (h: ∀ x, f x = g x) : f = g := by
  funext x
  exact (h x)
end

example : adhoc_fun = adhoc_fun' := by
  -- let `i` be an arbitrary real number
  funext i
  -- we show that `adhoc_fun i = adhoc_fun' i`.
  -- unfold adhoc_fun
  -- unfold adhoc_fun'
  -- rfl
  simp only [adhoc_fun, adhoc_fun']

--`adhoc_fun = adhoc_fun''''` is not even wrong, but meaningless.
-- example : adhoc_fun = adhoc_fun'''' := by sorry


-- We can use function composition to break down a function into simpler pieces:

#check abs
def minus_one := fun (x : ℝ) ↦ (x - 1)

example : adhoc_fun = fun x => abs (minus_one x) := by
  funext i
  rfl

#check @minus_one
#check @abs (α := ℝ)

-- (f ∘ g) (i) = f (g i)
example : adhoc_fun = abs ∘ minus_one := by
  funext i
  dsimp
  rfl



#check LeftInverse
#check @id


section
variable {f : X → Y} {g : Y → X}
#check LeftInverse f g -- `f` is a left inverse of `g`, i.e. `∀ y, f ( g y ) = y` equationally, and diagramatically
-- Y --g--> X --f--> Y = Y -- id --> Y
#check Function.RightInverse f g -- means `g (f x) = x for all x`,
end

example {f : X → Y} {g : Y → X} :  LeftInverse f g ↔ (f ∘ g = id) := by
  constructor
  · -- let's suppose that `f` is a left inverse of `g`
    intro h
    simp [Function.LeftInverse] at h
    funext y
    dsimp
    --exact h y
    -- apply h
    specialize h y
    assumption
  · intro h
    simp [Function.LeftInverse]
    intro x
    -- we want to eliminate function equality
    have : ∀ y, (f ∘ g) y = y := by
      -- `simp_rw` is like `rw` but applies under binders.
      simp_rw [h]
      simp only [id_eq]
      simp [implies_true]
    exact this x


example {f : X → Y} {g : Y → X} : RightInverse g f ↔ ∀ y : Y, f (g y) = y := by
  unfold Function.RightInverse
  unfold Function.LeftInverse
  rfl

example {f : X → Y} {g : Y → X} : RightInverse g f ↔ ∀ y : Y, f (g y) = y := by
  apply Iff.intro
  · intro h y
    simp [Function.RightInverse, Function.LeftInverse] at h
    apply h y
  · intro h
    exact h

-- 0, 1, 1, 2, 3, 5, 8, 13, 21, 34, ...
-- Finbonaci numbers defined as a sequence (function) by recursion
def F : ℕ → ℤ
  | 0 => 0 -- `F 0` is defined to be `0`
  | 1 => 1 -- `F 1` is defined to be `1`
  | n + 2 => F (n + 1) + F n -- the recursive part, `F (n + 2)` is defined to be `F (n + 1) + F n `.

example : F 2 = F 1 + F 0 := by
  rfl

example : F 2 = 1 := by
  rfl

example : F 5 = 5 := by
 -- F 5 = F (4 + 3) = F 4 + F 3
  rw [F]
  rw [F, F]
  iterate {rw [F]}
  rfl

example : F 5 = 5 := by
  rfl


#check ({1,2,3} : Set ℕ)

#check insert 4 ({1,2,3} : Set ℕ)
#check insert 2 ({1,2,3} : Set ℕ)

example : insert 2 ({1,2,3} : Set ℕ) = {1,2,3} := by
  ext x
  simp only [Set.insert, Set.mem_insert_iff]
  -- using P ∨ P ↔ P and few basic logical steps
  tauto


example : ({1,2,3} : Set ℕ) = {1} ∪ {2} ∪ {3} := by
  ext x
  -- simp only [Set.mem_insert_iff]
  -- simp only [Set.mem_singleton_iff]
  -- iterate simp only [Set.mem_union]
  -- iterate simp only [Set.mem_singleton_iff]
  -- rw [or_assoc]
  simp
  tauto

#check @Even -- ℕ → Prop

#check (Even : Set ℕ) -- this set picks only the elements `n` of `ℕ` for which `Even n` is true. `Even` is a subset of natural numbers which is not finite.

#check ({1,2,3} : Finset ℕ)

#check (∅ : Finset ℕ)

#check Finset.range 3

example : Finset.range 3 = {0, 1, 2} := by
  rfl

example : Finset.range 0 = ∅ := by
  rfl

-- `∑ 0 ≤ i < n, F (i + 1) = F (n + 2) - 1`
example (n : ℕ) : (∑ i in Finset.range n, F (i + 1)) = F (n + 2) - 1 := by
  apply eq_sub_of_add_eq
  induction n with
  -- the empty sum is equal to one (why?)
  | zero => rfl
  | succ n ih => sorry


-- sum of squares of consecutive fibonacci numbers
example {n : ℕ} : (F n)^2 + (F (n + 1))^2 = F (2 * n + 1) := by
  sorry



-- example (n : ℕ) : F n ≤ 2 ^ n := by
--   two_step_induction n with k IH1 IH2
--   · calc F 0 = 1 := by rw [F]
--       _ ≤ 2 ^ 0 := by numbers
--   · calc F 1 = 1 := by rw [F]
--       _ ≤ 2 ^ 1 := by numbers
--   · calc F (k + 2) = F (k + 1) + F k := by rw [F]
--       _ ≤ 2 ^ (k + 1) + 2 ^ k := by rel [IH1, IH2]
--       _ ≤ 2 ^ (k + 1) + 2 ^ k + 2 ^ k := by extra
--       _ = 2 ^ (k + 2) := by ring
