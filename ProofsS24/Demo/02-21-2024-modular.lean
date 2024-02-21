import Mathlib.Tactic.Ring
import ProofsS24.Tactic.Addarith
import ProofsS24.Tactic.Cancel

/-- A number is odd if its remainder when divided by 2 is 1.-/
def Odd (a : ℤ) : Prop := ∃ (k : ℤ), a = 2 * k + 1

def Odd' (a : ℤ) : Prop := ∃ (k : ℕ), a = 2 * k + 1

def Odd'' (a : ℤ) : Prop := ∃ (k : ℤ), a = 2 * k - 1

example : Odd (7 : ℤ) := by
  -- unfolding the definition of Odd
  unfold Odd
  --change ∃ (k : ℤ), 7 = 2 * k + 1
  use 3
  rfl

-- Since `Odd` is a predicate on integers in below `n` is automatically infered to be an integer.
example (h : Odd n) : Odd (7 * n) := by
  dsimp [Odd] at * -- `*` means everywhere, i.e. hypotheses and the goal
  obtain ⟨m, hm⟩ := h
  rw [hm]
  ring
  use 7 * m + 3
  ring

example (h1 : Odd m) (h2 : Odd n) : Odd (m * n) := by
  dsimp [Odd] at *
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  rw [hk1, hk2]
  ring_nf
  use k1 + k1 * k2 * 2 + k2
  ring


example (hn : Odd n) : Odd (n^3) := by sorry

def Even (a : ℤ) : Prop := ∃ k, a = 2 * k

example {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by
  sorry
