import Mathlib.Tactic.Ring
import ProofsS24.Tactic.Addarith
import ProofsS24.Tactic.Cancel
import ProofsS24.Tactic.ModCases

/-- Outcomes of a game of rock-paper-scissors:
https://en.wikipedia.org/wiki/Rock_paper_scissors
-/
inductive Hand
  | rock
  | paper
  | scissors

#check Hand.rock
#check Hand.paper
#check Hand.scissors

namespace Hand

/-- For outcomes `a` and `b` in a game of rock-paper-scissors, we say `beats a b` if `a` beats `b`. -/
@[reducible]
def beats : Hand → Hand → Prop
  | rock, scissors => True -- rock beats scissors
  | scissors, paper => True -- scissors beats paper
  | paper, rock => True -- paper beats rock
  | _, _ => False -- otherwise, it's a loss or a tie (e.g. rock doesn't beat rock).

example : ¬ Reflexive beats := by
  dsimp [Reflexive]
  push_neg
  use rock
  trivial

example : ¬ Symmetric beats := by
  dsimp [Symmetric]
  push_neg
  use rock
  use scissors
  trivial

example : ¬ Transitive beats := by
  dsimp [Transitive]
  push_neg
  use scissors
  use paper
  use rock
  trivial


example : ∀ (x : Hand), ∃ (y : Hand), beats x y := by
  intro x
  cases x
  use scissors
  use scissors
  use paper



#check Fin -- `Fin n` is the type whose elements are natural numbers smaller than `n`.

#check Fin 12

def ahead : Fin 12 → Fin 12 → Prop := fun a b => b < a

#check (12 : Fin 12) -- `Fin 12` is the type whose elements are natural numbers smaller than `12`.
#reduce (12 : Fin 12)

example : ahead 11 12 := by dsimp [ahead]; trivial

example : ahead 11 12 := by simp [ahead]

#synth LE (Fin 4)

example : (12 : Fin 12) ≤ 11 := by trivial

example : ¬ Reflexive ahead := by
  dsimp [Reflexive, ahead]
  push_neg
  use 0
  trivial

example : ¬ Symmetric ahead := by
  dsimp [Symmetric, ahead]
  push_neg
  use 1
  use 0
  trivial

example : Transitive ahead := by
  dsimp [Transitive, ahead]
  intro a b c
  intro h1 h2
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  obtain ⟨c, hc⟩ := c
  simp at *
  exact h2.trans h1

-- local infix:50 " ≺ " => beats

/-- Putting a less-than relation on the hand outcomes.
This instance makes the notation `<` available.    -/
instance : LT Hand where
  lt a b := beats b a

instance : LE Hand where
  le a b := a = b ∨ beats b a

example : scissors < rock := by trivial

example : scissors ≤ rock := by
  right
  trivial






-- https://en.wikipedia.org/wiki/Rock_paper_scissors#Additional_weapons




end Hand
