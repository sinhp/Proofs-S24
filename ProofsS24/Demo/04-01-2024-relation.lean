import Mathlib.Tactic.Ring
import ProofsS24.Tactic.Addarith
import ProofsS24.Tactic.Cancel
import ProofsS24.Tactic.ModCases

import Mathlib.Logic.Relation


def two_sided_inv : (α → α) → (α → α) → Prop :=
  fun f g => ∀ x, f (g x) = x ∧ g (f x) = x


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

/--
Defining a __binary predicate__ on `Hand`:
For outcomes `a` and `b` in a game of rock-paper-scissors, we say `beats a b` if `a` beats `b`. -/
@[reducible]
def beats : Hand → Hand → Prop
  | rock, scissors => True -- rock beats scissors
  | scissors, paper => True -- scissors beats paper
  | paper, rock => True -- paper beats rock
  | _, _ => False -- otherwise, it's a loss or a tie (e.g. rock doesn't beat rock).
-- https://en.wikipedia.org/wiki/Rock_paper_scissors#Additional_weapons

section
variable {n : ℤ}
#check (. ≡ . [ZMOD n])
variable (x y : ℤ)
#check x ≡ y [ZMOD n]
end

example {n : ℤ} : Reflexive (. ≡ . [ZMOD n]) := by
  dsimp [Reflexive]
  intro x
  use 0
  ring
  --exact Int.ModEq.refl


example : ¬ Reflexive beats := by
  intro h
  dsimp [Reflexive] at h
  --apply h paper
  specialize h paper
  trivial

example : ¬ Reflexive beats := by
  dsimp [Reflexive]
  push_neg
  use paper
  trivial

#check Symmetric


example : ¬ Symmetric beats := by
  dsimp [Symmetric]
  push_neg
  use paper, rock
  trivial
  --tauto

#check Transitive

example : ¬ Transitive beats := by
  dsimp [Transitive]
  push_neg
  use paper, rock, scissors
  trivial

instance : LT Hand where
  lt a b := beats b a

#check scissors < rock

example : scissors < rock := by
  dsimp [LT.lt]
  trivial

instance : LE Hand where
  le a b := a = b ∨ a < b

#check rock ≤ rock


#check Fin
#check Fin 3
#check Fin 12
#check (1 : Fin 3)
#check (1 : Fin 12)
#check (0 : Fin 12)
#check (13 : Fin 12)

example : (0 : Fin 12) = 12 := by
  rfl

example : (1 : Fin 12) = 13 := by
  rfl

#check ( (. : Fin 12) < .)

example : (1 : Fin 12) < 2 := by
  trivial

example : (12 : Fin 12) < 1 := by
  trivial

example : ¬ Reflexive ( (. : Fin 12) < .) := by
  dsimp [Reflexive]
  push_neg
  use 0
  trivial

example : ¬ Symmetric ( (. : Fin 12) < .) := by
  dsimp [Symmetric]
  push_neg
  use 0 , 1
  trivial

example : Transitive ( (. : Fin 12) < .) := by
  dsimp [Transitive]
  intro x y z h1 h2
  obtain ⟨x1, hx1⟩ := x
  obtain ⟨y1, hy1⟩ := y
  obtain ⟨z1, hz1⟩ := z
  simp at *
  linarith


example : Transitive ( (. : Fin 12) < .) := by
  intro ⟨x,hx⟩ ⟨y, hy⟩ ⟨z,hz⟩ h1 h2
  simp at *
  linarith


-- Transfer a relation along a function. -/
def transfer {α β : Type} (f : α → β) (r : β → β → Prop) : α → α → Prop :=
 sorry
