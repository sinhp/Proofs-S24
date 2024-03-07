import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic


theorem not_all_of_exists_not {A : X → Prop} :
    (∃ x, ¬ A x) ↔ ¬ (∀ x, A x) := by
  constructor
  · intro h
    obtain ⟨x, hnx⟩ := h
    intro hA
    specialize hA x
    contradiction
  · sorry

theorem not_forall_iff_exists_not {P : X → Prop} : (¬ ∀ x, P x) ↔ (∃ x, ¬ P x) := by
  constructor
  · intro h1
    sorry
  · sorry


lemma zero_of_le_every_pos (ε : ℝ) (h : 0 ≤ ε) : (∀ x : ℝ, 0 < x → ε ≤ x ) → ε = 0 := by
  intro h₁
  --have h₂ := h1 (ε/2)
  have h₂ : 0 = ε ∨ 0 < ε := eq_or_lt_of_le h
  cases h₂ with
  | inl h₃ => exact h₃.symm
  | inr h₃ => exfalso
              have h₃ : 0 < ε/2 := div_pos h₃ zero_lt_two
              have h₄ : ε ≤ ε/2 := h₁ (ε/2) h₃
              linarith

example (ε : ℝ) : |ε| = 0 → ε = 0 := abs_eq_zero.mp

example (ε : ℝ) : (∀ x : ℝ, 0 < x → |ε| ≤ x ) → ε = 0 := by
  intro h
  apply abs_eq_zero.mp
  apply zero_of_le_every_pos
  apply abs_nonneg
  assumption

example (ε : ℝ) : (∀ x : ℝ, 0 < x → |ε| ≤ x ) → ε = 0 := by
  intro h
  apply abs_eq_zero.mp
  refine zero_of_le_every_pos _ ?_ ?_
  apply abs_nonneg
  assumption
