import Mathlib.Tactic.Ring
import ProofsS24.Tactic.Addarith
import ProofsS24.Tactic.Cancel
import ProofsS24.Tactic.ModCases
import Mathlib.Data.Polynomial.Eval
import Mathlib.Data.Real.Basic



/-! # Connectives and quantifiers

Each connective or quantifier has an introduction rule and an elimination rule.

## Introduction Rules

**Disjunction** `∨` has two introduction rules. The corresponding Lean tactics are `left` and `right`. This means that whenever we have a goal of the kind `⊢ P ∨ Q`, we can use the `left` tactic to reduce the goal to `⊢ P` and the `right` tactic to reduce the goal to `⊢ Q`.

**Conjunction** `∧` has one introduction rule. The corresponding Lean tactic is `constructor`. This means that whenever we have a goal of the kind `⊢ P ∧ Q`, we can use the `constructor` tactic to reduce the goal to two subgoals, first `⊢ P` and then `⊢ Q`.

**Implication** `→` has one introduction rule. The corresponding Lean tactic is `intro`: This means whenever we have a goal of the kind `⊢ P → Q`, we can use the `intro` tactic to introduce a new hypothesis `h : P` and then prove `Q` using `h`. Note that `h` is not an actual proof of `P`, but a hypothesis that we can use to prove `Q`.

**Negation** `¬`, defined as an implication to `False`, has one introduction rule. The corresponding Lean tactic is `intro`. This means whenever we have a goal of the kind `⊢ ¬ P`, we can use the `intro h` tactic to introduce a new hypothesis `h : P` and then prove `False` using `h`. Note that `h` is not an actual proof of `P`, but a hypothesis that we can use to prove `False`.

The **existential quantifier** `∃` has one introduction rule. The corresponding Lean tactic is `use`. This means that whenever we have a goal of the kind `⊢ ∃ x : X, P x`,  we can propose a term `t` of `X` and apply the tactic `use` to the term `t`, like `use t`, to reduce the goal to `⊢ P t`.

The **universal quantifier** `∀` has one introduction rule. The corresponding Lean tactic is `intro`. This means that whenever we have a goal of the kind `⊢ ∀ x : X, P x`, we need to prove `P t` for any arbitrary term `t` of `X`. We can use the `intro t` tactic to introduce a new arbitrary term `t : X` -- we have no knowledge of `t` except that it is a term of `X`, and then prove `P t`.

### Elimination Rules

**Disjunction** `∨` has one elimination rule. The corresponding Lean tactic is `cases` (or, `cases'`). This means that whenever we have a hypothesis `h : P ∨ Q`, we can use the `cases' h with hp hw` tactic to generate two subgoals, the first having `P` as a hypothesis, and the second having `Q` as a hypothesis.

**Conjunction** `∧` has two elimination rules. The corresponding Lean tactics are `left` and `right`. This means that whenever we have a hypothesis `h : P ∧ Q`, we can use the `left` to get a proof of `P` as a hypothesis and the `right` tactic to get a proof of `Q` as a hypothesis.

**Implication** `→` has one elimination rule. The corresponding Lean tactic is `apply`. This means that whenever we have a goal `⊢ Q` and a hypothesis `h : P → Q`, we can use the `apply h` tactic to reduce the goal to `⊢ P`.

**Negation** `¬` has one elimination rule. The corresponding Lean tactics are `apply` and `contradiction`.

**Existential quantifier** `∃` has one elimination rule. The corresponding Lean tactics are `cases` and `obtain`. This means that whenever we have a hypothesis `h : ∃ x : X, P x`, we can use the `obtain ⟨t,ht⟩ := h` tactic to generate a new hypothesis `t : X` for which `P t` and the witness for `P t` is `ht` (i.e. `ht : P t`).

**Universal quantifier** `∀` has one elimination rule. The corresponding Lean tactic is `apply`. This means whenever we have a hypothesis of the kind `⊢ ∀ x, P x`, we can use the `intro` tactic to introduce a new term `x : X` and a new hypothesis `h : P x` then prove the goal using `h`.


  connective    quantifier
------------ | ------------
    ∨        |   ∃
    ∧        |   ∀



  connective                  quantifier
-----------------        | ------------
    ∨ (indutive)         |   ∃ (inductive) -- for elimination cases/obtain works
    → (non-inductive)    |   ∀  (non-inductive) -- for elimination we use `apply`


-/


example : P ∧ ¬ Q → ¬ (P → Q) := by
  intro h
  have hp := h.left -- the left elimination of ∧
  have hnq := h.right -- the right elimination of ∧
  intro hpq
  apply hpq at hp
  contradiction

example  (h : P ∧ Q → R) (hp : P) (hq : Q) : R := by
  apply h
  constructor
  exact hp
  exact hq

section
#check (∀ x : ℕ, Odd x) → (Even 1) -- this is true, see the proof below
#check ∀ x : ℕ, (Odd x → Even 1) -- this is false, see the proof of its negation below
end


example : (∀ x : ℕ, Odd x) → (Even 1) := by
  intro h
  have odd : Odd 2 := by apply h 2 -- applying `h` to the term `2 : ℕ`
  exfalso
  unfold Odd at *
  obtain ⟨k, hk⟩ := odd
  -- use modular arithmetic to get `False` out of `hk`
  sorry

example : ¬ (∀ x : ℕ, (Odd x → Even 1)) := by
  intro h
  have h1 : Odd 1 → Even 1 := by apply h 1
  have h2 : Odd 1 := by
    unfold Odd
    use 0
    trivial
  apply h1 at h2
  obtain ⟨k, hk⟩ := h2
  -- use modular arithmetic to get `False` out of `hk`
  sorry


example {a : ℝ} (h : ∀ x, a ≤ x ^ 2 - 2 * x) : a ≤ -1 := by
  -- we have a proof of a univerally-quantified statement as our hypothesis, namely `h: ∀ (x : ℝ), a ≤ x ^ 2 - 2 * x` and we want to specialize it to a particular value so that we can prove the goal. So we have to cleverly find `t : ℝ` such that `a ≤ t^2 - 2 * t` helps us to prove `a ≤ -1`.
  -- have := by apply h 2  -- this does not help us
  -- ` x ^ 2 - 2 * x` takes its minimum at `x = 1`
  have := by apply h 1
  simp at this
  linarith


example : ∃ b : ℝ, ∀ x : ℝ, b ≤ x ^ 2 - 2 * x := by
  -- intro rule for ∃
  use -1
  -- we have to use the intro rule for ∀; let's assume an arbitrary `x`
  intro a
  --change (0 ≤ a^2 - 2 * a + 1) := by sorry
  have : 0 ≤ a^2 - 2 * a + 1 := by
    calc 0 ≤ (a - 1)^2 := by positivity
        _  = a^2 - 2 * a + 1 := by ring
  addarith [this]
