import Mathlib.Tactic.Ring
import ProofsS24.Tactic.Addarith
import ProofsS24.Tactic.Cancel

/-! ### Biimplication, or otherwise known as If and Only If
The biimplication ` ↔ ` is a derived connective which is derived form `→` and `∧`. For propositions `P` and `Q`, we write `P ↔ Q` -- read as "P if and only if Q" -- for `(P → Q) ∧ (Q → P)`. Therefore `P ↔ Q = (P → Q) ∧ (Q → P)` by definition. And, as such, we can apply the tactic `split` to introduce a proof of `P ↔ Q` and `cases` to eliminate proofs of `P ↔ Q`.
-/

/-
**Note** The `constructor` tactic applies the unique constructor for conjunction, namely `and.intro`.
-/


/-
Recall the rules of deduction for conjunction:

1. Conjunction Introduction:


  ---  ---
    P   Q
   -------- ∧-intro
    P ∧ Q

The canonical way to construct a proof of `P ∧ Q` is to apply `And.intro` to suitable proofs `hp : p` and `hq : q`


2. Conjunction Elimination:

    P ∧ Q
   -------- ∧-elim_left
      P

    P ∧ Q
   -------- ∧-elim_right
      Q

 What if `hpq : P ∧ Q` is a hypothesis, and we want to use it? Then by the rules above we decompose `hpq` into `hpq.left : P ` and `hpq.right : Q` to get proofs of `P` and `Q` respectively.
-/

theorem conj_comm : P ∧ Q ↔ Q ∧ P := by
  constructor
  -- the forward direction: `P ∧ Q → Q ∧ P`
  · intro h
    constructor
    -- conjunction right elimination (∧-elim_right)
    · exact h.right
    · exact h.left
  -- the backward direction of ↔ : `Q ∧ P → P ∧ Q`
  · intro h
    exact ⟨h.right , h.left⟩


example : P ∧ Q ↔ Q ∧ P := by
exact ⟨fun h ↦ ⟨h.right, h.left⟩ , fun h ↦ ⟨h.right, h.left⟩⟩

example : P ∧ Q ↔ Q ∧ P := ⟨fun h ↦ ⟨h.right, h.left⟩, fun h ↦ ⟨h.right, h.left⟩⟩

/-
If we have a proof `h` of P ↔ Q then we can get `h.mp : P → Q` and `h.mpr : Q → P`.
-/

example (h : P ↔ Q) : P → Q := h.mp -- h.mp = h.1

example (h : P ↔ Q) : Q → P := h.mpr -- h.mpr = h.2

example : (P → Q) ↔ (¬P ∨ Q) := by
  constructor
  · intro h1
  -- By the law of excluded middle, either `P` or not `P`. If P is true then since we know `P → Q` is true therefore by implication elimination we have `Q`, which implies `¬ P ∨ Q`. On the other hand if `¬ P` is true then `¬P ∨ Q` is true.
    have h2 : P ∨ ¬ P := by exact em P
    cases' h2 with h21 h22
    · right
      exact h1 h21
    · left
      exact h22
  · intro h1
    intro h2
    cases' h1 with h11 h12
    · contradiction
    · exact h12

/-
- `P ∨ Q` means __"P or Q"__. To prove `P ∨ Q`, we need to choose one of `P` or `Q`, and prove that one.

If `⊢ P ∨ Q` is our goal, then

- if we have a proof `hp : P`, then term `Or.inl hp` (short for `Or.intro_left`) proves `P ∨ Q`, i.e. `Or.inl hp : P ∨ Q`.

- if we have a proof `hq : Q`, then term `Or.inr hq` (short for `Or.intro_right`) proves `P ∨ Q`, i.e. `Or.inr hq : P ∨ Q`.

      P
   -------- ∨-intro-left
    P ∨ Q



      Q
   -------- ∨-intro-right
     P ∨ Q

The elimination rule for disjunction (`∨`) is slightly more complicated. Let's think about it: suppose we know that `P ∨ Q` is true; of course this does not tell us which is the case: that we `P` is true or whether `Q` is true. All we know is that at least one of them is true. So, if we want to prove some other proposition `R` we should prove that `R` follows from `P` and that `R` follows from `Q`. In other words, it is a proof by cases.


 hpq : P ∨ Q     P        Q
                .        .
                .        .
                .        .
                R        R
----------------------------
            R

The tactic `cases' hpq with hp hq` corresponds to disjunction elimination.
-/


/-
The rules of deduction for existential quantifier

m    P m
------------- (intro rule for ∃)
∃ n, P n

the tactic corresponding to this rule is `use`

              for an arbitrary m, P m
                .
                .
∃ n, P n        R
-------------------
R

-/



/- The rules of deduction for existential quantifier are a more general case of the rules of deduction for disjunction. -/

inductive Two where
 | pos
 | neg

#check Two

#check Two.pos
#check Two.neg



variable (P : Two → Prop) -- P(pos) , P (neg)

example : (∃ t : Two, P t) ↔ P (Two.pos) ∨ P (Two.neg) := by
  constructor
  · intro h
    cases' h with t ht
    cases t with
    | pos => exact Or.inl ht
    | neg => exact Or.inr ht
  . intro h
    cases' h with h1 h2
    · use Two.pos
    · use Two.neg


example : (∃ t : Two, P t) ↔ P (Two.pos) ∨ P (Two.neg) := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := h -- cases' h with t ht
    cases t with
    | pos => exact Or.inl ht
    | neg => exact Or.inr ht
  . intro h
    cases' h with h1 h2
    · use Two.pos
    · use Two.neg
