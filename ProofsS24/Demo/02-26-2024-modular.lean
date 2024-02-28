import Mathlib.Tactic.Ring
import ProofsS24.Tactic.Addarith
import ProofsS24.Tactic.Cancel
import ProofsS24.Tactic.ModCases

def Odd (a : ℤ) : Prop := ∃ (k : ℤ), a = 2 * k + 1
def Even (a : ℤ) : Prop := ∃ (k : ℤ), a = 2 * k


example (hab : A ∨ B) (h1 : A → P) (h2: B → Q) : P ∨ Q := by
  cases' hab with ha hb
  · left
    -- use the hypotheses `ha : A` and `h1 : A → P` by the elimination rule of implication
    apply h1 at ha
    exact ha
  · right
  -- the goal is to prove `Q`, and by the virue of the implication `B → Q` it is sufficient to prove `B`
    apply h2
    exact hb


lemma Int.even_or_odd (n : ℤ) : Even n ∨ Odd n := by
-- divided n by 2. By the Euclid's division theorem the remainder of this division is either `0` or `1`.
-- Euclid's theorem says for all integers `a` and `b` we can find unique `q` (quotient) and `r` (remainder) such that `a =  b * q + r` and `0 ≤ r < b`, e.g. `13 = 4 * 4 + (-3)` and `13 = 4 * 3 + 1`, but only the second one is a valid Euclidean division.
-- `n = 2 * q + r` with unique `q` and `r` and `0 ≤ r < 2`. Therfore, `r = 0` or `r = 1`. If `r = 0`, then `n = 2 * q` and as such `n` is even.  If `r = 1`, then `n = 2 * q + 1 ` and as such `n` is odd.
sorry

#check 2 ∣ 4 -- the proposition that 2 divides 4
#check 2 ∣ 3 -- the proposition that 2 divides 3

#check Dvd.dvd -- ∣

example (a b : ℤ) : a ∣ b ↔ ∃ c, b = a * c := by rfl

lemma divides.transitive (a b c : ℤ) : a ∣ b → b ∣ c → a ∣ c := by
  intro h1 h2
  change ∃ k, c = a * k
  -- use b -- not a good choice since we end up with an impossible goal
  --dsimp [Dvd.dvd] at h2
  -- obtain ⟨k, hk⟩ := h2 -- we have no control over k
  -- before proposing `k` in th goal we simplify our hypotheses.
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  rw [hk2, hk1]
  use k1 * k2
  rw [mul_assoc]

lemma divides.reflexive (a: ℤ) : a ∣ a := by
  change ∃ k, a = a * k
  use 1
  ring
  --linarith
  --rw [mul_one]



-- 88 = 8 * 11 -- 8 ∣ 88 but ¬ (88 ∣ 8)
example (a b : ℤ) : ¬ (a ∣ b → b ∣ a) := by
  -- proof by negation
  intro h
  -- let's drive false out of `h`
  -- we want to use `h` which is a proof of an implication but we don't have another assumption to which `h` can be applied.
  -- impossible to proof because of the following examples
  sorry

example : 1 ∣ (-1) := by
  use -1
  ring

example : -1 ∣ 1 := by
  use -1
  ring

-- statement that divisibility is not symmetric.
example : ¬ ∀ a b : ℤ, (a ∣ b → b ∣ a) := by sorry

-- challenge
example {a b : ℕ} (hab : a ∣ b) (hb : 0 < b) : 0 < a := by
  sorry


example (n : ℤ) : Even n ∨ Odd n := by
  mod_cases hn : n % 2
  · left
    rw [Int.even_iff_modEq]
    apply hn
  · sorry

lemma three_divides_cube_sub_self {x : ℤ} : 3 ∣ x^3 - x := by
  change ∃ k, x^3 - x = 3 * k
  have : x^3 - x = x * (x - 1) * (x + 1) := by
    calc
      x^3 - x = x * (x^2 - 1) := by ring
      _ = x * (x - 1) * (x + 1) := by ring


lemma mod_equiv_divide {x : ℤ} : x ^ 3 ≡ x [ZMOD 3] ↔ 3 ∣ x^3 - x := by
  sorry

example {x : ℤ} : x ^ 3 ≡ x [ZMOD 3] := by
  apply mod_equiv_divide.mpr
  exact three_divides_cube_sub_self


example (x : ℤ) (h : x ≡ 0 [ZMOD 3]): (x^3 ≡ 0 [ZMOD 3]) := by
  change 3 ∣ x^3 - 0
  obtain ⟨k, hk⟩ := h
  rw [sub_zero] at hk
  use 9 * k^3
  rw [hk]
  ring_nf

example (h : x ≡ 0 [ZMOD 3]) : 0 ≡ x [ZMOD 3] := by
  obtain ⟨k, hk⟩ := h
  change ∃ k', 0 - x = 3 * k'
  have : 0 - x = 3 * (-k) := by
    calc
      0 - x = - (x - 0) := by ring
            _     = - (3 * k) := by rw [hk]
            _     = 3 * (-k) := by ring
  use -k

--
example {x : ℤ} : x ^ 3 ≡ x [ZMOD 3] := by
  -- by proving the goal in three different subgoals which exhaust all possibilities
  -- for `x`: either `x= 3*k` or `x =3 *k +1` or `x = 3*k + 2`
  mod_cases hx : x % 3
  calc
    x ^ 3 ≡ 0 ^ 3 [ZMOD 3] := by rel [hx]
    _ = 0 := by ring
    _ ≡ x [ZMOD 3] := by rel [hx]
  calc
    x ^ 3 ≡ 1 ^ 3 [ZMOD 3] := by rel [hx]
    _ = 1 := by sorry
    _ ≡ x [ZMOD 3] := by rel [hx]
  calc
    x ^ 3 ≡ 2 ^ 3 [ZMOD 3] := by rel [hx]
    _ = 2 + 3 * 2 := by sorry
    _ ≡ 2 [ZMOD 3] := by sorry
    _ ≡ x [ZMOD 3] := by rel [hx]
