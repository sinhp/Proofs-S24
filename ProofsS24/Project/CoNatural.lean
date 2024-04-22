/- Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sina Hazratpour.
-/

import ProofsS24.Project.Bit
import ProofsS24.Project.Decreasing

open Bit Decreasing Function

/-- Decreasing binary sequences as a subset of ℕ → 𝟚 -/
def CoNat := { β : ℕ → 𝟚 | Decreasing β }

namespace CoNat

scoped notation "ℕ[∞]" => CoNat

/-- Every co-natural number has an underlying binary sequence. -/
def seq (α : ℕ[∞]) : ℕ → 𝟚 := α.1

instance : Zero ℕ[∞] := ⟨zeroSeq, by intro; rfl⟩

instance : One ℕ[∞] := ⟨oneSeq, by intro; rfl⟩

def infinity : ℕ[∞] := ⟨fun _ => one, by intro; rfl⟩

scoped notation "∞" => infinity

-- Since we have an order on 𝟚, we immediately get an order on the function type ℕ → 𝟚: The order is point-wise meaning that `α ≤ β` iff `α n ≤ β n` for every index `n`.
lemma BinSeq_le (α β : ℕ → 𝟚) : α ≤ β ↔ ∀ n, α n ≤ β n := by
  rfl

#check Lex

instance : LE (Lex BinSeq) := sorry


-- Since ℕ[∞] is a subtype of the function type `ℕ → 𝟚`, it naturally inherits the order from `ℕ → 𝟚`.
lemma CoNat_le (α β : ℕ[∞]) : α ≤ β ↔ ∀ n, α.1 n ≤ β.1 n := by
  rfl

example : ¬ ∃ n : ℕ, ∀ m : ℕ, m ≤ n := by
  intro h
  obtain ⟨N,h⟩ := h
  specialize h (N+1)
  linarith

-- unlike natural numbers, co-natural numbers are not bounded
lemma le_infinity : ∀ β : ℕ[∞], β ≤ ∞ := by
  intro β n
  exact le_one

/-- We can construct from a binary sequence a co-natural number by forcing it to be decreasing using the function `Decreasing.mk`. -/
def ofBinSeq (β : ℕ → 𝟚) : ℕ[∞] := ⟨Decreasing.mk β, Decreasing.mk_is_decreasing β⟩

@[simp]
lemma ofBinSeq_left_inverse (α : ℕ[∞]) : ofBinSeq α = α := by
  cases' α with a h
  simp only [Subtype.mk.injEq]
  ext x
  -- dsimp [OfBinSeq]
  -- apply mk_eq_self
  sorry

lemma left_inverse  : LeftInverse CoNat.ofBinSeq CoNat.seq := by
  simp only [Function.LeftInverse]
  intro x
  sorry

/-- The canonical embedding of ℕ into ℕ[∞]. -/
def ofNat (n : ℕ) : ℕ[∞] :=  ⟨binSeqOf n, binSeqOf_decreasing n⟩

instance coe : Coe ℕ ℕ[∞] := ⟨ofNat⟩

lemma injective_ofNat : Injective ofNat := by
  intro m n h
  simp only [ofNat, Subtype.mk.injEq] at h
  unfold binSeqOf at h
  cases' (lt_trichotomy m n) with h₁ h₂
  · exfalso
    have h' := congr_fun h m
    rw [if_pos h₁] at h'
    rw [if_neg (Nat.lt_irrefl m)] at h'
    simp only [Bit.zero_ne_one h']
  · cases' h₂ with h₃ h₄
    · assumption
    · exfalso
      have h' := congr_fun h n
      rw [if_pos h₄] at h'
      rw [if_neg (Nat.lt_irrefl n)] at h'
      simp only [Bit.zero_ne_one h'.symm]

/-- The successor function adds `1` to the beginning of the binary sequence. -/
def succ (n : ℕ[∞]) : ℕ[∞] := match n with
| ⟨α, h⟩ =>  ⟨BinSeq.cons one α, Decreasing.cons one α h⟩

lemma succ_ofNat (n : ℕ) : succ n = Nat.succ n := by
  simp [succ]
  ext i
  dsimp
  cases i with
  | zero => simp
            sorry
  | succ i => sorry


lemma succ_le (n : ℕ[∞]) : n ≤ succ n := by
  sorry

lemma succ_lt (n : ℕ) : n < succ n := by
  sorry

lemma succ_ne_zero (n : ℕ[∞]) : succ n ≠ 0 := by
  sorry

lemma succ_pos (n : ℕ[∞]) : 0 < succ n := by
  sorry

lemma succ_injective : ∀ n m : ℕ[∞], succ n = succ m → n = m := by
  sorry

-- unlike for the natural numbers `succ` has a fixed point in co-natural numbers
lemma succ_fixed_point (n : ℕ[∞]) : succ n = n ↔ n = ∞ := by
  sorry

/-- The predecessor function removes the first bit of the binary sequence. -/
def pred (n : ℕ[∞]) : ℕ[∞] := ⟨n.1 ∘ Nat.succ, sorry⟩

lemma pred_ofNat (n : ℕ) : pred n = Nat.pred n := by
  sorry

lemma pred_infinity : pred ∞ = ∞ := by
  sorry

lemma pred_le (n : ℕ[∞]) : pred n ≤ n := by
  sorry

lemma pred_lt (n : ℕ[∞]) : pred n < n := by
  sorry

lemma pred_succ (n : ℕ[∞]) : pred (succ n) = n := by
  sorry

lemma pred_zero : pred 0 = 0 := by
  sorry


end CoNat
