/- Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sina Hazratpour.
-/

import ProofsS24.Project.Bit
import ProofsS24.Project.Decreasing

open Bit Decreasing

/-- Decreasing binary sequences as a subset of ℕ → 𝟚 -/
def CoNat := { β : ℕ → 𝟚 | Decreasing β }

namespace CoNat

scoped notation "ℕ[∞]" => CoNat

/-- Every co-natural number has an underlying binary sequence. -/
def seq (α : ℕ[∞]) : ℕ → 𝟚 := α.1

instance : Zero ℕ[∞] := ⟨zeroSeq, by intro; rfl⟩

instance : One ℕ[∞] := ⟨oneSeq, by intro; rfl⟩

def infinity : ℕ[∞] := ⟨fun _ => one, by intro; rfl⟩

-- Since we have an order on 𝟚, we immediately get an order on the function type ℕ → 𝟚: The order is point-wise meaning that `α ≤ β` iff `α n ≤ β n` for every index `n`.
lemma BinSeq_le (α β : ℕ → 𝟚) : α ≤ β ↔ ∀ n, α n ≤ β n := by
  rfl

-- Since ℕ[∞] is a subtype of the function type `ℕ → 𝟚`, it naturally inherits the order from `ℕ → 𝟚`.
lemma CoNat_le (α β : ℕ[∞]) : α ≤ β ↔ ∀ n, α.1 n ≤ β.1 n := by
  rfl

lemma le_infinity {β : ℕ[∞]} : β ≤ infinity := by
  intro n
  exact le_one

/-- We can construct from a binary sequence a co-natural number. -/
def ofBinSeq (β : ℕ → 𝟚) : ℕ[∞] := ⟨Decreasing.mk β, Decreasing.mk_is_decreasing β⟩

def ofNat (n : ℕ) : ℕ[∞] :=  ⟨binSeqOf n, binSeqOf_decreasing n⟩




end CoNat
