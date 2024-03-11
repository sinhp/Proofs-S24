/- Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sina Hazratpour.
-/

import Mathlib.Tactic
import ProofsS24.Project.Bit
import ProofsS24.Project.Decreasing

open Bit Decreasing

structure CoNat where
  seq : ℕ → 𝟚
  is_decreasing : Decreasing seq

namespace CoNat

scoped notation "ℕ∞" => CoNat

end CoNat
