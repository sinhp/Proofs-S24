
import Mathlib.Tactic
import ProofsS24.Project.Bit



#check 2
#check 𝟚

open Bit

-- i : ℕ → (ℕ → 𝟚)
def i : ℕ → ℕ → 𝟚 := fun n => (fun m => if m = n then 1 else 0)

#check i 2  -- this is a sequence of 0s and 1s

#check i 2 1 -- this is a binary value

-- (i 2) 1
#eval i 2 1 -- this is Bit.one
