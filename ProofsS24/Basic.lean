import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Set
import ProofsS24.Config.Constructor
import ProofsS24.Config.Contradiction
import ProofsS24.Config.ExistsDelaborator
import ProofsS24.Config.Initialize
import ProofsS24.Config.Ring
import ProofsS24.Config.Set
import ProofsS24.Config.Use
import ProofsS24.Theory.Comparison
import ProofsS24.Theory.Parity
import ProofsS24.Theory.Prime
import ProofsS24.Tactic.Addarith
import ProofsS24.Tactic.Cancel
import ProofsS24.Tactic.Extra.Basic
import ProofsS24.Tactic.Induction
import ProofsS24.Tactic.Numbers.Basic
import ProofsS24.Tactic.Obtain
import ProofsS24.Tactic.TruthTable

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

macro "linarith" linarithArgsRest : tactic => `(tactic | fail "linarith tactic disabled")
macro "nlinarith" linarithArgsRest : tactic => `(tactic | fail "nlinarith tactic disabled")
macro "linarith!" linarithArgsRest : tactic => `(tactic | fail "linarith! tactic disabled")
macro "nlinarith!" linarithArgsRest : tactic => `(tactic | fail "nlinarith! tactic disabled")
macro "polyrith" : tactic => `(tactic | fail "polyrith tactic disabled")
macro "decide" : tactic => `(tactic | fail "decide tactic disabled")
macro "aesop" : tactic => `(tactic | fail "aesop tactic disabled")
macro "tauto" : tactic => `(tactic | fail "tauto tactic disabled")

open Lean.Parser.Tactic in
macro "simp"  (&" only")?  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*) "]")?
  (location)? : tactic => `(tactic | fail "simp tactic disabled")

/--
Configure the environment with the right options and attributes
for the book *The Mechanics of Proof*.

Tries to perform essentially the following:

```
set_option push_neg.use_distrib true

attribute [-simp] ne_eq
attribute [-ext] Prod.ext
attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat
attribute [-norm_num] Mathlib.Meta.NormNum.evalNatDvd
  Mathlib.Meta.NormNum.evalIntDvd
```
-/
elab "math2001_init" : command => do
  trySetOptions #[
    ⟨`push_neg.use_distrib, true⟩
  ]
  tryEraseAttrs #[
    ⟨`simp, #[`ne_eq]⟩,
    ⟨`ext, #[`Prod.ext]⟩,
    ⟨`instance, #[`Int.instDivInt_1,`Int.instDivInt, `Nat.instDivNat]⟩,
    ⟨`norm_num, #[`Mathlib.Meta.NormNum.evalNatDvd, `Mathlib.Meta.NormNum.evalIntDvd]⟩
  ]
