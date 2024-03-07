import Lake
open Lake DSL

package «proofs-S24» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «ProofsS24» {
  -- add any library configuration options here
}

require Duper from git "https://github.com/hrmacbeth/duper" @ "main"
