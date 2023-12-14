import Lake
open Lake DSL


require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require verbose from git
  "https://github.com/mmasdeu/verbose-lean4"

package «fonaments» {
  -- add any package configuration options here
}
@[default_target]
lean_lib «Fonaments» {
  -- add any library configuration options here
}
