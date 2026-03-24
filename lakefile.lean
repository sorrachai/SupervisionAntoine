import Lake
open Lake DSL

package "MasterThesis" where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0-rc7"

require cslib from git
  "https://github.com/leanprover/cslib.git" @ "main"

lean_lib «MasterThesis» where
  -- add library configuration options here

@[default_target]
lean_exe "master_thesis" where
  root := `Main
