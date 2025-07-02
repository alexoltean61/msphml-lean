import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

require aesop from git "https://github.com/leanprover-community/aesop"

package «hybrid» where
  -- add package configuration options here

lean_lib «Hybrid» where
  -- add library configuration options here

@[default_target]
lean_exe «hybrid» where
  root := `Main
