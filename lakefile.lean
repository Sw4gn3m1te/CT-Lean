import Lake
open Lake DSL

package «cT-Lean» {
  -- add package configuration options here
}

lean_lib «CTLean» {
  -- add library configuration options here
}


lean_lib «TM» {
  -- add library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_exe «cT-Lean» {
  root := `Main
}
