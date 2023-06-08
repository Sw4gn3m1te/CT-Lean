import Lake
open Lake DSL

package «cT-Lean» {
  -- add any package configuration options here
}

lean_lib «TM» {
  -- add library configuration options here
}

lean_lib «Decidability» {
  -- add library configuration options here
}

lean_lib «Language» {
  -- add library configuration options here
}


require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «CTLean» {
  -- add any library configuration options here
}
