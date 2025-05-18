import Lake
open Lake DSL

package «something» {
  -- add package configuration options here
}

@[default_target]
lean_lib «Something» {
  -- add library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.3.0-rc2"
