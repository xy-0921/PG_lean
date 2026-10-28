import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

package PG_lean where
  -- add package configuration options here

@[default_target]
lean_lib PG_lean where
  roots := #[`PG_lean_0, `PG_lean_1, `PG_lean_2, `property20_Morley]
