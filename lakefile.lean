import Lake
open Lake DSL

package «formalization-of-mathematics-2024» where
  -- add package configuration options here

lean_lib «FormalizationOfMathematics2024» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_exe «formalization-of-mathematics-2024» where
  root := `Main
