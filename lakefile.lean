import Lake
open Lake DSL

def leanVersion : String := s!"v{Lean.versionString}"

package «formalization-of-mathematics-2024» where
  -- add package configuration options here

lean_lib «FormalizationOfMathematics2024» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ leanVersion

@[default_target]
lean_exe «formalization-of-mathematics-2024» where
  root := `Main
