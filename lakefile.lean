import Lake
open Lake DSL

def leanVersion : String := s!"v{Lean.versionString}"

package «algebra-in-lean» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ leanVersion

@[default_target]
lean_lib «AlgebraInLean» where
  -- add library configuration options here
