import Lake
open Lake DSL

def leanVersion : String := s!"v{Lean.versionString}"

package «algebra-in-lean» where
  leanOptions :=
    #[ ⟨`pp.unicode.fun, true⟩
     , ⟨`autoImplicit, false⟩
     , ⟨`relaxedAutoImplicit, false⟩
     ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ leanVersion

@[default_target]
lean_lib «AlgebraInLean» where
  -- add library configuration options here

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ leanVersion
