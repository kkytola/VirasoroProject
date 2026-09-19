import Lake
open Lake DSL

require VirasoroProject from ".."
require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint"@"v4.34.0"

package VirasoroBlueprint where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib VirasoroBlueprint where
