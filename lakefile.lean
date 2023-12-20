import Lake
open Lake DSL

package «primality-tests»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib PrimalityTests

lean_exe «miller-rabin» where
  root := `PrimalityTests.MillerRabin
