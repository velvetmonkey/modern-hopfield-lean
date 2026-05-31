import Lake
open Lake DSL

require "leanprover-community" / "mathlib" @ git "v4.28.0"

package «ModernHopfield» where

@[default_target]
lean_lib «ModernHopfield» where
