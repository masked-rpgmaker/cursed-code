import Lake
open Lake DSL

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.0.0"

package «cursed» {}

lean_lib «Cursed» {}

lean_exe «cursed-func» { root := `MainFunc }

lean_exe «cursed-structured» { root := `MainStructured }

lean_exe «cursed-oop» { root := `MainOOP }
