import LeanExport.Parse

/-! Not the toolchain's `LeanExport.dumpEnv`: this project's own declaration under that name, which
it can make because it imports LeanExport.Parse but not LeanExport.Basic, where the real one is.
The check must compare it with the toolchain's and reject it. -/
def LeanExport.dumpEnv : Nat := 1

theorem Forge.t : LeanExport.dumpEnv = 1 := rfl
