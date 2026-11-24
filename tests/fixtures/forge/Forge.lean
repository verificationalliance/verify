/-! Not the toolchain's `LeanExport.dumpEnv`: this project's own declaration under that name, which
it can make because it does not import LeanExport. The check must compare it with the toolchain's
LeanExport library, which is not one of Init, Std, Lean and Lake, and reject it. -/
def LeanExport.dumpEnv : Nat := 1

theorem Forge.t : LeanExport.dumpEnv = 1 := rfl
