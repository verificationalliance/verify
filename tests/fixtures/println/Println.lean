/-! This project's own top-level `println`. LeanChecker, a library of the toolchain that the project
does not import, declares one too; the check must take this one as the project's own, and pass. -/
def println (n : Nat) : Nat := n + 1

theorem Println.t : println 1 = 2 := rfl
