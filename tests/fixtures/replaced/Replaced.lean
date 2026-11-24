namespace Replaced

def doubleImpl (n : Nat) : Nat := n * 2

@[implemented_by doubleImpl]
def double (n : Nat) : Nat := n + n

theorem double_eq (n : Nat) : double n = n + n := rfl

end Replaced
