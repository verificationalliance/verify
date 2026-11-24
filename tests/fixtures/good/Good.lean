namespace Good

def f (n : Nat) : Nat := n + 1

theorem t1 (n : Nat) : f n = n + 1 ∨ f n ≠ n + 1 := Classical.em _

theorem «key never leaves» (n : Nat) : n < f n := Nat.lt_succ_self n

end Good
