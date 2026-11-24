namespace Good

def f (n : Nat) : Nat := n + 1

theorem t1 (n : Nat) : f n = n + 1 ∨ f n ≠ n + 1 := Classical.em _

theorem «key never leaves» (n : Nat) : n < f n := Nat.lt_succ_self n

end Good

/-! As in OSVA Monitor's core: a structure, and definitions through `match` and structural recursion,
which the report shows by their headers. -/
namespace Good

structure Range where
  lo : Nat
  hi : Nat

def Range.contains (r : Range) (v : Nat) : Bool := r.lo ≤ v && v < r.hi

def anyIn (rs : List Range) (v : Nat) : Bool := rs.any (·.contains v)

def lowest : List Nat → Nat
  | [] => 0
  | x :: xs => min x (lowest xs)

def pick (o : Option Nat) : Nat :=
  match o with
  | none => 0
  | some n => n

theorem anyIn_nil (v : Nat) : anyIn [] v = false := rfl

theorem pick_lowest (xs : List Nat) : pick (some (lowest xs)) = lowest xs := rfl

end Good
