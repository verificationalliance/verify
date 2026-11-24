prelude

/-- Not Lean's `Eq`: any two values are "equal". -/
inductive Eq {α : Sort u_1} : α → α → Prop where
  | any (a b : α) : Eq a b

theorem FakeEq.t {α : Sort u_1} (a b : α) : Eq a b := Eq.any a b
