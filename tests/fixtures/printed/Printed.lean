/-! What the report prints: nanoda_bin prints a definition with an implicit or instance binder as
`fun` over its value's own binder names, and a statement's hypothesis after an implicit binder as an
arrow. leanexport shares one expression among those equal but for binder names, so a type's binder
names can be another declaration's. -/
namespace Printed

def Pos (m : Nat) (n : Nat) : Prop := m > 0

def P2 {α : Type} (m n : Nat) : Prop := n > 0

def P4 [Inhabited Nat] (m n : Nat) : Prop := n > 0

theorem pos : Pos 1 0 := Nat.one_pos

theorem u2 : P2 (α := Unit) 0 1 := Nat.one_pos

theorem u4 : P4 0 1 := Nat.one_pos

theorem t5 {α : Type} (xs : List α) (h : xs ≠ []) : xs.length = xs.length := rfl

end Printed
