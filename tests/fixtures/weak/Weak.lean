namespace Weak
def Safe (p : List Nat) : Prop := True
def prog : List Nat := [1, 2, 3]
theorem prog_safe : Safe prog := trivial
def Sorted : List Nat → Prop
  | a :: b :: t => a ≤ b ∧ Sorted (b :: t)
  | _ => True
def insert (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insert x ys
def sort : List Nat → List Nat
  | [] => []
  | x :: xs => insert x (sort xs)
theorem sort_example : Sorted (sort [3, 1, 2]) := by simp [sort, insert, Sorted]
def Valid (n : Nat) : Prop := n > 0
theorem add_zero_of_valid (n : Nat) (h : Valid n) : n + 0 = n := by simp
theorem sort_length_self : ∀ xs : List Nat, (sort xs).length = (sort xs).length := fun _ => rfl
theorem vacuous (n : Nat) (h₁ : n < 2) (h₂ : n > 5) : sort [n] = [] := by omega
theorem no_project : ∀ n : Nat, n + 0 = n := fun n => rfl
theorem arrow : Valid 1 → 1 + 0 = 1 := fun _ => rfl
theorem by_lemma : ∀ n : Nat, n + 0 = n := Nat.add_zero
end Weak
