namespace Budget

-- With tag replaced by a variable, the kernel re-checks light in 350k to 400k heartbeats and heavy in
-- 600k to 700k, on v4.35.0 and v4.36.0. test_cli builds the sanity helper with 500k heartbeats per
-- re-check: light fits, even a second time, and heavy does not.
def tag : Nat := 0

set_option maxRecDepth 8000 in
theorem light : tag = tag ∧ ((List.range 74).all fun i => (List.range 74).all fun j => i + j < 148) = true :=
  ⟨rfl, by decide⟩

set_option maxRecDepth 8000 in
theorem heavy : tag = tag ∧ ((List.range 100).all fun i => (List.range 100).all fun j => i + j < 200) = true :=
  ⟨rfl, by decide⟩

end Budget
