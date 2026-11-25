namespace Reach

-- The kernel accepts safe's proof with threshold replaced by any number: rfl unfolds isHigh, which
-- still names the real threshold. Yet the claim does not hold whatever threshold is: isHigh is
-- made of it. So threshold is never tried, because isHigh, in the statement too, reaches it.
def threshold : Nat := 10
def isHigh (n : Nat) : Bool := n > threshold
theorem safe (h : threshold > 0) : isHigh 20 = true := rfl

-- even and odd are one mutual block. Lean compiles each to helpers that neither names the other, so
-- the kernel accepts even_two's proof with odd replaced by anything, though even is made of odd.
mutual
def even : Nat → Bool
  | 0 => true
  | n + 1 => odd n
def odd : Nat → Bool
  | 0 => false
  | n + 1 => even n
end
theorem even_two : even 2 = true ∨ odd 2 = true := Or.inl rfl

end Reach
