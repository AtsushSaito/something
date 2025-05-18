def hello := "world"

theorem identity (n : Nat) : n = n := by
  rfl

theorem add_comm (a b : Nat) : a + b = b + a := by
  induction a with
  | zero =>
    rw [Nat.zero_add]
    rw [← Nat.add_zero b]
  | succ n ih =>
    rw [Nat.succ_add, ih, Nat.add_succ]
