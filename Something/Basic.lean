def hello := "world"

theorem identity (n : Nat) : n = n := by
  rfl

theorem add_comm (a b : Nat) : a + b = b + a := by
  induction a with
  | zero =>
    simp
  | succ n ih =>
    simp
    rw [ih]
    rfl
