example {a b c : Nat} (h₁ : a = b) (h₂ : b = c) : a = c := by calc
  a = b := by exact h₁
  _ = c := by exact h₂
