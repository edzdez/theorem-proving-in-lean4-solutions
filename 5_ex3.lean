example : ¬ (p ↔ ¬ p) := by
  intro h
  have hnp : ¬ p := by
    intro hp
    exact absurd hp (h.mp hp)
  apply absurd; exact h.mpr hnp; assumption
