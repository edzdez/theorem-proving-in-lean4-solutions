variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  have h₁ := (h barber)
  have hnsbb : ¬ shaves barber barber := by
    intro hsbb
    apply absurd; assumption; apply h₁.mp; assumption
  suffices hsbb : shaves barber barber from absurd hsbb hnsbb
  apply h₁.mpr; assumption
