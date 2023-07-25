variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have h₁ : shaves barber barber ↔ ¬ shaves barber barber := h barber
  have hnsbb : ¬ shaves barber barber :=
    λ hsbb : shaves barber barber =>
    have hnsbb : ¬ shaves barber barber := h₁.mp hsbb
    absurd hsbb hnsbb
  have hsbb : shaves barber barber := h₁.mpr hnsbb
  absurd hsbb hnsbb
