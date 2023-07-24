example : ¬(p ↔ ¬p) :=
  λ h : p ↔ ¬p =>
    have hnp : ¬p :=
      (λ hp : p =>
        have hnp : ¬p := h.mp hp
        absurd hp hnp)
    have hp : p := h.mpr hnp
    absurd hp hnp
