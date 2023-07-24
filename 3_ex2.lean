open Classical

variable (p q r : Prop)
theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)
theorem deMorgans1 {p q : Prop} (h : ¬(p ∨ q)) : ¬p ∧ ¬q :=
  And.intro
    (fun hp : p => absurd (Or.inl hp) h)
    (fun hq : q => absurd (Or.inr hq) h)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  λ h : p → q ∨ r =>
    byCases
      (λ hp : p =>
        have hqr : q ∨ r := h hp
        Or.elim hqr
          (λ hq : q =>
            Or.inl (λ _ : p => hq))
          (λ hr : r =>
            Or.inr (λ _ : p => hr)))
      (λ hnp : ¬p =>
        suffices hpq : p → q from Or.inl hpq
        (λ hp : p =>
          absurd hp hnp))

theorem deMorgans2 {p q : Prop} (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  byContradiction
    (λ h₁ : ¬(¬p ∨ ¬q) =>
      have h₁' : ¬¬p ∧ ¬¬q := deMorgans1 h₁
      have h₁'' : p ∧ q := And.intro (dne h₁'.left) (dne h₁'.right)
      absurd h₁'' h)

example : ¬(p → q) → p ∧ ¬q :=
  λ h : ¬(p → q) => And.intro
    (byContradiction
      (λ hnp : ¬p =>
        have hpq : p → q := (λ hp : p => absurd hp hnp)
        absurd hpq h))
    (byContradiction
      (λ hq : ¬¬q =>
        have hpq : p → q := (λ _ : p => dne hq)
        absurd hpq h))

example : (p → q) → (¬p ∨ q) :=
  λ h : p → q =>
    byCases
      (λ hp : p => Or.inr (h hp))
      (λ hnp : ¬p => Or.inl hnp)

example : (¬q → ¬p) → (p → q) :=
  λ h : ¬q → ¬p =>
  byCases
    (λ hq : q =>
      byContradiction
        (λ h₁ : ¬(p → q) =>
          have hpq : p → q := λ _ : p => hq
          absurd hpq h₁))
    (λ hnq : ¬q =>
      have hnp : ¬p := h hnq
      (λ hp : p => absurd hp hnp))

-- this feels like circular logic to me...
example : p ∨ ¬p :=
  byCases
    (λ hp : p => Or.inl hp)
    (λ hnp : ¬p => Or.inr hnp)

example : (((p → q) → p) → p) :=
  λ h : ((p → q) → p) =>
    byContradiction
      (λ hnp : ¬p =>
        have hpq : p → q := λ hp : p => absurd hp hnp
        have hp : p := h hpq
        absurd hp hnp)
