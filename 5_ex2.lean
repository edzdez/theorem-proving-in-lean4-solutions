open Classical

variable (p q r : Prop)
theorem deMorgans1 {p q : Prop} (h : ¬(p ∨ q)) : ¬p ∧ ¬q := by
  apply And.intro
  . intro hp
    have hpq : p ∨ q := Or.inl hp
    apply absurd; assumption; assumption
  . intro hq
    have hpq : p ∨ q := Or.inr hq
    apply absurd; assumption; assumption
theorem dne {p : Prop} (h : ¬¬p) : p := by
  cases (em p) with
  | inl hp => exact hp
  | inr hnp => exact absurd hnp h

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro h
  apply byCases
  . intro h₁; have hqr := h h₁
    cases hqr;
    . apply Or.inl; exact λ _ : p => by assumption
    . apply Or.inr; exact λ _ : p => by assumption
  . intro h₁; constructor ; exact λ hp : p => absurd hp h₁

example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h
  apply byContradiction; intro h₁
  let ⟨hnnp, hnnq⟩ := deMorgans1 h₁
  exact absurd ⟨dne hnnp, dne hnnq⟩ h

example : ¬(p → q) → p ∧ ¬q := by
  intro h
  constructor <;> apply byContradiction <;> intro h₁
  . have hpq : p → q := λ hp : p => absurd hp h₁
    exact absurd hpq h
  . have hq : q := dne h₁
    have hpq : p → q := λ _ : p => hq
    exact absurd hpq h

example : (p → q) → (¬p ∨ q) := by
  intro h
  apply byCases
  . intro hp
    have hq := h hp
    exact Or.inr hq
  . intro hnp; exact Or.inl hnp

example : (¬q → ¬p) → (p → q) := by
  intro h hp
  apply byContradiction; intro hnq
  apply absurd; exact hp; apply h hnq

example : p ∨ ¬p := by
  apply byContradiction; intro h
  let ⟨hnp, hnnp⟩ := deMorgans1 h
  exact absurd (dne hnnp) hnp

example : (((p → q) → p) → p) := by
  intro h
  apply byCases
  . intro hp; assumption
  . intro hnp;
    exact h (λ hp: p => absurd hp hnp)

