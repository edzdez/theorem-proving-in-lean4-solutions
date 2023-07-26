variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  apply Iff.intro <;> intro h
  . apply And.intro <;> intro x <;> let ⟨hpx, hqx⟩ := h x <;> assumption
  . intro x
    apply And.intro
    apply h.left x
    apply h.right x

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro h h₁ x
  apply h; apply h₁

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro h x
  apply Or.elim h <;> intro h₁ <;> have h₂ := h₁ x
  . constructor; assumption
  . apply Or.inr; assumption
