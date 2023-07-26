variable (α : Type) (p q : α → Prop)
variable (r : Prop)
theorem deMorgans1 {p q : Prop} (h : ¬(p ∨ q)) : ¬p ∧ ¬q := by
  apply And.intro <;> intro h₁
  . have hpq : p ∨ q := Or.inl h₁
    apply absurd; assumption; assumption
  . have hpq : p ∨ q := Or.inr h₁
    apply absurd; assumption; assumption

example : α → ((∀ _ : α, r) ↔ r) := by
  intro x
  apply Iff.intro <;> intro h
  . exact h x
  . intro _; assumption


example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  apply Iff.intro <;> intro h
  . apply Classical.byContradiction
    intro h₁
    let ⟨hnAxpx, hnr⟩ := deMorgans1 h₁
    suffices h₂ : ∀ x, p x by apply absurd h₂; assumption
    intro x
    cases h x with
    | inl hpx => assumption
    | inr hr => exact absurd hr hnr
  . intro x
    apply Or.elim h <;> intro h₁ <;> have h₂ := h₁ x
    . constructor; assumption
    . exact Or.inr h₁

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  apply Iff.intro <;> intro h h₁ h₂ <;> exact h h₂ h₁
