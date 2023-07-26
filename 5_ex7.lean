open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _ : α, r) → r := by
  intro h
  apply Exists.elim h
  intro _ hr
  assumption

example (a : α) : r → (∃ _ : α, r) := by
  intro hr
  apply Exists.intro
  repeat assumption

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  apply Iff.intro <;> intro h
  . let ⟨x, hpxr⟩ := h
    apply And.intro; exact ⟨x, hpxr.left⟩; exact hpxr.right
  . let ⟨⟨x, hpx⟩, hr⟩ := h
    exact ⟨x, And.intro hpx hr⟩

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  apply Iff.intro <;> intro h
  . let ⟨x, hpxqx⟩ := h
    cases hpxqx with
    | inl hpx => exact Or.inl ⟨x, hpx⟩
    | inr hqx => exact Or.inr ⟨x, hqx⟩
  . cases h with
    | inl hExpx => let ⟨x, px⟩ := hExpx; exact ⟨x, Or.inl px⟩
    | inr hExqx => let ⟨x, qx⟩ := hExqx; exact ⟨x, Or.inr qx⟩

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  apply Iff.intro <;> intro h
  . intro hExnpx
    let ⟨x, hnpx⟩ := hExnpx
    apply absurd; exact h x; assumption
  . intro x
    apply byContradiction; intro hpnpx
    have hExpnpx: ∃ x, ¬ p x := ⟨x, hpnpx⟩
    exact absurd hExpnpx h

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  apply Iff.intro <;> intro h
  . let ⟨x, hpx⟩ := h
    intro hAxnpx
    exact absurd hpx (hAxnpx x)
  . apply byContradiction; intro h₁
    suffices h₂ : ∀ x, ¬ p x from absurd h₂ h
    intro x hpx
    exact absurd ⟨x, hpx⟩ h₁

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  apply Iff.intro <;> intro h
  . intro x hpx
    exact absurd ⟨x, hpx⟩ h
  . intro hExpx
    let ⟨x, px⟩ := hExpx
    apply absurd; assumption; exact h x

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
  apply Iff.intro <;> intro h
  . apply byContradiction; intro h₁
    suffices h₂ : ∀ x, p x from absurd h₂ h
    intro x
    apply byContradiction; intro hnpx
    exact absurd ⟨x, hnpx⟩ h₁
  . let ⟨x, hnpx⟩ := h
    intro h₁
    apply absurd; exact h₁ x; assumption

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
  apply Iff.intro <;> intro h
  . intro h₁
    let ⟨x, hpx⟩ := h₁
    apply h; assumption
  . intro x px
    apply h; exact ⟨x, px⟩

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  apply Iff.intro <;> intro h
  . intro h₁
    let ⟨x, pxr⟩ := h
    apply pxr; exact h₁ x
  . apply byCases
    . intro (hAxpx : ∀ x, p x)
      have hr : r := h hAxpx
      exact ⟨a, λ _ => hr⟩
    . intro (hnAxpx : ¬ ∀ x, p x)
      apply byContradiction <;> intro h₁
      suffices h₂ : ∀ x, p x from absurd h₂ hnAxpx
      intro x
      apply byContradiction <;> intro hnpx
      exact absurd ⟨x, λ hpx => absurd hpx hnpx⟩ h₁

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
  apply Iff.intro <;> intro h
  . let ⟨x, hrpx⟩ := h
    intro hr
    exact ⟨x, hrpx hr⟩
  . apply byCases
    . intro (hr : r)
      have ⟨x, hpx⟩ := h hr
      exact ⟨x, λ _ => hpx⟩
    . intro (hnr : ¬ r)
      apply byContradiction
      intro hnEarpa
      have hrpa : r → p a := λ hr : r => absurd hr hnr
      exact absurd ⟨a, hrpa⟩ hnEarpa


