variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro <;> intro h <;> apply And.intro h.right h.left

example : p ∨ q ↔ q ∨ p := by
  apply Iff.intro <;> intro h <;> cases h <;> first | apply Or.inl; assumption | apply Or.inr; assumption

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  apply Iff.intro <;> intro h
  . have hp := h.left.left
    have hqr := And.intro h.left.right h.right
    apply And.intro hp hqr
  . have hpq := And.intro h.left h.right.left
    have hr := h.right.right
    apply And.intro hpq hr

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro <;> intro h
  . apply Or.elim h <;> intro h₁
    . apply Or.elim h₁ <;> intro h₂
      . exact Or.inl h₂
      . have hqr : q ∨ r := Or.inl h₂
        exact Or.inr hqr
    . exact Or.inr (Or.inr h₁)
  . apply Or.elim h <;> intro h₁
    . exact Or.inl (Or.inl h₁)
    . apply Or.elim h₁ <;> intro h₂
      . exact Or.inl (Or.inr h₂)
      . exact Or.inr h₂

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro <;> intro h
  . let ⟨hp, hqr⟩ := h
    cases hqr with
    | inl hq => exact Or.inl (And.intro hp hq)
    | inr hr => apply Or.inr; apply And.intro; exact hp; exact hr
  . cases h with
    | inl hpq => let ⟨hp, hq⟩ := hpq; apply And.intro hp; apply Or.inl; exact hq
    | inr hpr => let ⟨hp, hr⟩ := hpr; apply And.intro hp; apply Or.inr; assumption

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro <;> intro h
  . cases h with
    | inl hp => exact And.intro (Or.inl hp) (Or.inl hp)
    | inr hqr => exact And.intro (Or.inr hqr.left) (Or.inr hqr.right)
  . let ⟨hpq, hpr⟩ := h
    cases hpq with
    | inl hp => exact Or.inl hp
    | inr hq => cases hpr with
      | inl hp => exact Or.inl hp
      | inr hr => exact Or.inr (And.intro hq hr)

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  apply Iff.intro
  . intros h hpq
    let ⟨hp, hq⟩ := hpq
    exact (h hp) hq
  . intros hpqr hp hq
    apply hpqr; apply And.intro; assumption; assumption

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  apply Iff.intro <;> intro h
  . apply And.intro <;> intro h₁
    . apply h (Or.inl h₁)
    . apply h (Or.inr h₁)
  . let ⟨hpr, hqr⟩ := h
    intro hpq
    cases hpq <;> first | apply hpr; assumption | apply hqr; assumption


example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro <;> intro h
  . apply And.intro
    . intro hp
      have hpq : p ∨ q := Or.inl hp
      apply absurd; assumption; assumption
    . intro hq
      have hpq : p ∨ q := Or.inr hq
      apply absurd; assumption; assumption
  . let ⟨hnp, hnq⟩ := h
    intro hpq; apply Or.elim hpq <;> intro h₁
    all_goals apply absurd; assumption; assumption

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro h hpq
  have hp := hpq.1
  have hq := hpq.2
  apply Or.elim h <;> intro h₁
  . exact absurd hp h₁
  . exact absurd hq h₁

example : ¬(p ∧ ¬p) := by
  intro hpnp
  have hp := hpnp.1; have hnp := hpnp.2; exact absurd hp hnp

example : p ∧ ¬q → ¬(p → q) := by
  intro h
  intro hpq
  have hq := hpq h.left
  exact absurd hq h.right

example : ¬p → (p → q) := by
  intro hnp hp
  apply absurd; assumption; assumption

example : (¬p ∨ q) → (p → q) := by
  intro hnpq hp
  cases hnpq with
  | inl hnp => exact absurd hp hnp
  | inr hq => exact hq

example : p ∨ False ↔ p := by
  apply Iff.intro <;> intro h
  . apply Or.elim h <;> intro h₁
    . assumption
    . apply False.elim; assumption
  . exact Or.inl h

example : p ∧ False ↔ False := by
  apply Iff.intro <;> intro h
  . exact False.elim h.right
  . exact False.elim h

example : (p → q) → (¬q → ¬p) := by
  intro h hnq hp
  apply absurd; exact h hp; assumption

