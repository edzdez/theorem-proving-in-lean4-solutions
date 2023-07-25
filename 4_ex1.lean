variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (λ h : ∀ x, p x ∧ q x => And.intro
      (λ x : α =>
        have hpxqx : p x ∧ q x := h x
        hpxqx.left)
      (λ x : α =>
        have hpxqx : p x ∧ q x := h x
        hpxqx.right))
    (λ h : (∀ x, p x) ∧ (∀ x, q x) =>
      λ x : α =>
      And.intro (h.left x) (h.right x))

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  λ h : ∀ x, p x → q x =>
  λ h₁ : ∀ x, p x =>
  λ x : α =>
  (h x) (h₁ x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  λ h : (∀ x, p x) ∨ (∀ x, q x) =>
  λ x : α =>
  Or.elim h
    (λ hAxpx : ∀ x, p x => Or.inl (hAxpx x))
    (λ hAxqx : ∀ x, q x => Or.inr (hAxqx x))

/-
The reverse implication is not derivable, as $∀ x, p x ∨ q x$ only
implies that at least one of $p x$ or $q x$ is true for all x, not
that it's necessarily that one of $p x$ or $q x$ is true for all x.

Counterexample:
  ∀ x ∈ ℕ, (isEven x) ∨ (isOdd x) ≢ (∀ x ∈ ℕ, isEven x) ∨ (∀ x ∈ ℕ, isOdd x)
-/
