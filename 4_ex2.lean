variable (α : Type) (p q : α → Prop)
variable (r : Prop)
theorem deMorgans1 {p q : Prop} (h : ¬(p ∨ q)) : ¬p ∧ ¬q :=
  And.intro
    (fun hp : p => absurd (Or.inl hp) h)
    (fun hq : q => absurd (Or.inr hq) h)

example : α → ((∀ _ : α, r) ↔ r) :=
  λ a : α =>
  Iff.intro
    (λ h : ∀ _ : α, r =>
      h a)
    (λ h : r =>
      λ _ : α =>
      h)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (λ h : ∀ x, p x ∨ r =>
      Classical.byContradiction
        λ h₁ : ¬ ((∀ x, p x) ∨ r) =>
        have h₁' : ¬ (∀ x, p x) ∧ ¬ r := deMorgans1 h₁
        have hnAxpx : ¬ ∀ x, p x := h₁'.left
        have hnr : ¬ r := h₁'.right
        suffices h₂ : ∀ x, p x from absurd h₂ hnAxpx
        λ x =>
        have hpxr : p x ∨ r := h x
        Or.elim hpxr
          (λ hpx : p x => hpx)
          (λ hr : r => absurd hr hnr))
    (λ h : (∀ x, p x) ∨ r =>
      λ x =>
      Or.elim h
        (λ hAxpx : ∀ x, p x => Or.inl (hAxpx x))
        (λ hr : r => Or.inr hr))

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (λ h : ∀ x, r → p x =>
      λ hr : r =>
      λ x =>
      (h x) hr)
    (λ h : r → ∀ x, p x =>
      λ x =>
      λ hr : r =>
      (h hr) x)

