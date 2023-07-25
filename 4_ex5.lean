open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)
theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p) (fun hp : p => hp) (fun hnp : ¬p => absurd hnp h)

example : (∃ _ : α, r) → r :=
  λ h : ∃ _ : α, r =>
  Exists.elim h
    λ _ : α =>
    λ w : r =>
    w

example (a : α) : r → (∃ _ : α, r) :=
  λ h : r =>
  Exists.intro a h

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (λ h : ∃ x, p x ∧ r =>
      let ⟨w, hpw, hr⟩ := h
      And.intro ⟨w, hpw⟩ hr)
    (λ h : (∃ x, p x) ∧ r =>
      let ⟨w, hpw⟩ := h.left
      have hr : r := h.right
      Exists.intro w (And.intro hpw hr))

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (λ h : ∃ x, p x ∨ q x =>
      let ⟨w, hw⟩ := h
      Or.elim hw
        (λ hpw : p w => Or.inl ⟨w, hpw⟩)
        (λ hqw : q w => Or.inr ⟨w, hqw⟩))
    (λ h : (∃ x, p x) ∨ (∃ x, q x) =>
      Or.elim h
      (λ h₁ : ∃ x, p x =>
        let ⟨w, hpw⟩ := h₁
        have hpq : p w ∨ q w := Or.inl hpw
        ⟨w, hpq⟩)
      (λ h₁ : ∃ x, q x =>
        let ⟨w, hqw⟩ := h₁
        have hpq : p w ∨ q w := Or.inr hqw
        ⟨w, hpq⟩))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
    (λ h : ∀ x, p x =>
      λ h1 : (∃ x, ¬ p x) =>
        let ⟨a, hpa⟩ := h1
        absurd (h a) hpa)
    (λ h : ¬ (∃ x, ¬ p x) =>
      λ x : α =>
      byContradiction
        λ hnpx : ¬ p x =>
        have h2 : ∃ x, ¬ p x := ⟨x, hnpx⟩
        absurd h2 h)

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
    (λ h : ∃ x, p x =>
      let ⟨x, hpx⟩ := h
      λ h1 : ∀ x, ¬ p x =>
        absurd hpx (h1 x))
    (λ h : ¬ (∀ x, ¬ p x) =>
      byContradiction
        λ h1 : ¬ ∃ x, p x =>
        suffices h2 : ∀ x, ¬ p x from absurd h2 h
        λ x : α =>
        λ hpx : p x =>
        absurd ⟨x, hpx⟩ h1)

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
    (λ h : (¬ ∃ x, p x) =>
      λ x : α =>
      λ hpx : p x =>
      absurd ⟨x, hpx⟩ h)
    (λ h : (∀ x, ¬ p x) =>
      λ h1 : ∃ x, p x =>
      let ⟨x, hpx⟩ := h1
      absurd hpx (h x))

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
    (λ h : (¬ ∀ x, p x) =>
      byContradiction
        λ h1 : ¬ ∃ x, ¬ p x =>
        suffices h2 : ∀ x, p x from absurd h2 h
        λ x : α =>
        byContradiction
          λ hnpx : ¬ p x =>
          absurd ⟨x, hnpx⟩ h1)
    (λ h : (∃ x, ¬ p x) =>
      let ⟨x, hpnx⟩ := h
      λ h1 : ∀ x, p x =>
      absurd (h1 x) hpnx)

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
    (λ h : ∀ x, p x → r =>
      λ h1 : ∃ x, p x =>
      let ⟨x, hpx⟩ := h1
      show r from (h x) hpx)
    (λ h : (∃ x, p x) → r =>
      λ x : α =>
      λ hpx : p x =>
        have hExpx : ∃ x, p x := ⟨x, hpx⟩
        show r from h hExpx)

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (λ h : ∃ x, p x → r =>
      let ⟨x, hpxr⟩ := h
      λ h1 : ∀ x, p x =>
      hpxr (h1 x))
    (λ h : (∀ x, p x) → r =>
      byCases
        (λ hApx : ∀ x, p x =>
          have hr : r := h hApx
          ⟨a, λ _ : p a => hr⟩)
        (λ hnAxpx : ¬ ∀ x, p x =>
          byContradiction
            λ hnExpxr : ¬ ∃ x, p x → r =>
            suffices hAxpx : ∀ x, p x from absurd hAxpx hnAxpx
            λ x : α =>
            byContradiction
              λ hnpx : ¬ p x =>
              have hpxr : p x → r := λ hpx : p x => absurd hpx hnpx
              have hExpxr : ∃ x, p x → r := ⟨x, hpxr⟩
              absurd hExpxr hnExpxr))

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
    (λ h : ∃ x, r → p x =>
      let ⟨x, hrpx⟩ := h
      λ hr : r =>
      ⟨x, hrpx hr⟩)
    (λ h : r → ∃ x, p x =>
      byCases
        (λ hr : r =>
          have hExpx : ∃ x, p x := h hr
          let ⟨x, hpx⟩ := hExpx
          have hrpx := λ _ : r => hpx
          ⟨x, hrpx⟩)
        (λ hnr : ¬ r =>
          byContradiction
            λ hnEarpa : ¬ ∃ a, r → p a =>
            have hrpa : r → p a := λ hr : r => absurd hr hnr
            have hEarpa : ∃ a, r → p a := ⟨a, hrpa⟩
            absurd hEarpa hnEarpa))
