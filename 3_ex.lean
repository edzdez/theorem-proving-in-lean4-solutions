variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (λ h : p ∧ q =>
      have hp : p := And.left h
      have hq : q := And.right h
      show q ∧ p from And.intro hq hp)
    (λ h : q ∧ p =>
      have hq : q := And.left h
      have hp : p := And.right h
      show p ∧ q from And.intro hp hq)

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (λ h : p ∨ q =>
      Or.elim h
        (λ hp : p =>
          show q ∨ p from Or.inr hp)
        (λ hq : q =>
          show q ∨ p from Or.inl hq))
    (λ h : q ∨ p =>
      Or.elim h
        (λ hq : q =>
          show p ∨ q from Or.inr hq)
        (λ hp : p =>
          show p ∨ q from Or.inl hp))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (λ h : (p ∧ q) ∧ r =>
      have hs : (p ∧ q) := And.left h
      have hp : p := show p from And.left hs
      have hq : q := show q from And.right hs
      have hr : r := show r from And.right h
      show p ∧ (q ∧ r) from And.intro hp (And.intro hq hr))
    (λ h : p ∧ (q ∧ r) =>
      have hs : (q ∧ r) := And.right h
      have hp : p := And.left h
      have hq : q := And.left hs
      have hr : r := And.right hs
      show (p ∧ q) ∧ r from And.intro (And.intro hp hq) hr)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (λ h : (p ∨ q) ∨ r =>
      Or.elim h
        (λ hs : (p ∨ q) =>
          Or.elim hs
            (λ hp : p =>
              show p ∨ (q ∨ r) from Or.inl hp)
            (λ hq : q =>
              have ht : (q ∨ r) := Or.inl hq
              show p ∨ (q ∨ r) from Or.inr ht))
        (λ hr : r =>
          have ht : (q ∨ r) := Or.inr hr
          show p ∨ (q ∨ r) from Or.inr ht))
    (λ h : p ∨ (q ∨ r) =>
      Or.elim h
        (λ hp : p =>
          have hs : (p ∨ q) := Or.inl hp
          show (p ∨ q) ∨ r from Or.inl hs)
        (λ ht : (q ∨ r) =>
          Or.elim ht
            (λ hq : q =>
              have hs : (p ∨ q) := Or.inr hq
              show (p ∨ q) ∨ r from Or.inl hs)
            (λ hr : r =>
              show (p ∨ q) ∨ r from Or.inr hr)))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (λ h : p ∧ (q ∨ r) =>
      have hp : p := And.left h
      have hs : (q ∨ r) := And.right h
      Or.elim hs
        (λ hq : q =>
          suffices ht : (p ∧ q) from Or.inl ht
          show p ∧ q from And.intro hp hq)
        (λ hr : r =>
          suffices ht : (p ∧ r) from Or.inr ht
          show p ∧ r from And.intro hp hr))
    (λ h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (λ hs : (p ∧ q) =>
          have hp : p := And.left hs
          have hq : q := And.right hs
          suffices ht : (q ∨ r) from And.intro hp ht
          show q ∨ r from Or.inl hq)
        (λ hs : (p ∧ r) =>
          have hp : p := And.left hs
          have hr : r := And.right hs
          suffices ht : (q ∨ r) from And.intro hp ht
          show q ∨ r from Or.inr hr))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (λ h : p ∨ (q ∧ r) =>
      Or.elim h
        (λ hp : p =>
          have hs : p ∨ q := Or.inl hp
          have ht : p ∨ r := Or.inl hp
          show (p ∨ q) ∧ (p ∨ r) from And.intro hs ht)
        (λ hs : q ∧ r =>
          have hq : q := And.left hs
          have hr : r := And.right hs
          have ht : p ∨ q := Or.inr hq
          have hu : p ∨ r := Or.inr hr
          show (p ∨ q) ∧ (p ∨ r) from And.intro ht hu))
    (λ h : (p ∨ q) ∧ (p ∨ r) =>
      have hs : (p ∨ q) := And.left h
      have ht : (p ∨ r) := And.right h
      Or.elim hs
        (λ hp : p =>
          show p ∨ (q ∧ r) from Or.inl hp)
        (λ hq : q =>
          Or.elim ht
            (λ hp : p =>
              show p ∨ (q ∧ r) from Or.inl hp)
            (λ hr : r =>
              have hu : q ∧ r := And.intro hq hr
              show p ∨ (q ∧ r) from Or.inr hu)))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (λ h : p → (q → r) =>
      (λ hpq : p ∧ q =>
        have hp : p := And.left hpq
        have hq : q := And.right hpq
        show r from h hp hq))
    (λ h : p ∧ q → r =>
      (λ hp : p =>
        λ hq : q =>
          show r from h (And.intro hp hq)))

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (λ h : ((p ∨ q) → r) =>
      And.intro
        (fun hp : p =>
          h (Or.inl hp))
        (fun hq : q =>
          h (Or.inr hq)))
    (λ h : (p → r) ∧ (q → r) =>
      have hpr : p -> r := And.left h
      have hqr : q -> r := And.right h
      (λ hpq : p ∨ q =>
        Or.elim hpq
          (fun hp : p => hpr hp)
          (fun hq : q => hqr hq)))

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (λ h : ¬(p ∨ q) =>
      And.intro
        (fun hp : p => absurd (Or.inl hp) h)
        (fun hq : q => absurd (Or.inr hq) h))
    (λ h : ¬p ∧ ¬q =>
      (λ hpq : p ∨ q =>
        Or.elim hpq
          (λ hp : p => absurd hp (And.left h))
          (λ hq : q => absurd hq (And.right h))))

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
    (λ h : ¬p ∨ ¬q =>
      (λ hpq : p ∧ q =>
        have hp : p := And.left hpq
        have hq : q := And.right hpq
        Or.elim h
          (λ hnp : ¬p => absurd hp hnp)
          (λ hnq : ¬q => absurd hq hnq)))

example : ¬(p ∧ ¬p) :=
  (λ h : p ∧ ¬p =>
    absurd (And.left h) (And.right h))

example : p ∧ ¬q → ¬(p → q) :=
  (λ h : p ∧ ¬q =>
    have hp : p := And.left h
    have hnq : ¬q := And.right h
    (λ hpq : p → q =>
      have hq : q := hpq hp
      absurd hq hnq))

example : ¬p → (p → q) :=
  (λ h : ¬p =>
    (λ hp : p =>
      absurd hp h))

example : (¬p ∨ q) → (p → q) :=
  (λ h : ¬p ∨ q =>
    (λ hp : p =>
      Or.elim h
        (λ hnp : ¬p => absurd hp hnp)
        (λ hq : q => hq)))

example : p ∨ False ↔ p :=
  Iff.intro
    (λ h : p ∨ False =>
      Or.elim h
        (λ hp : p => hp)
        (λ hf : False => False.elim hf))
    (λ h : p => Or.inl h)

example : p ∧ False ↔ False :=
  Iff.intro
    (λ h : p ∧ False => False.elim (And.right h))
    (λ h : False => False.elim h)

example : (p → q) → (¬q → ¬p) :=
  (λ h : p → q =>
    (λ hnq : ¬q =>
      (λ hp : p =>
        have hq : q := h hp
        absurd hq hnq)))

