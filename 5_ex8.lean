example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  constructor
  . constructor; exact hp
  . constructor
    . apply Or.inr; constructor; exact hp
    . apply Or.inr; apply Or.inr; exact hp

-- I know that this works
example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  constructor <;> constructor; exact hp; apply Or.inr; constructor; exact hp; apply Or.inr; apply Or.inr; exact hp

-- And this
example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  constructor; constructor; assumption; constructor; apply Or.inr; constructor; assumption; apply Or.inr; apply Or.inr; assumption

-- But I'm not sure about this
example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  repeat first | exact Or.inl hp | exact Or.inr hp | apply And.intro | apply Or.inr

-- Or this
example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  constructor <;> constructor <;> repeat first | exact hp | exact Or.inl hp | apply Or.inr

