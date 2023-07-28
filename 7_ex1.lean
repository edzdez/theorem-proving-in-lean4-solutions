namespace Hidden


-- multiplication

def mul (m n : Nat) : Nat :=
  match n with
  | 0 => 0
  | (n + 1) => m * n + m

theorem mul_zero (m : Nat) : m * 0 = 0 := by rfl
theorem mul_succ (m n: Nat) : m * Nat.succ n = m * n + m := by rfl
theorem mul_one (m : Nat) : m * 1 = m := by rw [mul_succ, mul_zero, Nat.zero_add]

theorem zero_mul (n : Nat) : 0 * n = 0 := by
  induction n
  case zero => rfl
  case succ ih => rw [mul_succ, Nat.add_zero, ih]

theorem succ_mul (m n: Nat) : Nat.succ m * n = m * n + n := by
  induction n
  case zero => rfl
  case succ ih => rw [mul_succ, Nat.add_succ, ih, mul_succ, Nat.add_succ, Nat.add_right_comm]

theorem one_mul (m : Nat) : 1 * m = m := by
  induction m
  case zero => rfl
  case succ ih => rw [mul_succ, ih]

theorem distrib_left (m n o : Nat) : m * (n + o) = m * n + m * o := by
  induction o
  case zero => rfl
  case succ o ih => rw [Nat.add_succ, mul_succ, mul_succ, ih, Nat.add_assoc]

theorem mul_assoc (m n o : Nat) : (m * n) * o = m * (n * o) := by
  induction o
  case zero => repeat rw [mul_zero]
  case succ o ih => rw [mul_succ, mul_succ, distrib_left, ih]

theorem mul_comm (m n : Nat) : m * n = n * m := by
  induction n
  case zero => rw [mul_zero, zero_mul]
  case succ n ih => rw [mul_succ, succ_mul, ←ih]

-- pred

def pred (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | m + 1 => m

#eval pred 1
#eval pred 0
#eval pred 100

-- truncated subtraction

def sub (m n : Nat) : Nat :=
  match n with
  | 0 => m
  | o + 1 => sub (pred m) o

#eval sub 5 2
#eval sub 2 3
#eval sub 10 10

-- exponentiation

def exp (m n : Nat) : Nat :=
  match n with
  | 0 => 1
  | o + 1 => exp m o * m

#eval exp 1 2
#eval exp 5 0
#eval exp 10 2
#eval exp 2 8
#eval exp 0 100

end Hidden
