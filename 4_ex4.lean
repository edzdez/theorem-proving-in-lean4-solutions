def divides (a b: Nat) : Prop := ∃ k : Nat, b = a * k
infix:50 " ∣ " => divides

def even (n : Nat) : Prop := ∃ k : Nat, n = 2 * k
def odd (n : Nat) : Prop := ¬ even n

def prime (n : Nat) : Prop := n > 1 ∧ ∀ k : Nat, k ≠ 1 ∧ k ≠ n → ¬ k ∣ n

def infinitely_many_primes : Prop := ∀ p1 : Nat, prime p1 → ∃ p2 : Nat, p2 > p1 ∧ prime p2

def Fermat_prime (n : Nat) : Prop := prime n ∧ ∃ k : Nat, n = 2^(2^k) + 1

def infinitely_many_Fermat_primes : Prop := ∀ n : Nat, Fermat_prime n → ∃ m : Nat, m > n ∧ Fermat_prime m

def goldbach_conjecture : Prop := ∀ n : Nat, n > 2 ∧ even n → ∃ i j : Nat, prime i ∧ prime j ∧ i + j = n

def Goldbach's_weak_conjecture : Prop := ∀ n : Nat, n > 5 ∧ odd n → ∃ i j k : Nat, prime i ∧ prime j ∧ prime k ∧ i + j + k = n

def Fermat's_last_theorem : Prop := ∀ n : Nat, n > 2 → ¬ ∃ a b c : Nat, a > 0 ∧ b > 0 ∧ c > 0 ∧ a^n + b^n = c^n
