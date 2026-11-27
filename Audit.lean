import Mathlib.Tactic
import Mathlib.Data.Nat.GCD.Basic

/-!
# Strong divisibility for a second-order recurrence

Lehs's question on Mathematics Stack Exchange asks about all positive
coprime coefficients and all positive initial values F(1), with F(0) = 0.
The recurrence starts at F(2), so it never needs a negative index.

Source: https://math.stackexchange.com/questions/2145404
Formalization: @ecirak42.
-/

namespace OMA.S_mse_2145404

theorem main : ∀ a b : ℕ, 0 < a → 0 < b → Nat.Coprime a b →
    ∀ F : ℕ → ℕ, F 0 = 0 → 0 < F 1 →
    (∀ i : ℕ, F (i + 2) = a * F (i + 1) + b * F i) →
    ∀ m n : ℕ, F (Nat.gcd m n) = Nat.gcd (F n) (F m) := by
  sorry

end OMA.S_mse_2145404


/-!
This is the classical strong divisibility theorem for Lucas sequences of
the first kind, with parameters P = a and Q = -b. See Broderius and Greene,
Lucas Sequences Containing Few Primes (2021), equation (1.11).
The Euclidean descent follows the pattern of Mathlib's Nat.fib_gcd.
-/

namespace LucasDivisibility

private def u (a b : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | i + 2 => a * u a b (i + 1) + b * u a b i

private theorem step (a b i : ℕ) :
    u a b (i + 2) = a * u a b (i + 1) + b * u a b i := rfl

private theorem primeToB {a b : ℕ} (hab : Nat.Coprime a b) (i : ℕ) :
    Nat.Coprime (u a b (i + 1)) b := by
  induction i with
  | zero => simp [u]
  | succ i ih =>
    rw [step, Nat.coprime_add_mul_left_left, Nat.coprime_mul_iff_left]
    exact ⟨hab, ih⟩

private theorem adjacent {a b : ℕ} (hab : Nat.Coprime a b) (i : ℕ) :
    Nat.Coprime (u a b i) (u a b (i + 1)) := by
  induction i with
  | zero => simp [u]
  | succ i ih =>
    rw [step, Nat.coprime_mul_right_add_right, Nat.coprime_mul_iff_right]
    exact ⟨primeToB hab i, ih.symm⟩

private theorem addition (a b m n : ℕ) :
    u a b (m + n + 1) =
      b * u a b m * u a b n + u a b (m + 1) * u a b (n + 1) := by
  induction n generalizing m with
  | zero => simp [u]
  | succ n ih =>
    rw [show m + (n + 1) + 1 = (m + 1) + n + 1 by omega, ih, step a b m, step a b n]
    ring

private theorem add_self {a b : ℕ} (hab : Nat.Coprime a b) (m n : ℕ) :
    Nat.gcd (u a b m) (u a b (n + m)) = Nat.gcd (u a b m) (u a b n) := by
  cases m with
  | zero => simp [u]
  | succ m =>
    rw [show n + (m + 1) = n + m + 1 by omega, addition]
    rw [show b * u a b n * u a b m + u a b (n + 1) * u a b (m + 1) =
        u a b n * (b * u a b m) + u a b (n + 1) * u a b (m + 1) by ring,
      Nat.gcd_add_mul_right_right]
    exact Nat.Coprime.gcd_mul_right_cancel_right _ <|
      Nat.coprime_mul_iff_left.mpr ⟨(primeToB hab m).symm, adjacent hab m⟩

private theorem add_multiple {a b : ℕ} (hab : Nat.Coprime a b) (m n : ℕ) : ∀ k,
    Nat.gcd (u a b m) (u a b (n + k * m)) = Nat.gcd (u a b m) (u a b n)
  | 0 => by simp
  | k + 1 => by rw [Nat.add_mul, Nat.one_mul, ← Nat.add_assoc, add_self hab, add_multiple hab m n k]

private theorem gcd {a b : ℕ} (hab : Nat.Coprime a b) (m n : ℕ) :
    u a b (Nat.gcd m n) = Nat.gcd (u a b m) (u a b n) := by
  induction m, n using Nat.gcd.induction with
  | H0 => simp [u]
  | H1 m n _ ih =>
    rw [← Nat.gcd_rec m n] at ih
    conv_rhs => rw [← Nat.mod_add_div' n m]
    rwa [add_multiple hab m (n % m) (n / m), Nat.gcd_comm (u a b m) _]

theorem scaled (a b : ℕ) (hab : Nat.Coprime a b) (F : ℕ → ℕ) (h0 : F 0 = 0)
    (hF : ∀ i, F (i + 2) = a * F (i + 1) + b * F i) (m n : ℕ) :
    F (Nat.gcd m n) = Nat.gcd (F n) (F m) := by
  have scale : ∀ k, F k = F 1 * u a b k
    | 0 => by simp [u, h0]
    | 1 => by simp [u]
    | i + 2 => by rw [hF, scale (i + 1), scale i, step]; ring
  rw [scale (Nat.gcd m n), scale n, scale m, Nat.gcd_mul_left, gcd hab, Nat.gcd_comm (u a b m)]

end LucasDivisibility

theorem OMA.solution : type_of% @OMA.S_mse_2145404.main := by
  intro a b _ _ hab F h0 _ hF m n
  exact LucasDivisibility.scaled a b hab F h0 hF m n

#print axioms OMA.solution
