import OMAStatements.S_oeis_a246048
import Mathlib.Tactic

namespace A246048Proof

private theorem scale {p : ℕ} (hp : p.Prime) (k m : ℕ) :
    ((p ^ k * m).factorial).factorization p =
      m.factorial.factorization p + m * (p ^ k).factorial.factorization p := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Nat.mul_assoc, Nat.factorization_factorial_mul hp, ih,
      Nat.factorization_factorial_mul hp]
    ring

theorem exclusion {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ¬ OMA.S_oeis_a246048.isTerm (p ^ (k + 1)) := by
  let n := p ^ (k + 1)
  have hpos : 0 < n.factorial.factorization p := by
    dsimp [n]
    rw [pow_succ', Nat.factorization_factorial_mul hp]
    have : 0 < p ^ k := pow_pos hp.pos _
    omega
  have htop : (n ^ 2).factorial.factorization p =
      n.factorial.factorization p + n * n.factorial.factorization p := by
    simpa only [pow_two] using scale hp (k + 1) n
  have htwo : (2 * n).factorial.factorization p =
      (2 : ℕ).factorial.factorization p + 2 * n.factorial.factorization p := by
    rw [mul_comm 2 n]
    exact scale hp (k + 1) 2
  intro hd
  change n.factorial ^ n * (2 * n).factorial ∣ (n ^ 2).factorial at hd
  have hv := (Nat.factorization_le_iff_dvd
    (mul_ne_zero (pow_ne_zero n n.factorial_ne_zero) (2 * n).factorial_ne_zero)
    (n ^ 2).factorial_ne_zero).2 hd p
  rw [Nat.factorization_mul (pow_ne_zero n n.factorial_ne_zero) (2 * n).factorial_ne_zero,
    Nat.factorization_pow] at hv
  change n * n.factorial.factorization p + (2 * n).factorial.factorization p ≤
    (n ^ 2).factorial.factorization p at hv
  rw [htop, htwo] at hv
  omega

end A246048Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a246048.main :=
  fun _ k hp => A246048Proof.exclusion hp k
