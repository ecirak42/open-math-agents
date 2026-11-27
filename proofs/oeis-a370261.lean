import OMAStatements.S_oeis_a370261

/-!
# Integrality of Peter Bala's OEIS A370261

For x = 2n+1 the Chebyshev identity below makes the radicand the square
of U(n-1,x)/n. This quotient is integral since U(n-1,x) is congruent
to U(n-1,1) = n modulo n.
-/

namespace OMA

open Polynomial Polynomial.Chebyshev S_oeis_a370261

private theorem doubleAngle (k x : ℤ) :
    (T ℤ (2*k)).eval x - 1 = 2 * (x^2-1) * ((U ℤ (k-1)).eval x)^2 := by
  have shift (j : ℤ) : (S ℤ j).eval (2*x) = (U ℤ j).eval x := by
    rw [← S_comp_two_mul_X, eval_comp]
    simp
  have norm := congrArg (fun p : ℤ[X] => p.eval (2*x)) (S_sq_add_S_sq ℤ (k-1))
  simp only [eval_sub, eval_add, eval_pow, eval_mul, eval_X, eval_one,
    sub_add_cancel, shift] at norm
  have lin := congrArg (fun p : ℤ[X] => p.eval x) (T_eq_U_sub_X_mul_U ℤ k)
  simp only [eval_sub, eval_mul, eval_X] at lin
  have dbl := congrArg (fun p : ℤ[X] => p.eval x) (T_mul_T ℤ k k)
  simp only [eval_mul, eval_ofNat, eval_add, sub_self, T_zero, eval_one,
    ← two_mul] at dbl
  rw [lin] at dbl
  linear_combination 2 * norm - dbl

theorem solution : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, a n = k := by
  intro n hn
  let P := U ℤ ((n : ℤ)-1)
  have h := Polynomial.sub_dvd_eval_sub (2*(n : ℤ)+1) 1 P
  have h1 : P.eval 1 = (n : ℤ) := by simp [P, U_eval_one]
  rw [h1] at h
  obtain ⟨w, hw⟩ := h
  let q := 2*w+1
  have hq : P.eval (2*(n : ℤ)+1) = (n : ℤ)*q := by
    dsimp [q]
    linear_combination hw
  have hT := doubleAngle (n : ℤ) (2*(n : ℤ)+1)
  change _ = 2 * _ * (P.eval _)^2 at hT
  rw [hq] at hT
  have hreal : (((T ℤ (2*(n : ℤ))).eval (2*(n : ℤ)+1) : ℤ) : ℝ) - 1 =
      2 * ((2*(n : ℝ)+1)^2 - 1) * ((n : ℝ)*(q : ℝ))^2 := by
    exact_mod_cast hT
  refine ⟨q.natAbs, ?_⟩
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1 : (n : ℝ)+1 ≠ 0 := by positivity
  unfold a A370259
  push_cast
  have rad : ((((T ℤ (2*(n : ℤ))).eval (2*(n : ℤ)+1) : ℤ) : ℝ) - 1) /
      (2*(n : ℝ))^3 / ((n : ℝ)+1) = (q : ℝ)^2 := by
    rw [hreal]
    field_simp
    ring
  rw [rad, Real.sqrt_sq_eq_abs]
  exact_mod_cast (Int.natCast_natAbs q).symm

end OMA
