import OMAStatements.S_oeis_a368773
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic

open PowerSeries OMA.S_oeis_a368773

-- Squaring the defining series gives a quadratic equation for B.
-- Differentiate that equation once and eliminate B².
private theorem quadratic : (1 - 3 * X) * B^2 = (1 - X^2) * (1 + 3 * X) := by
  let q : ℚ⟦X⟧ := -10 * X^2 + 9 * X^4
  have hs : HasSubst q := HasSubst.of_constantCoeff_zero' (by simp [q])
  have hb : binomialSeries ℚ (1/2 : ℚ)^2 = 1 + X := by
    rw [sq, ← binomialSeries_add, show (1/2 : ℚ) + 1/2 = (1:ℕ) by norm_num,
      binomialSeries_nat, pow_one]
  have hr : radical ^ 2 = 1 + q := by
    change (subst q _)^2 = _
    rw [← subst_pow hs, hb, ← coe_substAlgHom hs, map_add, map_one, substAlgHom_X]
  let f : ℚ⟦X⟧ := 1 - 3 * X
  have hc : constantCoeff f ≠ 0 := by simp [f]
  have h : B * f = radical := by
    change radical * f⁻¹ * f = _
    rw [mul_assoc, PowerSeries.inv_mul_cancel _ hc, mul_one]
  apply mul_left_cancel₀ (show f ≠ 0 from fun e => hc (by simp [e]))
  calc
    _ = (B * f)^2 := by dsimp [f]; ring
    _ = _ := by rw [h, hr]; dsimp [q, f]; ring

private theorem equation :
    2 • derivative ℚ B - 20 • (X^2 * derivative ℚ B) + 18 • (X^4 * derivative ℚ B) =
    6 • B - 2 • (X^1 * B) - 6 • (X^2 * B) + 18 • (X^3 * B) := by
  have d := congrArg (derivative ℚ) quadratic
  have c : derivative ℚ 3 = 0 := by
    rw [← map_ofNat C 3, derivative_C]
  simp [Derivation.leibniz, c] at d
  simp only [nsmul_eq_mul, Nat.cast_ofNat, pow_one]
  linear_combination ((1 - 3*X)*B)*d + (3*B - 2*(1 - 3*X)*derivative ℚ B)*quadratic

theorem OMA.solution : type_of% @OMA.S_oeis_a368773.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n-4, by omega⟩
  have h := congrArg (coeff (k+4)) equation
  simp only [map_add, map_sub, map_nsmul] at h
  simp +arith (disch := omega) [coeff_X_pow_mul', coeff_derivative, nsmul_eq_mul] at h
  cases k <;> simp +arith [a, coeff_one, coeff_X] at h ⊢ <;> linarith
