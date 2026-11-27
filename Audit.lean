import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Mathar's recurrence for A368773

Source: https://oeis.org/A368773
The recurrence starts at index 4, so all indices are nonnegative.
-/

namespace OMA.S_oeis_a368773

open PowerSeries

noncomputable def radical : PowerSeries ℚ :=
  PowerSeries.subst (-10 * X ^ 2 + 9 * X ^ 4 : PowerSeries ℚ) (binomialSeries ℚ (1 / 2 : ℚ))

noncomputable def B : PowerSeries ℚ := radical * (1 - 3 * X)⁻¹

/-- Coefficients of the even part of the published packing-path series. -/
noncomputable def a (n : ℕ) : ℚ := coeff (n + 1) (B - 1 + X) / 4

theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℚ) + 1) * a n - 3 * a (n - 1) + (-(10 : ℚ) * n + 11) * a (n - 2) +
      3 * a (n - 3) + 9 * ((n : ℚ) - 4) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a368773


namespace PackingPaths
open PowerSeries OMA.S_oeis_a368773

private theorem radical_sq : radical ^ 2 =
    1 - 10 * X ^ 2 + 9 * X ^ 4 := by
  let q : PowerSeries ℚ := -10 * X ^ 2 + 9 * X ^ 4
  have hq : HasSubst q := HasSubst.of_constantCoeff_zero' (by simp [q])
  have hbin : binomialSeries ℚ (1 / 2 : ℚ) ^ 2 = 1 + X := by
    rw [pow_two, ← binomialSeries_add, show (1 / 2 : ℚ) + 1 / 2 = (1 : ℕ) by norm_num,
      binomialSeries_nat, pow_one]
  change (subst q _) ^ 2 = _
  rw [← subst_pow hq, hbin, ← coe_substAlgHom hq, map_add, map_one, substAlgHom_X]
  dsimp [q]
  ring

private theorem quad : (1 - 3 * X) * B ^ 2 = (1 - X ^ 2) * (1 + 3 * X) := by
  let f : PowerSeries ℚ := 1 - 3 * X
  have hconst : constantCoeff f ≠ 0 := by simp [f]
  have hf : f ≠ 0 := fun h => hconst (by rw [h, map_zero])
  have hB : B * f = radical := by
    change (radical * f⁻¹) * f = _
    rw [mul_assoc, PowerSeries.inv_mul_cancel f hconst, mul_one]
  apply mul_left_cancel₀ hf
  calc
    f * ((1 - 3 * X) * B ^ 2) = (B * f) ^ 2 := by dsimp [f]; ring
    _ = _ := by rw [hB, radical_sq]; dsimp [f]; ring

private theorem ode :
    derivative ℚ B - 10 • (X ^ 2 * derivative ℚ B) + 9 • (X ^ 4 * derivative ℚ B) =
      3 • B - X ^ 1 * B - 3 • (X ^ 2 * B) + 9 • (X ^ 3 * B) := by
  let d := derivative ℚ
  have h3 : d 3 = 0 := by
    change derivative ℚ (3 : PowerSeries ℚ) = 0
    rw [show (3 : PowerSeries ℚ) = PowerSeries.C (3 : ℚ) by simp, derivative_C]
  have hd := congrArg d quad
  change d ((1 - 3 * X) * B^2) = d ((1 - X^2) * (1 + 3 * X)) at hd
  dsimp [d] at hd h3
  simp only [Derivation.leibniz, map_sub, map_add, derivative_one, derivative_X, h3,
    derivative_pow, smul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one, zero_mul,
    mul_zero, mul_one, one_mul, add_zero, zero_add] at hd
  simp only [nsmul_eq_mul, Nat.cast_ofNat, pow_one]
  apply mul_left_cancel₀ (by norm_num : (2 : PowerSeries ℚ) ≠ 0)
  linear_combination ((1 - 3 * X) * B) * hd +
    (-(2 : PowerSeries ℚ) * (1 - 3 * X) * derivative ℚ B + 3 * B) * quad

private theorem coeff_ode (k : ℕ) :
    (((k : ℚ) + 4) + 1) * coeff (k + 5) B - 3 * coeff (k + 4) B
      + (-10 * ((k : ℚ) + 4) + 11) * coeff (k + 3) B + 3 * coeff (k + 2) B
      + 9 * (k : ℚ) * coeff (k + 1) B = 0 := by
  have h := congrArg (coeff (k + 4)) ode
  simp only [map_sub, map_add, map_nsmul, coeff_X_pow_mul', coeff_derivative,
    nsmul_eq_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one,
    show 1 ≤ k + 4 by omega, show 2 ≤ k + 4 by omega,
    show 3 ≤ k + 4 by omega, show 4 ≤ k + 4 by omega, ↓reduceIte,
    show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega] at h
  linear_combination h

theorem recurrence (n : ℕ) (hn : 4 ≤ n) :
    ((n : ℚ) + 1) * a n - 3 * a (n - 1) + (-(10 : ℚ) * n + 11) * a (n - 2)
      + 3 * a (n - 3) + 9 * ((n : ℚ) - 4) * a (n - 4) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have h := coeff_ode k
  rw [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega]
  cases k <;> simp [a, map_add, map_sub, coeff_one, coeff_X] at h ⊢ <;> linarith

end PackingPaths

theorem OMA.solution : type_of% @OMA.S_oeis_a368773.main := PackingPaths.recurrence

#print axioms OMA.solution
