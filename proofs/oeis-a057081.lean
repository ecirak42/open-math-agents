import Mathlib

/-!
# A057081 and Peter Bala's alternating series

The sequence consists of the even-indexed Chebyshev polynomials of the second
kind evaluated at sqrt(11)/2. Its first terms, starting at index 0, are 1,
10, 89 and 791. Peter Bala stated the general alternating-series conjecture
on 8 June 2025. The summation index in the source starts at 1, so the term
indexed by j in the finite sum below is the source term with n = j + 1.

Source: https://oeis.org/A057081
Credit: @ecirak42
-/

namespace OMA.S_oeis_a057081

noncomputable def a (n : ℕ) : ℝ :=
  (Polynomial.Chebyshev.U ℝ (2 * (n : ℤ))).eval (Real.sqrt 11 / 2)

noncomputable def s (k : ℕ) : ℝ := ∑ j ∈ Finset.range k, a j

noncomputable def term (k n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) / (a (k * n) - s k / a (k * n))

/-- The partial sums of Bala's series converge to the stated value for every positive k. -/
theorem main : ∀ k : ℕ, 1 ≤ k →
    Filter.Tendsto (fun N => ∑ j ∈ Finset.range N, term k (j + 1))
      Filter.atTop (nhds (1 / (1 + a k))) := by
  sorry

end OMA.S_oeis_a057081


/-! Bala's series telescopes between successive reciprocals of sums of adjacent subsequence terms. -/

namespace A057081Proof

open OMA.S_oeis_a057081 Filter Real

noncomputable def t : ℝ := arcosh (sqrt 11 / 2)

private theorem arg_gt : 1 < sqrt 11 / 2 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num), Real.sqrt_nonneg (11 : ℝ)]

private theorem tpos : 0 < t := Real.arcosh_pos arg_gt

private theorem shpos : 0 < sinh t := Real.sinh_pos_iff.mpr tpos

private theorem aval (n : ℕ) : a n = sinh ((2 * (n : ℝ) + 1) * t) / sinh t := by
  apply (eq_div_iff shpos.ne').mpr
  unfold a
  rw [← show cosh t = sqrt 11 / 2 from Real.cosh_arcosh arg_gt.le]
  simpa using Polynomial.Chebyshev.U_real_cosh t (2 * (n : ℤ))

private theorem product_sinh (x y : ℝ) :
    sinh (x + y) * sinh (x - y) = sinh x ^ 2 - sinh y ^ 2 := by
  rw [Real.sinh_add, Real.sinh_sub]
  calc
    _ = sinh x ^ 2 * cosh y ^ 2 - cosh x ^ 2 * sinh y ^ 2 := by ring
    _ = _ := by rw [Real.cosh_sq, Real.cosh_sq]; ring

private theorem sval (n : ℕ) : s n = sinh ((n : ℝ) * t) ^ 2 / sinh t ^ 2 := by
  induction n with
  | zero => simp [s]
  | succ n ih =>
    rw [s, Finset.sum_range_succ, ← s, ih, aval]
    push_cast
    have h := product_sinh (((n : ℝ) + 1) * t) ((n : ℝ) * t)
    rw [show ((n : ℝ) + 1) * t + n * t = (2 * n + 1) * t by ring,
        show ((n : ℝ) + 1) * t - n * t = t by ring] at h
    field_simp [shpos.ne']
    linarith

private theorem rational_identity (x y L R c d : ℝ) (hx : 0 < x) (hd : 0 < d)
    (hL : 0 < L) (hR : 0 < R) (hc : 0 < c)
    (hprod : x ^ 2 - y ^ 2 = L * R) (hsum : L + R = 2 * x * c) :
    1 / (x / d - y ^ 2 / d ^ 2 / (x / d)) =
      d / (2 * c) / L + d / (2 * c) / R := by
  have hn : x ^ 2 - y ^ 2 ≠ 0 := by rw [hprod]; positivity
  calc
    _ = d * x / (x ^ 2 - y ^ 2) := by
      have h : x / d - y ^ 2 / d ^ 2 / (x / d) = (x ^ 2 - y ^ 2) / (d*x) := by
        field_simp [hx.ne', hd.ne']; ring
      rw [h]; field_simp; ring
    _ = _ := by
      rw [hprod]
      field_simp [hc.ne', hL.ne', hR.ne']
      linear_combination -d * hsum

noncomputable def b (k n : ℕ) : ℝ :=
  sinh t / (2 * cosh ((k : ℝ) * t)) /
    sinh ((2 * (k : ℝ) * n + k + 1) * t)

private theorem bfirst (k : ℕ) : b k 0 = 1 / (1 + a k) := by
  have ht := tpos
  rw [b, aval]
  push_cast
  simp only [mul_zero, zero_add]
  have hu : 0 < sinh (((k : ℝ) + 1) * t) := Real.sinh_pos_iff.mpr (by positivity)
  have h : sinh t + sinh ((2 * (k : ℝ) + 1) * t) =
      2 * cosh ((k : ℝ) * t) * sinh (((k : ℝ) + 1) * t) := by
    conv_lhs => lhs; rw [show t = ((k : ℝ) + 1) * t - k * t by ring, Real.sinh_sub]
    conv_lhs => rhs; rw [show (2 * (k : ℝ) + 1) * t = (k + 1) * t + k * t by ring, Real.sinh_add]
    ring
  have hv : 0 < sinh ((2 * (k : ℝ) + 1) * t) := Real.sinh_pos_iff.mpr (by positivity)
  field_simp [shpos.ne', hu.ne', (Real.cosh_pos _).ne', (add_pos shpos hv).ne']
  linear_combination (sinh t) * h

private theorem decompose (k n : ℕ) :
    1 / (a (k * (n+1)) - s k / a (k * (n+1))) = b k n + b k (n+1) := by
  have ht := tpos
  let u := (2 * ((k : ℝ) * (n+1)) + 1) * t
  let v := (k : ℝ) * t
  have minus : u-v = (2*(k:ℝ)*n+k+1)*t := by dsimp [u,v]; ring
  have plus : u+v = (2*(k:ℝ)*(n+1)+k+1)*t := by dsimp [u,v]; ring
  have hu : 0 < sinh u := Real.sinh_pos_iff.mpr (by dsimp [u]; positivity)
  have hL : 0 < sinh (u-v) := Real.sinh_pos_iff.mpr (by rw [minus]; positivity)
  have hR : 0 < sinh (u+v) := Real.sinh_pos_iff.mpr (by rw [plus]; positivity)
  have hprod : sinh u ^ 2 - sinh v ^ 2 = sinh (u-v) * sinh (u+v) := by
    rw [mul_comm (sinh (u-v)), product_sinh]
  have hsum : sinh (u-v) + sinh (u+v) = 2 * sinh u * cosh v := by
    rw [Real.sinh_sub, Real.sinh_add]; ring
  have h := rational_identity (sinh u) (sinh v) (sinh (u-v)) (sinh (u+v))
    (cosh v) (sinh t) hu shpos hL hR (Real.cosh_pos _) hprod hsum
  rw [minus, plus] at h
  simpa only [aval, sval, b, Nat.cast_mul, Nat.cast_add_one, u, v] using h

private theorem partial_sum (k N : ℕ) :
    (∑ j ∈ Finset.range N, term k (j+1)) = b k 0 - (-1 : ℝ)^N * b k N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, term, div_eq_mul_one_div, decompose]
    simp only [pow_succ]
    ring

private theorem bzero (k : ℕ) (hk : 1 ≤ k) : Tendsto (b k) atTop (nhds 0) := by
  have ht := tpos
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hg : Tendsto (fun n : ℕ => sinh ((2 * (k:ℝ) * n + k + 1)*t)) atTop atTop := by
    apply tendsto_atTop.2
    intro M
    obtain ⟨N, hN⟩ := exists_nat_gt (M/t)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hnr : (N:ℝ) ≤ n := by exact_mod_cast hn
    have hnk : (n:ℝ) ≤ k * n := by nlinarith [mul_nonneg (sub_nonneg.mpr hkr) (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have harg : (N:ℝ) ≤ 2*(k:ℝ)*n+k+1 := by nlinarith
    have hM := (div_lt_iff₀ tpos).mp hN
    exact hM.le.trans ((mul_le_mul_of_nonneg_right harg tpos.le).trans
      (Real.self_le_sinh_iff.mpr (by positivity)))
  simpa [b, div_eq_mul_inv] using
    (tendsto_const_nhds (x := sinh t / (2 * cosh ((k:ℝ)*t)))).mul (tendsto_inv_atTop_zero.comp hg)

end A057081Proof

open OMA.S_oeis_a057081 A057081Proof Filter

theorem OMA.solution : type_of% @OMA.S_oeis_a057081.main := by
  intro k hk
  have hz := bzero k hk
  have hs : Tendsto (fun n : ℕ => (-1 : ℝ)^n * b k n) atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa [norm_mul] using tendsto_zero_iff_norm_tendsto_zero.mp hz
  simpa only [partial_sum, bfirst, sub_zero] using
    (tendsto_const_nhds (x := b k 0)).sub hs

#print axioms OMA.solution
