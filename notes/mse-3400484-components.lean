import Mathlib

/-!
# A tail inequality at the mean for a log-concave density

The question by smcc asks for an inequality for every differentiable
log-concave probability density on a bounded interval with nonnegative
left endpoint. The CDF and the mean below use the original density.
The values of the density outside its interval of support play no role.

Source: https://math.stackexchange.com/q/3400484 (2019, CC BY-SA 4.0)
Credit: @ecirak42
-/

namespace OMA.S_mse_3400484

open MeasureTheory

noncomputable def cdf (f : ℝ → ℝ) (l x : ℝ) : ℝ := ∫ t in l..x, f t
noncomputable def mean (f : ℝ → ℝ) (l u : ℝ) : ℝ := ∫ x in l..u, x * f x

theorem main : ∀ (l u : ℝ) (f : ℝ → ℝ),
    0 ≤ l → l < u → DifferentiableOn ℝ f (Set.Icc l u) →
    (∀ x ∈ Set.Icc l u, 0 ≤ f x) → (∀ x ∈ Set.Ioo l u, 0 < f x) →
    ConcaveOn ℝ (Set.Ioo l u) (fun x => Real.log (f x)) →
    (∫ x in l..u, f x) = 1 →
    let μ := mean f l u
    (∫ x in μ..u, cdf f l x * (1 - cdf f l x)) ≤ μ * (cdf f l μ)^2 := by
  sorry

end OMA.S_mse_3400484

/-!
# The analytic estimates for the log-concave tail inequality

These lemmas certify the integral and scalar estimates in the mathematical
proof of Math.SE 3400484. The pointwise midpoint hypothesis is exactly the
instance of the survival function's log-concavity used in the tail bound.
-/

namespace LogConcaveTail

open MeasureTheory Set

theorem tailBound (S : ℝ → ℝ) (μ u : ℝ) (hu : μ ≤ u) (hc : Continuous S)
    (hmid : ∀ x ∈ Icc μ ((μ+u)/2), S μ * S (2*x-μ) ≤ (S x)^2) :
    (∫ x in μ..u, (1-S x)*S x) ≤ (1-S μ/2) * ∫ x in μ..u, S x := by
  let m := (μ+u)/2
  have hm : μ ≤ m := by dsimp [m]; linarith
  have hmu : m ≤ u := by dsimp [m]; linarith
  have hsc : Continuous (fun x : ℝ => (S x)^2) := hc.pow 2
  have ha : Continuous (fun x : ℝ => S μ * S (2*x-μ)) :=
    continuous_const.mul (hc.comp (by fun_prop))
  have h := intervalIntegral.integral_mono_on hm (ha.intervalIntegrable ..)
    (hsc.intervalIntegrable ..) hmid
  have hnext : 0 ≤ ∫ x in m..u, (S x)^2 :=
    intervalIntegral.integral_nonneg hmu (fun x _ => sq_nonneg _)
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hsc.intervalIntegrable μ m) (hsc.intervalIntegrable m u)
  have hchange : (∫ x in μ..m, S (2*x-μ)) = (1/2) * ∫ x in μ..u, S x := by
    rw [intervalIntegral.integral_comp_mul_sub S (by norm_num : (2:ℝ) ≠ 0) μ]
    have h₁ : 2*μ-μ = μ := by ring
    have h₂ : 2*m-μ = u := by dsimp [m]; ring
    rw [h₁,h₂]
    simp [smul_eq_mul]
  rw [intervalIntegral.integral_const_mul, hchange] at h
  have hid : (∫ x in μ..u, (1-S x)*S x) =
      (∫ x in μ..u, S x) - ∫ x in μ..u, (S x)^2 := by
    rw [← intervalIntegral.integral_sub (hc.intervalIntegrable μ u)
      (hsc.intervalIntegrable μ u)]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hid]
  linarith

theorem leftChordBound (F : ℝ → ℝ) (μ : ℝ) (hμ : 0 < μ) (hc : Continuous F)
    (hchord : ∀ x ∈ Icc 0 μ, F x ≤ x * (F μ / μ)) :
    (∫ x in 0..μ, F x) ≤ μ * F μ / 2 := by
  have hlin : Continuous (fun x : ℝ => x * (F μ / μ)) := by fun_prop
  calc
    _ ≤ ∫ x in 0..μ, x * (F μ / μ) :=
      intervalIntegral.integral_mono_on hμ.le (hc.intervalIntegrable ..)
        (hlin.intervalIntegrable ..) hchord
    _ = _ := by
      rw [intervalIntegral.integral_mul_const, integral_id]
      field_simp
      <;> ring

/-- The logarithm estimate follows by integrating an elementary rational majorant. -/
theorem negLogBound (a : ℝ) (ha : 0 ≤ a) (ha' : a < 1) :
    -Real.log (1-a) ≤ a + a^2/2 + a^3/(3*(1-a)) := by
  let f (x : ℝ) := x + x^2/2 + x^3/(3*(1-x)) + Real.log (1-x)
  have hd (x : ℝ) (hx : x < 1) : HasDerivAt f (x^3/(3*(1-x)^2)) x := by
    have h₀ : 1-x ≠ 0 := by linarith
    have h₁ : 3*(1-x) ≠ 0 := mul_ne_zero (by norm_num) h₀
    have hd₁ : HasDerivAt (fun t : ℝ => 1-t) (0-1) x :=
      (hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)
    have h := (((hasDerivAt_id x).add (((hasDerivAt_pow 2 x).div_const 2))).add
      ((hasDerivAt_pow 3 x).div (hd₁.const_mul 3) h₁)).add (hd₁.log h₀)
    convert h using 1 <;> dsimp [f] <;> field_simp <;> ring
  have hdiff : DifferentiableOn ℝ f (Icc 0 a) :=
    fun x hx => (hd x (lt_of_le_of_lt hx.2 ha')).differentiableAt.differentiableWithinAt
  have hm : MonotoneOn f (Icc 0 a) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc ..) hdiff.continuousOn
      (hdiff.mono interior_subset)
    intro x hx
    have hmem : x ∈ Icc 0 a := interior_subset hx
    rw [(hd x (lt_of_le_of_lt hmem.2 ha')).deriv]
    have hx₀ := hmem.1
    positivity
  have h := hm (left_mem_Icc.mpr ha) (right_mem_Icc.mpr ha) ha
  simpa [f] using (show -Real.log (1-a) ≤ a+a^2/2+a^3/(3*(1-a)) by
    dsimp [f] at h
    simp only [zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 3 ≠ 0),
      zero_div, zero_add, sub_zero, Real.log_one, add_zero] at h
    linarith)

theorem upperBranch (μ a H A I : ℝ) (hμ : 0 ≤ μ) (ha : 2/5 ≤ a) (ha' : a < 1)
    (hH : H = -Real.log (1-a)) (hhead : A ≤ μ*(1-a/H))
    (htail : I ≤ ((1+a)/2)*A) : I ≤ μ*a^2 := by
  have ha₀ : 0 < a := by linarith
  have hd : 0 < 1-a := by linarith
  have hH₀ : 0 < H := by rw [hH]; exact neg_pos.mpr (Real.log_neg hd (by linarith))
  have hpoly : 3 ≤ 7*a+2*a^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ a+2/5 by linarith)]
  have hmajor := negLogBound a ha₀.le ha'
  have hden : 0 < (1-a)*(1+2*a) := by positivity
  have h₁ : H ≤ a*(1+a)/((1-a)*(1+2*a)) := by
    rw [hH]
    apply hmajor.trans
    field_simp
    nlinarith [mul_nonneg (show 0 ≤ 2*a^2+7*a-3 by linarith) ha₀.le]
  have h₂ := (le_div_iff₀ hden).mp h₁
  have h₃ : ((1+a)/2)*(1-a/H) ≤ a^2 := by
    field_simp
    nlinarith
  have h₄ := mul_le_mul_of_nonneg_left hhead (show 0 ≤ (1+a)/2 by linarith)
  have h₅ := mul_le_mul_of_nonneg_left h₃ hμ
  nlinarith

end LogConcaveTail

#print axioms LogConcaveTail.tailBound
#print axioms LogConcaveTail.leftChordBound
#print axioms LogConcaveTail.negLogBound
#print axioms LogConcaveTail.upperBranch
