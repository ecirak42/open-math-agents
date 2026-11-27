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

/-- A tangent line to a differentiable concave function majorizes it. -/
theorem belowTangent {g : ℝ → ℝ} {D : Set ℝ} {x y c : ℝ}
    (hg : ConcaveOn ℝ D g) (hx : x ∈ D) (hy : y ∈ D) (hd : HasDerivAt g c x) :
    g y ≤ g x + c*(y-x) := by
  rcases lt_trichotomy x y with h | rfl | h
  · have hs := hg.slope_le_of_hasDerivAt hx hy h hd
    rw [slope_def_field] at hs
    linarith [(div_le_iff₀ (sub_pos.mpr h)).mp hs]
  · simp
  · have hs := hg.le_slope_of_hasDerivAt hy hx h hd
    rw [slope_def_field] at hs
    linarith [(le_div_iff₀ (sub_pos.mpr h)).mp hs]

/-- An exponential tangent with positive slope controls the area to its left. -/
theorem leftExpArea (f : ℝ → ℝ) (l x b c : ℝ) (hx : l ≤ x) (hb : 0 ≤ b)
    (hc : 0 < c) (hf : ContinuousOn f (Icc l x))
    (hpoint : ∀ t ∈ Ioo l x, f t ≤ b * Real.exp (c*t-c*x)) :
    (∫ t in l..x, f t) ≤ b/c := by
  have hcont : Continuous (fun t : ℝ => b * Real.exp (c*t-c*x)) := by fun_prop
  calc
    _ ≤ ∫ t in l..x, b * Real.exp (c*t-c*x) :=
      intervalIntegral.integral_mono_on_of_le_Ioo hx (hf.intervalIntegrable_of_Icc hx)
        (hcont.intervalIntegrable ..) hpoint
    _ = b * (c⁻¹ * (1-Real.exp (c*l-c*x))) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_mul_sub Real.exp hc.ne', integral_exp]
      simp [smul_eq_mul]
    _ ≤ _ := by
      rw [div_eq_mul_inv]
      have h := mul_nonneg (mul_nonneg hb (inv_nonneg.mpr hc.le))
        (Real.exp_pos (c*l-c*x)).le
      linarith

/-- One-dimensional preservation of log-concavity under cumulative integration. -/
theorem cdfLogConcave (f F : ℝ → ℝ) (l u : ℝ)
    (hf : ContinuousOn f (Icc l u))
    (hder : ∀ x ∈ Ioo l u, DifferentiableAt ℝ f x)
    (hfpos : ∀ x ∈ Ioo l u, 0 < f x)
    (hlog : ConcaveOn ℝ (Ioo l u) (fun x => Real.log (f x)))
    (hFpos : ∀ x ∈ Ioo l u, 0 < F x)
    (hFder : ∀ x ∈ Ioo l u, HasDerivAt F (f x) x)
    (hprim : ∀ x ∈ Ioo l u, F x = ∫ t in l..x, f t) :
    ConcaveOn ℝ (Ioo l u) (fun x => Real.log (F x)) := by
  have key (x : ℝ) (hx : x ∈ Ioo l u) : deriv f x * F x ≤ f x * f x := by
    by_cases hd : 0 < deriv f x
    · let c := deriv f x / f x
      have hc : 0 < c := div_pos hd (hfpos x hx)
      have hdlog : HasDerivAt (fun y => Real.log (f y)) c x :=
        (hder x hx).hasDerivAt.log (hfpos x hx).ne'
      have area := leftExpArea f l x (f x) c hx.1.le (hfpos x hx).le hc
        (hf.mono (Icc_subset_Icc le_rfl hx.2.le)) (by
          intro t ht
          have ht' : t ∈ Ioo l u := ⟨ht.1, ht.2.trans hx.2⟩
          have h := belowTangent hlog hx ht' hdlog
          have h' : Real.log (f t) ≤ Real.log (f x) + (c*t-c*x) := by linarith
          have := Real.exp_le_exp.mpr h'
          rwa [Real.exp_log (hfpos t ht'), Real.exp_add, Real.exp_log (hfpos x hx)] at this)
      rw [← hprim x hx] at area
      have h := (le_div_iff₀ hc).mp area
      change F x * (deriv f x / f x) ≤ f x at h
      rw [← mul_div_assoc] at h
      linarith [(div_le_iff₀ (hfpos x hx)).mp h]
    · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hd) (hFpos x hx).le).trans
        (mul_self_nonneg _)
  apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := fun x => f x/F x)
    (f'' := fun x => (deriv f x*F x - f x*f x)/(F x)^2) (convex_Ioo ..)
  · intro x hx
    exact ((hFder x hx).log (hFpos x hx).ne').continuousAt.continuousWithinAt
  · intro x hx
    have hmem := interior_subset hx
    exact ((hFder x hmem).log (hFpos x hmem).ne').hasDerivWithinAt
  · intro x hx
    have hmem := interior_subset hx
    exact ((hder x hmem).hasDerivAt.div (hFder x hmem) (hFpos x hmem).ne').hasDerivWithinAt
  · intro x hx
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (key x (interior_subset hx)))
      (sq_nonneg _)

theorem concaveReflection (g : ℝ → ℝ) (l u : ℝ) (hc : ConcaveOn ℝ (Ioo l u) g) :
    ConcaveOn ℝ (Ioo (-u) (-l)) (fun x => g (-x)) := by
  refine ⟨convex_Ioo .., ?_⟩
  intro x hx y hy a b ha hb hab
  have hx' : -x ∈ Ioo l u := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hy' : -y ∈ Ioo l u := ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have h := hc.2 hx' hy' ha hb hab
  simp only [smul_eq_mul] at *
  convert h using 2 <;> ring

/-- Reflecting the density proves the corresponding result for survival. -/
theorem survivalLogConcave (f F : ℝ → ℝ) (l u : ℝ)
    (hf : Continuous f) (hF : Continuous F)
    (hder : ∀ x ∈ Ioo l u, DifferentiableAt ℝ f x)
    (hfpos : ∀ x ∈ Ioo l u, 0 < f x)
    (hlog : ConcaveOn ℝ (Ioo l u) (fun x => Real.log (f x)))
    (hSpos : ∀ x ∈ Ioo l u, F x < 1)
    (hFder : ∀ x ∈ Ioo l u, HasDerivAt F (f x) x) (hFu : F u = 1) :
    ConcaveOn ℝ (Ioo l u) (fun x => Real.log (1-F x)) := by
  let g := fun x : ℝ => f (-x)
  let G := fun x : ℝ => 1-F (-x)
  have hx' (x : ℝ) (hx : x ∈ Ioo (-u) (-l)) : -x ∈ Ioo l u :=
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have cG : Continuous G := by dsimp [G]; fun_prop
  have cg : Continuous g := by dsimp [g]; fun_prop
  have hg (x : ℝ) (hx : x ∈ Ioo (-u) (-l)) : HasDerivAt G (g x) x := by
    have h := (hasDerivAt_const x (1:ℝ)).sub
      ((hFder (-x) (hx' x hx)).comp x (hasDerivAt_id x).neg)
    simpa [G,g] using h
  have prim (x : ℝ) (hx : x ∈ Ioo (-u) (-l)) : G x = ∫ t in -u..x, g t := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1.le cG.continuousOn
      (fun t ht => hg t ⟨ht.1, ht.2.trans hx.2⟩) (cg.intervalIntegrable ..)]
    simp [G,hFu]
  have h := cdfLogConcave g G (-u) (-l) cg.continuousOn
    (fun x hx => (hder (-x) (hx' x hx)).comp x (differentiableAt_id.neg))
    (fun x hx => hfpos _ (hx' x hx)) (concaveReflection _ _ _ hlog)
    (fun x hx => sub_pos.mpr (hSpos _ (hx' x hx))) hg prim
  simpa [G] using concaveReflection _ _ _ h

/-- The mass below the mean is at least 1/e. A tangent to log F and the
primitive of f log F avoid an improper integral at the lower endpoint. -/
theorem massAtMean (F M f : ℝ → ℝ) (l u μ : ℝ) (hμ : μ ∈ Ioo l u)
    (hF : Continuous F) (hM : Continuous M)
    (hFpos : ∀ x ∈ Ioo l u, 0 < F x) (hf : ∀ x ∈ Ioo l u, 0 ≤ f x)
    (hFder : ∀ x ∈ Ioo l u, HasDerivAt F (f x) x)
    (hMder : ∀ x ∈ Ioo l u, HasDerivAt M (x*f x) x)
    (hlog : ConcaveOn ℝ (Ioo l u) (fun x => Real.log (F x)))
    (hFl : F l = 0) (hFu : F u = 1) (hMl : M l = 0) (hMu : M u = μ) :
    (1:ℝ)/3 ≤ F μ := by
  let a := F μ
  let c := f μ / a
  let P := fun t : ℝ => (Real.log a-c*μ)*F t + c*M t + Real.negMulLog (F t) + F t
  have hP : Continuous P := by dsimp [P]; fun_prop
  have derivP (x : ℝ) (hx : x ∈ Ioo l u) :
      HasDerivAt P (f x*(Real.log a+c*(x-μ)-Real.log (F x))) x := by
    have d := hFder x hx
    have dm := hMder x hx
    have he := (Real.hasDerivAt_negMulLog (hFpos x hx).ne').comp x d
    have h := ((((d.const_mul (Real.log a-c*μ)).add (dm.const_mul c)).add he).add d)
    convert h using 1
    · rfl
    · ring
  have hm : MonotoneOn P (Icc l u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc ..) hP.continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      exact (derivP x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(derivP x hx).deriv]
      have hd : HasDerivAt (fun t => Real.log (F t)) c μ :=
        (hFder μ hμ).log (hFpos μ hμ).ne'
      have h := belowTangent hlog hμ hx hd
      exact mul_nonneg (hf x hx) (sub_nonneg.mpr h)
  have hlu := hμ.1.le.trans hμ.2.le
  have hend := hm (left_mem_Icc.mpr hlu) (right_mem_Icc.mpr hlu) hlu
  simp [P, hFl, hFu, hMl, hMu] at hend
  have hlo : -1 ≤ Real.log (F μ) := by dsimp [a] at hend; linarith
  have h := Real.exp_le_exp.mpr hlo
  rw [Real.exp_log (hFpos μ hμ), Real.exp_neg] at h
  refine le_trans ?_ h
  have he : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  simpa [one_div] using (inv_anti₀ (Real.exp_pos 1) he)

/-- The two areas about the mean agree by integration by parts. -/
theorem meanBalance (F f : ℝ → ℝ) (l μ u : ℝ) (hl : l ≤ μ) (hu : μ ≤ u)
    (hF : ContinuousOn F (Icc l u)) (hf : ContinuousOn f (Icc l u))
    (hder : ∀ x ∈ Ioo l u, HasDerivAt F (f x) x) (hleft : F l = 0)
    (hright : F u = 1) (hmean : (∫ x in l..u, x*f x) = μ) :
    (∫ x in l..μ, F x) = ∫ x in μ..u, 1-F x := by
  have hlu := hl.trans hu
  have hFu : ContinuousOn F (uIcc l u) := by simpa [uIcc_of_le hlu] using hF
  have hfu : ContinuousOn f (uIcc l u) := by simpa [uIcc_of_le hlu] using hf
  have h₁ := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := l) (b := u) (u := fun x : ℝ => x) (u' := fun _ => (1:ℝ))
    (v := F) (v' := f) continuous_id.continuousOn hFu
    (fun x _ => hasDerivAt_id x) (by simpa [min_eq_left hlu, max_eq_right hlu] using hder)
    intervalIntegrable_const hfu.intervalIntegrable
  simp only [one_mul, hleft, mul_zero, sub_zero, hright, mul_one, hmean] at h₁
  have h₂ : IntervalIntegrable F volume l μ :=
    (hF.mono (Icc_subset_Icc le_rfl hu)).intervalIntegrable_of_Icc hl
  have h₃ : IntervalIntegrable F volume μ u :=
    (hF.mono (Icc_subset_Icc hl le_rfl)).intervalIntegrable_of_Icc hu
  have h₄ := intervalIntegral.integral_add_adjacent_intervals h₂ h₃
  rw [intervalIntegral.integral_sub intervalIntegrable_const h₃,
    intervalIntegral.integral_const, smul_eq_mul]
  linarith

theorem tailBound (S : ℝ → ℝ) (μ u : ℝ) (hu : μ ≤ u) (hc : Continuous S)
    (hmid : ∀ x ∈ Icc μ ((μ+u)/2), S μ * S (2*x-μ) ≤ (S x)^2) :
    (∫ x in μ..u, (1-S x)*S x) ≤ (1-S μ/2) * ∫ x in μ..u, S x := by
  let m := (μ+u)/2
  have hm : μ ≤ m := by dsimp [m]; linarith
  have hmu : m ≤ u := by dsimp [m]; linarith
  have hsc : Continuous (fun x : ℝ => (S x)^2) := hc.pow 2
  have ha : Continuous (fun x : ℝ => S μ * S (2*x-μ)) :=
    continuous_const.mul (hc.comp (by fun_prop))
  have h := intervalIntegral.integral_mono_on (μ := volume) hm (ha.intervalIntegrable ..)
    (hsc.intervalIntegrable ..) hmid
  have hnext : 0 ≤ ∫ x in m..u, (S x)^2 :=
    intervalIntegral.integral_nonneg hmu (fun x _ => sq_nonneg _)
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
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
      ring

/-- Integrate the exponential chord supplied by log-concavity of survival. -/
theorem exponentialChord (F : ℝ → ℝ) (μ a H : ℝ) (hμ : 0 < μ) (hH : 0 < H)
    (hc : Continuous F) (hexp : Real.exp (-H) = 1-a)
    (hchord : ∀ x ∈ Icc 0 μ, F x ≤ 1-Real.exp ((-H/μ)*x)) :
    (∫ x in 0..μ, F x) ≤ μ*(1-a/H) := by
  have hc' : Continuous (fun x : ℝ => Real.exp ((-H/μ)*x)) := by fun_prop
  have hb : -H/μ ≠ 0 := div_ne_zero (neg_ne_zero.mpr hH.ne') hμ.ne'
  have hinv : (-H/μ)⁻¹ = -(μ/H) := by rw [inv_div, div_neg]
  calc
    _ ≤ ∫ x in 0..μ, 1-Real.exp ((-H/μ)*x) :=
      intervalIntegral.integral_mono_on hμ.le (hc.intervalIntegrable ..)
        ((continuous_const.sub hc').intervalIntegrable ..) hchord
    _ = _ := by
      rw [intervalIntegral.integral_sub (intervalIntegrable_const) (hc'.intervalIntegrable ..),
        intervalIntegral.integral_comp_mul_left Real.exp hb, integral_exp,
        mul_zero, Real.exp_zero, div_mul_cancel₀ _ hμ.ne', hexp,
        intervalIntegral.integral_const, smul_eq_mul, hinv]
      simp only [smul_eq_mul, div_eq_mul_inv]
      ring

theorem lowerBranch (μ a A I : ℝ) (hμ : 0 ≤ μ) (ha : 1/3 ≤ a)
    (hhead : A ≤ μ*a/2) (htail : I ≤ ((1+a)/2)*A) : I ≤ μ*a^2 := by
  have ha₀ : 0 ≤ a := by linarith
  have h₁ := mul_le_mul_of_nonneg_left hhead (show 0 ≤ (1+a)/2 by linarith)
  nlinarith [mul_nonneg (mul_nonneg hμ ha₀) (show 0 ≤ 3*a-1 by linarith)]

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
    convert h using 1
    · funext t
      rfl
    · norm_num
      field_simp
      ring
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
  simp [f] at h
  linarith

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

/-- Combine the pointwise shape inequalities. In the lower case the CDF
lies below its chord. In the upper case survival lies above its log chord. -/
theorem conclusionOfShapes (F : ℝ → ℝ) (μ u : ℝ) (hc : Continuous F)
    (hμ : 0 < μ) (hu : μ ≤ u) (ha : 0 < F μ) (ha' : F μ < 1)
    (balance : (∫ x in 0..μ, F x) = ∫ x in μ..u, 1-F x)
    (mid : ∀ x ∈ Icc μ ((μ+u)/2), (1-F μ)*(1-F (2*x-μ)) ≤ (1-F x)^2)
    (mode : (1/3 ≤ F μ ∧ ∀ x ∈ Icc 0 μ, F x ≤ x*(F μ/μ)) ∨
      (2/5 ≤ F μ ∧ ∀ x ∈ Icc 0 μ, F x ≤ 1-Real.exp ((Real.log (1-F μ)/μ)*x))) :
    (∫ x in μ..u, F x*(1-F x)) ≤ μ*(F μ)^2 := by
  let S := fun x : ℝ => 1-F x
  have ht := tailBound S μ u hu (continuous_const.sub hc) mid
  dsimp [S] at ht
  have hs : 1-(1-F μ)/2 = (1+F μ)/2 := by ring
  simp only [sub_sub_cancel, hs, ← balance] at ht
  rcases mode with ⟨ha₁, h₁⟩ | ⟨ha₂, h₂⟩
  · exact lowerBranch _ _ _ _ hμ.le ha₁ (leftChordBound _ _ hμ hc h₁) ht
  · let H := -Real.log (1-F μ)
    have hpos : 0 < H := neg_pos.mpr (Real.log_neg (by linarith) (by linarith))
    have he : Real.exp (-H) = 1-F μ := by
      dsimp [H]
      rw [neg_neg, Real.exp_log (by linarith)]
    have hhead := exponentialChord F μ (F μ) H hμ hpos hc he
      (by simpa [H] using h₂)
    exact upperBranch _ _ _ _ _ hμ.le ha₂ ha' rfl hhead ht

end LogConcaveTail

#print axioms LogConcaveTail.survivalLogConcave
#print axioms LogConcaveTail.massAtMean
#print axioms LogConcaveTail.cdfLogConcave
#print axioms LogConcaveTail.meanBalance
#print axioms LogConcaveTail.tailBound
#print axioms LogConcaveTail.leftChordBound
#print axioms LogConcaveTail.exponentialChord
#print axioms LogConcaveTail.lowerBranch
#print axioms LogConcaveTail.negLogBound
#print axioms LogConcaveTail.upperBranch
#print axioms LogConcaveTail.conclusionOfShapes
