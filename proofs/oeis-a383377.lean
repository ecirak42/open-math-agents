import OMAStatements.S_oeis_a383377
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

namespace A383377Proof
open PowerSeries Finset

private theorem cast_abs (a : ℤ) : (↑|a| : ZMod 2) = (a : ZMod 2) := by
  rcases le_total 0 a with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, Int.cast_neg]
    have htwo : (2 : ZMod 2) = 0 := by decide
    linear_combination -(a : ZMod 2) * htwo

private theorem geometric (S B : PowerSeries (ZMod 2))
    (hs : ∀ n, coeff n S = ∑ j ∈ range (n + 1), coeff (n - j) (B ^ j)) :
    S * (1 - X * B) = 1 := by
  let q : PowerSeries (ZMod 2) := X * B
  have hc (n j : ℕ) : coeff n (q ^ j) =
      if j ≤ n then coeff (n - j) (B ^ j) else 0 := by
    rw [show q ^ j = X ^ j * B ^ j by exact mul_pow _ _ _, coeff_X_pow_mul']
  have htrunc (N : ℕ) : X ^ N ∣ S - ∑ j ∈ range N, q ^ j := by
    rw [X_pow_dvd_iff]
    intro n hn
    rw [map_sub, sub_eq_zero, map_sum, hs]
    refine (sum_congr rfl (fun j hj => ?_)).trans
      (sum_subset (range_mono (show n + 1 ≤ N by omega)) (fun j _ hj => ?_))
    · simp only [hc, Nat.le_of_lt_succ (mem_range.mp hj), ↓reduceIte]
    · simp only [hc, (by simpa using hj : ¬ j ≤ n), ↓reduceIte]
  suffices hz : S * (1 - q) - 1 = 0 from sub_eq_zero.mp hz
  ext n
  have hdiv : X ^ (n + 1) ∣ S * (1 - q) - 1 := by
    let G := ∑ j ∈ range (n + 1), q ^ j
    have hG : G * (1 - q) = 1 - q ^ (n + 1) := geom_sum_mul_neg q (n + 1)
    have hpow : X ^ (n + 1) ∣ q ^ (n + 1) := ⟨B ^ (n + 1), mul_pow _ _ _⟩
    have hD : X ^ (n + 1) ∣ (S - G) * (1 - q) - q ^ (n + 1) :=
      dvd_sub (dvd_mul_of_dvd_left (htrunc _) _) hpow
    convert hD using 1
    linear_combination hG
  simpa only [map_zero] using X_pow_dvd_iff.mp hdiv n (Nat.lt_succ_self n)

end A383377Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a383377.main := by
  intro A hA n hn
  let red := Int.castRingHom (ZMod 2)
  let S := PowerSeries.map red (A : PowerSeries ℤ)
  let B := PowerSeries.map red (↑A⁻¹ : PowerSeries ℤ)
  have hs (k : ℕ) : PowerSeries.coeff k S =
      ∑ j ∈ Finset.range (k + 1), PowerSeries.coeff (k - j) (B ^ j) := by
    change red (PowerSeries.coeff k (A : PowerSeries ℤ)) = _
    rw [hA, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [show B ^ j = PowerSeries.map red ((↑A⁻¹ : PowerSeries ℤ) ^ j) from
      (map_pow _ _ _).symm, PowerSeries.coeff_map]
    exact A383377Proof.cast_abs _
  have hSB : S * B = 1 := by
    change PowerSeries.map red _ * PowerSeries.map red _ = 1
    rw [← map_mul, Units.mul_inv, map_one]
  have hgeo := A383377Proof.geometric S B hs
  have hform : S = 1 + PowerSeries.X := by
    linear_combination hgeo + PowerSeries.X * hSB
  have hred : ((PowerSeries.coeff n (A : PowerSeries ℤ) : ℤ) : ZMod 2) = 0 := by
    change PowerSeries.coeff n S = 0
    rw [hform, map_add, PowerSeries.coeff_one, PowerSeries.coeff_X]
    simp [show n ≠ 0 by omega, show n ≠ 1 by omega]
  exact even_iff_two_dvd.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hred)
