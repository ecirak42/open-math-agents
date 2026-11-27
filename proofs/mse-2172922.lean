import Mathlib

/-!
# Fractional parts of partial sums of natural logarithms

E. Joseph asked whether, for every positive ε, infinitely many N have
fractional part of the sum of log n from n = 2 to N less than ε.
Infinitely many natural indices are expressed by the existence of a witness
above every bound.

Source: https://math.stackexchange.com/q/2172922 (2017, CC BY-SA 3.0)
Credit: @ecirak42
-/

namespace OMA.S_mse_2172922

/-- The sum of log 2, ..., log N. -/
noncomputable def logSum (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 2 N, Real.log (j : ℝ)

theorem main : ∀ ε : ℝ, 0 < ε → ∀ B : ℕ, ∃ N : ℕ,
    B < N ∧ Int.fract (logSum N) < ε := by
  sorry

end OMA.S_mse_2172922


/-!
Subtract an integer from each logarithmic increment on a long block where
these translated increments are positive and small. The translated sum must
cross an integer, with overshoot less than ε.

Credit: @ecirak42
-/

namespace OMA
open S_mse_2172922

/-- Positive increments accumulate to at least one. If each is smaller than ε,
the first crossing of the next integer has overshoot less than ε. -/
private theorem crossing (y : ℕ → ℝ) (L : ℕ) (d ε : ℝ)
    (hL : 1 ≤ (L : ℝ) * d)
    (hs : ∀ i < L, d ≤ y (i + 1) - y i ∧ y (i + 1) - y i < ε) :
    ∃ i ≤ L, ∃ z : ℤ, (z : ℝ) ≤ y i ∧ y i < (z : ℝ) + ε := by
  let z : ℤ := ⌊y 0⌋ + 1
  have hstart : y 0 < (z : ℝ) := by
    simp [z]
  have hz : (z : ℝ) ≤ y 0 + 1 := by
    simpa [z] using add_le_add_right (Int.floor_le (y 0)) 1
  have growth : ∀ i ≤ L, y 0 + (i : ℝ) * d ≤ y i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      intro hi
      have h := (hs i (by omega)).1
      have hp := ih (by omega)
      push_cast
      linarith
  by_contra! h
  have below : ∀ i ≤ L, y i < (z : ℝ) := by
    intro i
    induction i with
    | zero => exact fun _ => hstart
    | succ i ih =>
      intro hi
      have hp := ih (by omega)
      have hstep := (hs i (by omega)).2
      by_contra! hcross
      have := h (i+1) hi z hcross
      linarith
  have := below L le_rfl
  have := growth L le_rfl
  linarith

/-- Exponential growth supplies arbitrarily late blocks of length L on which
each logarithm lies between m+d and m+2d for a single natural number m. -/
private theorem logBlock (d : ℝ) (hd : 0 < d) (B L : ℕ) :
    ∃ m s : ℕ, B < s ∧ ∀ i < L,
      (m : ℝ) + d ≤ Real.log (((s + i : ℕ) : ℝ) + 1) ∧
      Real.log (((s + i : ℕ) : ℝ) + 1) < (m : ℝ) + 2*d := by
  let c := Real.exp (2*d) - Real.exp d
  have hc : 0 < c := sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))
  obtain ⟨m, hm⟩ := exists_nat_gt (max (B : ℝ) (((L : ℝ) + 2) / c))
  have hB : (B : ℝ) < m := lt_of_le_of_lt (le_max_left _ _) hm
  have hm' := lt_of_le_of_lt (le_max_right _ _) hm
  have hwidth : (L : ℝ) + 2 < Real.exp ((m : ℝ) + 2*d) - Real.exp ((m : ℝ) + d) := by
    have h₁ := (div_lt_iff₀ hc).mp hm'
    have h₂ := Real.add_one_le_exp (m : ℝ)
    have h₃ : (m : ℝ) ≤ Real.exp m := by linarith
    have h₄ := mul_le_mul_of_nonneg_right h₃ hc.le
    rw [Real.exp_add, Real.exp_add, ← mul_sub]
    exact lt_of_lt_of_le h₁ h₄
  let x := Real.exp ((m : ℝ) + d)
  let s : ℕ := ⌈x⌉₊
  have hs : x ≤ (s : ℝ) := Nat.le_ceil x
  have hs' : (s : ℝ) < x + 1 := Nat.ceil_lt_add_one (Real.exp_pos _).le
  have hms := Real.add_one_le_exp ((m : ℝ) + d)
  have hBs : (B : ℝ) < s := by dsimp [x] at hs; linarith
  refine ⟨m, s, by exact_mod_cast hBs, ?_⟩
  intro i hi
  have hi' : (i : ℝ) < L := by exact_mod_cast hi
  have hp : 0 < (((s + i : ℕ) : ℝ) + 1) := by positivity
  constructor
  · apply (Real.le_log_iff_exp_le hp).mpr
    push_cast
    dsimp [x] at hs
    linarith [Nat.cast_nonneg (α := ℝ) i]
  · apply (Real.log_lt_iff_lt_exp hp).mpr
    push_cast
    dsimp [x] at hs'
    linarith

theorem solution : type_of% OMA.S_mse_2172922.main := by
  intro ε hε B
  let d := ε / 3
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨L, hL⟩ := exists_nat_gt (1/d)
  have hl := ((div_lt_iff₀ hd).mp hL).le
  obtain ⟨m, s, hBs, hblock⟩ := logBlock d hd B L
  let y (i : ℕ) := logSum (s+i) - (i : ℝ) * m
  have inc (i : ℕ) : y (i+1) - y i =
      Real.log (((s + i : ℕ) : ℝ) + 1) - m := by
    have hs : 2 ≤ (s+i)+1 := by omega
    simp only [y, logSum, ← Nat.add_assoc, Finset.sum_Icc_succ_top hs, Nat.cast_add,
      Nat.cast_one]
    ring
  have hstep (i : ℕ) (hi : i < L) : d ≤ y (i+1) - y i ∧ y (i+1) - y i < ε := by
    rw [inc]
    obtain ⟨lo, hi'⟩ := hblock i hi
    dsimp [d] at *
    constructor <;> linarith
  obtain ⟨i, _, z, hlo, hhi⟩ := crossing y L d ε hl hstep
  refine ⟨s+i, by omega, ?_⟩
  let w : ℤ := z + (i : ℤ) * m
  have hw : (w : ℝ) = (z : ℝ) + (i : ℝ) * m := by simp [w]
  dsimp [y] at hlo hhi
  have hwle : (w : ℝ) ≤ logSum (s+i) := by rw [hw]; linarith
  have hfloor : w ≤ ⌊logSum (s+i)⌋ := Int.le_floor.mpr hwle
  have hfloor' : (w : ℝ) ≤ (⌊logSum (s+i)⌋ : ℝ) := by exact_mod_cast hfloor
  rw [Int.fract]
  rw [hw] at hfloor'
  linarith

end OMA

#print axioms OMA.solution
