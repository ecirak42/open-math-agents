import OMAStatements.S_oeis_a228791
import Mathlib.Tactic

/-!
# OEIS A228791

The five last-row counts imply a second-order recurrence after the
first extension. The roots of its characteristic polynomial give
Barker's closed form, as fixed by the values at two and three rows.
-/

namespace OMA.S_oeis_a228791

private theorem threeSteps (v : Rows) :
    (extend (extend (extend v))).total =
      5 * (extend (extend v)).total - 3 * (extend v).total := by
  simp [extend, Rows.total]
  ring

private theorem recurrence (n : Nat) :
    a (n+4) = 5*a (n+3) - 3*a (n+2) :=
  threeSteps (state n)

private theorem series (n : Nat) : productCoeff n = numeratorCoeff n := by
  match n with
  | 0 | 1 | 2 | 3 => decide
  | k + 4 =>
    have h := recurrence k
    change a (k+4) - 5*a (k+3) + 3*a (k+2) = 0
    omega

private noncomputable def radicalSum (n : Nat) : ℝ :=
  -(2 * ((-11 + Real.sqrt 13) * ((5 + Real.sqrt 13)/2)^n +
    ((5 - Real.sqrt 13)/2)^n * (11 + Real.sqrt 13))) / (9 * Real.sqrt 13)

private theorem normalized (n : Nat) : closedForm n = radicalSum n := by
  simp only [closedForm, radicalSum, div_pow]
  ring

private theorem powerRec (r : ℝ) (hr : r^2 = 5*r - 3) (n : Nat) :
    r^(n+2) = 5*r^(n+1) - 3*r^n := by
  simp only [pow_add, pow_one]
  rw [hr]
  ring

private theorem radicalRec (n : Nat) :
    radicalSum (n+2) = 5*radicalSum (n+1) - 3*radicalSum n := by
  have hs : (Real.sqrt 13)^2 = 13 := Real.sq_sqrt (by norm_num)
  have hp : ((5 + Real.sqrt 13)/2)^2 = 5*((5 + Real.sqrt 13)/2) - 3 := by
    nlinarith
  have hm : ((5 - Real.sqrt 13)/2)^2 = 5*((5 - Real.sqrt 13)/2) - 3 := by
    nlinarith
  unfold radicalSum
  rw [powerRec _ hp n, powerRec _ hm n]
  ring

private theorem allRadicals (k : Nat) : (a (k+2) : ℝ) = radicalSum (k+2) := by
  have hs : (Real.sqrt 13)^2 = 13 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt 13 ≠ 0 := by positivity
  have hc : (Real.sqrt 13)^3 = 13 * Real.sqrt 13 := by
    calc
      _ = (Real.sqrt 13)^2 * Real.sqrt 13 := by ring
      _ = _ := by rw [hs]
  have pair : ∀ j : Nat,
      (a (j+2) : ℝ) = radicalSum (j+2) ∧ (a (j+3) : ℝ) = radicalSum (j+3) := by
    intro j
    induction j with
    | zero =>
      constructor <;> norm_num [a, state, extend, Rows.total, radicalSum] <;>
        field_simp [hne] <;> nlinarith
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      change (a (j+4) : ℝ) = radicalSum ((j+2)+2)
      rw [recurrence, radicalRec]
      push_cast
      rw [ih.1, ih.2]
  exact (pair k).1

end OMA.S_oeis_a228791

open OMA.S_oeis_a228791

theorem OMA.solution : type_of% @OMA.S_oeis_a228791.main := by
  refine ⟨series, ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n-2, by omega⟩
  rw [normalized]
  exact allRadicals k
