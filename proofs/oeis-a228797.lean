import OMAStatements.S_oeis_a228797
import Mathlib.Tactic

/-!
# OEIS A228797

Three column extensions give the recurrence with coefficients 1, 3, 1.
The three exponential terms in Barker's closed form satisfy it because
their bases are the roots of (X+1)(X²−2X−1).
-/

namespace OMA.S_oeis_a228797

private theorem threeSteps (v : Columns) :
    (extend (extend (extend v))).total =
      (extend (extend v)).total + 3 * (extend v).total + v.total := by
  simp [extend, Columns.total]
  ring

private theorem recurrence (n : Nat) :
    a (n + 3) = a (n + 2) + 3 * a (n + 1) + a n := by
  cases n with
  | zero => decide
  | succ n => exact threeSteps (state n)

private theorem series (n : Nat) :
    productCoeff n = (if n = 1 then 2 else 0) := by
  match n with
  | 0 | 1 | 2 => decide
  | k + 3 =>
    have h := recurrence k
    simp [productCoeff]
    omega

private theorem radicalRoot (u : ℝ) (hu : u^2 = 2) :
    (1+u)^3 = (1+u)^2 + 3*(1+u) + 1 := by
  calc
    (1+u)^3 = (1+u)^2 + 3*(1+u) + 1 + (u+2)*(u^2-2) := by ring
    _ = _ := by rw [hu]; ring

private theorem powerRec (r : ℝ) (h : r^3 = r^2 + 3*r + 1) (n : Nat) :
    r^(n+3) = r^(n+2) + 3*r^(n+1) + r^n := by
  simp only [pow_add, pow_one]
  rw [h]
  ring

private theorem closedRec (n : Nat) :
    closedForm (n+3) = closedForm (n+2) + 3*closedForm (n+1) + closedForm n := by
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hp := radicalRoot (Real.sqrt 2) hs
  have hm : (1 - Real.sqrt 2)^3 =
      (1 - Real.sqrt 2)^2 + 3*(1 - Real.sqrt 2) + 1 := by
    simpa only [sub_eq_add_neg] using radicalRoot (-Real.sqrt 2) (by nlinarith)
  unfold closedForm
  rw [powerRec (-1) (by norm_num) n, powerRec _ hm n, powerRec _ hp n]
  ring

private theorem allClosed (n : Nat) : (a n : ℝ) = closedForm n := by
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have triple : ∀ k : Nat,
      (a k : ℝ) = closedForm k ∧ (a (k+1) : ℝ) = closedForm (k+1) ∧
      (a (k+2) : ℝ) = closedForm (k+2) := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_, ?_⟩ <;>
        norm_num [a, state, extend, Columns.total, closedForm] <;> nlinarith
    | succ k ih =>
      refine ⟨ih.2.1, ih.2.2, ?_⟩
      change (a (k+3) : ℝ) = closedForm (k+3)
      rw [recurrence, closedRec]
      push_cast
      rw [ih.1, ih.2.1, ih.2.2]
  exact (triple n).1

end OMA.S_oeis_a228797

open OMA.S_oeis_a228797

theorem OMA.solution : type_of% @OMA.S_oeis_a228797.main :=
  ⟨series, fun n _ => allClosed n⟩
