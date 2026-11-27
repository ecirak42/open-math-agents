import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Basic

/-!
# OEIS A385736

Felix Huber asks which triangular numbers are perimeters of nondegenerate
triangles with triangular sides. The three strict triangle inequalities
ensure that the sides are positive and exclude collinear triangles.

Source: https://oeis.org/A385736
Formalization: @ecirak42.
-/

namespace OMA.S_oeis_a385736

def triangular (n : ℕ) : ℕ := (n + 1).choose 2

def fits (p i j k : ℕ) : Prop :=
  let x := triangular i
  let y := triangular j
  let z := triangular k
  x + y + z = p ∧ z < x + y ∧ y < x + z ∧ x < y + z

def perimeter (p : ℕ) : Prop := ∃ i j k : ℕ, fits p i j k

def exceptional (p : ℕ) : Prop := p = 0 ∨ p = 1 ∨ p = 6 ∨ p = 10 ∨ p = 28 ∨ p = 55

theorem main : ∀ n : ℕ, ¬ perimeter (triangular n) ↔ exceptional (triangular n) := by
  sorry

end OMA.S_oeis_a385736


namespace TriangularPerimeters
open OMA.S_oeis_a385736

private theorem next (n : ℕ) : triangular (n + 1) = (n + 1) + triangular n := by
  simpa only [triangular, Nat.choose_one_right] using Nat.choose_succ_succ (n + 1) 1

private theorem twice (n : ℕ) : 2 * triangular n = n * (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih => rw [next]; nlinarith

private theorem bounded {i : ℕ} (h : triangular i ≤ 55) : i < 11 := by
  have hm : Monotone triangular :=
    monotone_nat_of_le_succ (fun n => by rw [next]; omega)
  by_contra! hn
  have hb := hm hn
  have he : triangular 11 = 66 := by decide
  omega

set_option maxRecDepth 4096 in
private theorem small : ∀ i j k : Fin 11,
    let x := triangular i
    let y := triangular j
    let z := triangular k
    exceptional (x + y + z) → ¬ (z < x + y ∧ y < x + z ∧ x < y + z) := by
  unfold exceptional
  decide

private theorem excluded {p : ℕ} (he : exceptional p) : ¬ perimeter p := by
  rintro ⟨i, j, k, h⟩
  obtain ⟨hs, ht⟩ := h
  have hp : p ≤ 55 := by unfold exceptional at he; omega
  have hi := bounded (i := i) (by omega)
  have hj := bounded (i := j) (by omega)
  have hk := bounded (i := k) (by omega)
  exact small ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ (hs.symm ▸ he) ht

private theorem divisibleThree (r : ℕ) : perimeter (triangular (3 * (r + 2))) := by
  refine ⟨r + 1, 2 * (r + 2), 2 * (r + 2), ?_⟩
  have hP := twice (3 * (r + 2))
  have hx := twice (r + 1)
  have hy := twice (2 * (r + 2))
  unfold fits
  exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

private theorem remainderOne (r : ℕ) : perimeter (triangular (3 * (r + 4) + 1)) := by
  refine ⟨r + 4, 2 * (r + 4), 2 * (r + 4) + 1, ?_⟩
  have hP := twice (3 * (r + 4) + 1)
  have hx := twice (r + 4)
  have hy := twice (2 * (r + 4))
  have hz := twice (2 * (r + 4) + 1)
  unfold fits
  exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

private theorem remainderTwo (r : ℕ) : perimeter (triangular (3 * r + 2)) := by
  refine ⟨r + 1, 2 * r + 1, 2 * r + 1, ?_⟩
  have hP := twice (3 * r + 2)
  have hx := twice (r + 1)
  have hy := twice (2 * r + 1)
  unfold fits
  exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

theorem classification (n : ℕ) : ¬ perimeter (triangular n) ↔ exceptional (triangular n) := by
  refine ⟨fun hn => ?_, excluded⟩
  by_contra he
  apply hn
  by_cases hsmall : n ≤ 10
  · interval_cases n <;> first
    | exact (he (by unfold exceptional; decide)).elim
    | exact remainderTwo 0
    | exact remainderTwo 1
    | exact remainderTwo 2
    | exact divisibleThree 0
    | exact divisibleThree 1
  · have hr : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hr with hr | hr | hr
    · convert divisibleThree (n / 3 - 2) using 1
      congr 2
      omega
    · convert remainderOne (n / 3 - 4) using 1
      congr 2
      omega
    · convert remainderTwo (n / 3) using 1
      congr 2
      omega

end TriangularPerimeters

theorem OMA.solution : type_of% @OMA.S_oeis_a385736.main := TriangularPerimeters.classification

#print axioms OMA.solution
