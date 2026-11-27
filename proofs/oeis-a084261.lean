import OMAStatements.S_oeis_a084261
import Mathlib.Tactic

namespace A084261Proof
open OMA.S_oeis_a084261 Finset

private theorem interlaced_step (j : ℕ) :
    2 * interlaced (j + 2) = ((j : ℤ) + 2) * interlaced j := by
  by_cases h : j % 2 = 0
  · have h' : (j + 2) % 2 = 0 := by omega
    have hd : (j + 2) / 2 = j / 2 + 1 := by omega
    have hj : 2 * (j / 2) = j := by omega
    have hj' : 2 * ((j / 2 : ℕ) : ℤ) = (j : ℤ) := by exact_mod_cast hj
    simp only [interlaced, h, h', ↓reduceIte, hd, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    linear_combination ((j / 2).factorial : ℤ) * hj'
  · simp [interlaced, h]

private theorem pascal (n : ℕ) (f : ℕ → ℤ) :
    transform (n + 1) f = transform n f + transform n (fun j => f (j + 1)) := by
  let F := fun j : ℕ => (n.choose j : ℤ) * f j
  have h : (∑ j ∈ range (n + 1), F (j + 1)) + F 0 = ∑ j ∈ range (n + 1), F j := by
    rw [← sum_range_succ', sum_range_succ]
    simp [F, Nat.choose_succ_self]
  change (∑ j ∈ range (n + 1 + 1), ((n + 1).choose j : ℤ) * f j) = _
  rw [sum_range_succ']
  simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, sum_add_distrib,
    Nat.choose_zero_right, Nat.cast_one, one_mul]
  simpa [F, transform, add_assoc, add_left_comm, add_comm] using
    congrArg (fun x => (∑ j ∈ range (n + 1), (n.choose j : ℤ) * f (j + 1)) + x) h

private theorem moment (n : ℕ) (f : ℕ → ℤ) :
    transform (n + 1) (fun j => (j : ℤ) * f j) =
      ((n : ℤ) + 1) * transform n (fun j => f (j + 1)) := by
  unfold transform
  rw [sum_range_succ', mul_sum]
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
  apply sum_congr rfl
  intro j _
  have h : ((n : ℤ) + 1) * (n.choose j : ℤ) =
      ((n + 1).choose (j + 1) : ℤ) * ((j : ℤ) + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq n j
  push_cast
  linear_combination -(f (j + 1)) * h

private theorem lifted (n : ℕ) :
    2 * transform n (fun j => interlaced (j + 2)) =
      transform n (fun j => (j : ℤ) * interlaced j) + 2 * transform n interlaced := by
  unfold transform
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  linear_combination (n.choose j : ℤ) * interlaced_step j

theorem recurrence (k : ℕ) :
    2 * a (k + 3) - 4 * a (k + 2) - ((k : ℤ) + 1) * a (k + 1)
      + ((k : ℤ) + 1) * a k = 0 := by
  unfold a
  have h := pascal (k + 1) (fun j => interlaced (j + 1))
  linear_combination 2 * pascal (k + 2) interlaced - 2 * pascal (k + 1) interlaced
    + 2 * h + lifted (k + 1) + moment k interlaced
    - ((k : ℤ) + 1) * pascal k interlaced

end A084261Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a084261.main :=
  A084261Proof.recurrence
