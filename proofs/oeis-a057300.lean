import OMAStatements.S_oeis_a057300
import Mathlib

namespace A057300Proof

open OMA.S_oeis_a057300

private theorem appendDigit (q r : ℕ) (hr : r < 4) :
    a (4*q+r) = 4*a q + swapDigit r := by
  rw [a]
  split
  · rename_i hz
    obtain rfl : q = 0 := by omega
    obtain rfl : r = 0 := by omega
    simp [a, swapDigit]
  · rw [show (4*q+r)/4 = q by omega, show (4*q+r)%4 = r by omega]

private theorem appendBit (q r b : ℕ) (hb : b < 2) :
    a (2*(4*q+r)+b) = 4*a (2*q+r/2) + swapDigit (2*(r%2)+b) := by
  rw [show 2*(4*q+r)+b = 4*(2*q+r/2)+(2*(r%2)+b) by omega]
  exact appendDigit _ _ (by omega)

private def Recurrences (n : ℕ) : Prop :=
  a (2*n) + 2*a n = 5*n ∧ a (2*n+1) + 2*a n = 5*n+2

private theorem nextDigit (q r : ℕ) (hr : r < 4) (hq : Recurrences q) :
    Recurrences (4*q+r) := by
  obtain ⟨heven, hodd⟩ := hq
  have ha := appendDigit q r hr
  have h0 := appendBit q r 0 (by decide)
  have h1 := appendBit q r 1 (by decide)
  unfold Recurrences
  interval_cases r <;> norm_num [swapDigit] at ha h0 h1 ⊢ <;> omega

theorem allCases (n : ℕ) : Recurrences n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n = 0
    · subst n
      have hzero : a 0 = 0 := by rw [a, if_pos rfl]
      have hone := appendDigit 0 1 (by decide)
      change a 1 = 4 * a 0 + 2 at hone
      change a 0 + 2 * a 0 = 0 ∧ a 1 + 2 * a 0 = 2
      omega
    · have hn : n / 4 < n := by omega
      have hqr : 4*(n/4)+n%4 = n := by omega
      simpa only [hqr] using nextDigit (n/4) (n%4) (by omega) (ih _ hn)

end A057300Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a057300.main :=
  A057300Proof.allCases
