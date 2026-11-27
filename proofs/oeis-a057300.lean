import Mathlib

/-!
# A057300 and Ralf Stephan's even and odd recurrences

The sequence swaps each neighboring pair of binary digits, counting positions
from the units digit. Equivalently, it swaps 1 and 2 in base 4 and leaves 0
and 3 fixed. Ralf Stephan conjectured the two recurrences on October 11, 2003.
Both equalities below move the negative term to the left, so that all
arithmetic takes place in the natural numbers.

Source: https://oeis.org/A057300
Credit: @ecirak42
-/

namespace OMA.S_oeis_a057300

/-- Reverse the two binary bits comprising one base-4 digit. -/
def swapDigit (d : ℕ) : ℕ := 2 * (d % 2) + d / 2

/-- Apply the digit swap to the base-4 expansion, starting at the units digit. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else 4 * a (n / 4) + swapDigit (n % 4)
termination_by n
decreasing_by omega

theorem main : ∀ n : ℕ,
    a (2 * n) + 2 * a n = 5 * n ∧
    a (2 * n + 1) + 2 * a n = 5 * n + 2 := by
  sorry

end OMA.S_oeis_a057300


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

private theorem appendBit (q r b : ℕ) (hr : r < 4) (hb : b < 2) :
    a (2*(4*q+r)+b) = 4*a (2*q+r/2) + swapDigit (2*(r%2)+b) := by
  rw [show 2*(4*q+r)+b = 4*(2*q+r/2)+(2*(r%2)+b) by omega]
  exact appendDigit _ _ (by omega)

private def Recurrences (n : ℕ) : Prop :=
  a (2*n) + 2*a n = 5*n ∧ a (2*n+1) + 2*a n = 5*n+2

private theorem nextDigit (q r : ℕ) (hr : r < 4) (hq : Recurrences q) :
    Recurrences (4*q+r) := by
  obtain ⟨heven, hodd⟩ := hq
  have ha := appendDigit q r hr
  have h0 := appendBit q r 0 hr (by decide)
  have h1 := appendBit q r 1 hr (by decide)
  unfold Recurrences
  interval_cases r <;> norm_num [swapDigit] at ha h0 h1 ⊢ <;> omega

theorem allCases (n : ℕ) : Recurrences n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n = 0
    · subst n
      norm_num [Recurrences, a, swapDigit]
    · have hn : n / 4 < n := by omega
      have hqr : 4*(n/4)+n%4 = n := by omega
      simpa only [hqr] using nextDigit (n/4) (n%4) (by omega) (ih _ hn)

end A057300Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a057300.main :=
  A057300Proof.allCases

#print axioms OMA.solution
