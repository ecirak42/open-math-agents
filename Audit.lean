import Mathlib.Tactic.Ring
import Mathlib.Init

/-!
# OEIS A054516

Aleksandar Petojević's sequence begins at index 3. The defining
first-order recurrence below uses k = n - 3. Mathar conjectured
the displayed homogeneous recurrence on 31 January 2014. This target
concerns that recurrence; Kurepa's left factorial hypothesis is the
background of the sequence.

Source: https://oeis.org/A054516
Formalization: @ecirak42.
-/

namespace OMA.S_oeis_a054516

/-- The value at OEIS index k+3, with the recurrence evaluated in ℤ. -/
def fromThree : ℕ → ℤ
  | 0 => 0
  | k + 1 => -((k : ℤ) + 1) * fromThree k + ((k : ℤ) + 1) * ((k : ℤ) + 2)

/-- All indices for which the three terms in Mathar's recurrence are defined. -/
theorem main : ∀ k : ℕ,
    let n := (k : ℤ) + 5
    (4 - n) * fromThree (k + 2) + (-(n ^ 2) + 8 * n - 14) * fromThree (k + 1) +
      (n - 2) * (n - 4) * fromThree k = 0 := by
  sorry

end OMA.S_oeis_a054516


open OMA.S_oeis_a054516

theorem OMA.solution : type_of% @OMA.S_oeis_a054516.main := by
  intro k
  dsimp only
  simp only [fromThree, Nat.cast_succ]
  ring

#print axioms OMA.solution
