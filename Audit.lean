import Mathlib.Tactic.Ring
import Mathlib.Init

/-!
# OEIS A056158

The sequence starts at a(3) = -4 and satisfies
a(n) = -(n-3) a(n-1) - 2(n-1). R. J. Mathar's conjecture of
31 January 2014 is a homogeneous recurrence involving four terms.
All coefficients and terms below are integers.

Source: https://oeis.org/A056158
Formalization: @ecirak42.
-/

namespace OMA.S_oeis_a056158

/-- Value at index k+3 in the original sequence. -/
def fromThree : ℕ → ℤ
  | 0 => -4
  | k + 1 => -((k : ℤ) + 1) * fromThree k - 2 * ((k : ℤ) + 3)

/-- The smallest eligible n is 6, so n = k+6 covers every case. -/
theorem main : ∀ k : ℕ,
    let n := (k : ℤ) + 6
    fromThree (k + 3) + (n - 5) * fromThree (k + 2) +
      (-2 * n + 9) * fromThree (k + 1) + (n - 5) * fromThree k = 0 := by
  sorry

end OMA.S_oeis_a056158


open OMA.S_oeis_a056158

theorem OMA.solution : type_of% @OMA.S_oeis_a056158.main := by
  intro k
  dsimp only
  simp only [fromThree, Nat.cast_succ]
  ring

#print axioms OMA.solution
