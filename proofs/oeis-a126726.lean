import OMAStatements.S_oeis_a126726

/-!
# Counterexample to the conjecture in A126726

The only two-digit binary integers are 2 and 3, neither of which is a
square. The integer square roots of 4 and 8 both equal 2. At n = 2 the
proposed equality therefore reads 0 = -1.
-/

open OMA.S_oeis_a126726

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a126726.main) := by
  intro h
  have hs : squareCount 2 = 0 := by decide
  have h4 : 2 = Nat.sqrt 4 := Nat.eq_sqrt.mpr (by decide)
  have h8 : 2 = Nat.sqrt 8 := Nat.eq_sqrt.mpr (by decide)
  have hb : betweenPowers 2 = 0 := by
    change Nat.sqrt 8 - Nat.sqrt 4 = 0
    rw [← h8, ← h4]
  have hh := h 2 (by decide)
  rw [hs, hb] at hh
  exact (by decide : ¬ ((0 : Int) = (0 : Int) - (-1 : Int) ^ 2)) hh
