import Mathlib.Tactic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic

/-!
# OEIS A386969

Jules Beauchamp's Recamán variant starts at zero. Subtract the new index
when the difference is nonnegative and has never occurred, otherwise add
the new index and three. Bill McEachen conjectures explicit formulas for
odd and even indices from index three on. Zhuorui He conjectures the
ordinary generating function x(4+2x+11x³−2x⁴−9x⁵)/(1−x²)².

The second conclusion equates the integer coefficients after multiplying
by (1−x²)². The two parity cases in the first conclusion also give
McEachen's equivalent expression using (−1)^n.

Source: https://oeis.org/A386969
Formalization: @ecirak42.
-/

namespace OMA.S_oeis_a386969

def nextValue (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  if n + 1 ≤ a n ∧ ∀ i : Fin (n + 1), a i ≠ a n - (n + 1) then
    a n - (n + 1)
  else a n + (n + 1) + 3

def lag (a : ℕ → ℕ) (n k : ℕ) : ℤ :=
  if k ≤ n then (a (n - k) : ℤ) else 0

def numerator : ℕ → ℤ
  | 1 => 4
  | 2 => 2
  | 4 => 11
  | 5 => -2
  | 6 => -9
  | _ => 0

theorem main : ∀ a : ℕ → ℕ, a 0 = 0 → (∀ n, a (n + 1) = nextValue a n) →
    (∀ n, 3 ≤ n → a n = if n % 2 = 0 then 2*n + 7 else n + 5) ∧
    (∀ n, (a n : ℤ) - 2 * lag a n 2 + lag a n 4 = numerator n) := by
  sorry

end OMA.S_oeis_a386969


namespace Recaman386969
open OMA.S_oeis_a386969

private def f (n : ℕ) : ℕ :=
  if n = 0 then 0 else if n = 1 then 4 else if n = 2 then 2
  else if n % 2 = 0 then 2*n + 7 else n + 5

private theorem tail (n : ℕ) (hn : 3 ≤ n) :
    f n = if n % 2 = 0 then 2*n + 7 else n + 5 := by
  simp [f, show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega]

private theorem follows (n : ℕ) : f (n+1) = nextValue f n := by
  by_cases hn : n < 3
  · interval_cases n <;> decide
  by_cases he : n % 2 = 0
  · have hf : f n = 2*n + 7 := by simp [tail n (by omega), he]
    have fresh : ∀ i : Fin (n+1), f i ≠ f n - (n+1) := by
      intro i
      have hi := i.isLt
      rw [hf]
      unfold f
      split_ifs <;> omega
    rw [nextValue, if_pos ⟨by omega, fresh⟩, hf, tail (n+1) (by omega)]
    split_ifs <;> omega
  · have hf : f n = n + 5 := by simp [tail n (by omega), he]
    have used : ¬ (n+1 ≤ f n ∧ ∀ i : Fin (n+1), f i ≠ f n - (n+1)) := by
      rintro ⟨_, h⟩
      have h1 := h ⟨1, by omega⟩
      change 4 ≠ f n - (n+1) at h1
      omega
    rw [nextValue, if_neg used, hf, tail (n+1) (by omega)]
    split_ifs <;> omega

private theorem unique (a : ℕ → ℕ) (h0 : a 0 = 0)
    (ha : ∀ n, a (n+1) = nextValue a n) : a = f := by
  funext n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => exact h0
    | succ n =>
      have hp := ih n (Nat.lt_succ_self n)
      have hmem : (∀ i : Fin (n+1), a i ≠ a n - (n+1)) ↔
          (∀ i : Fin (n+1), f i ≠ f n - (n+1)) := by
        apply forall_congr'
        intro i
        rw [hp, ih i i.isLt]
      rw [ha, follows]
      simp only [nextValue, hmem, hp]

private theorem generating (n : ℕ) :
    (f n : ℤ) - 2 * lag f n 2 + lag f n 4 = numerator n := by
  by_cases hn : n < 7
  · interval_cases n <;> decide
  have hnum : numerator n = 0 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n-7, by omega⟩
    rfl
  rw [hnum]
  simp only [lag, if_pos (show 2 ≤ n by omega), if_pos (show 4 ≤ n by omega),
    tail n (by omega), tail (n-2) (by omega), tail (n-4) (by omega)]
  split_ifs <;> omega

end Recaman386969

theorem OMA.solution : type_of% @OMA.S_oeis_a386969.main := by
  intro a h0 ha
  rw [Recaman386969.unique a h0 ha]
  exact ⟨Recaman386969.tail, Recaman386969.generating⟩

#print axioms OMA.solution
