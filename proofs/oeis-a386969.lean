import OMAStatements.S_oeis_a386969
import Mathlib.Tactic

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
    have good : n+1 ≤ f n ∧ ∀ i : Fin (n+1), f i ≠ f n - (n+1) := ⟨by omega, fresh⟩
    unfold nextValue
    split
    · rw [hf, tail (n+1) (by omega)]
      split_ifs <;> omega
    · contradiction
  · have hf : f n = n + 5 := by simp [tail n (by omega), he]
    have used : ¬ (n+1 ≤ f n ∧ ∀ i : Fin (n+1), f i ≠ f n - (n+1)) := by
      rintro ⟨_, h⟩
      have h1 := h ⟨1, by omega⟩
      change 4 ≠ f n - (n+1) at h1
      omega
    simp only [nextValue, used, ↓reduceIte]
    rw [hf, tail (n+1) (by omega)]
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
      rw [hp] at hmem
      simp only [nextValue, hp, hmem]

private theorem generating (n : ℕ) :
    (f n : ℤ) - 2 * lag f n 2 + lag f n 4 = numerator n := by
  by_cases hn : n < 7
  · interval_cases n <;> decide
  have hnum : numerator n = 0 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n-7, by omega⟩
    rfl
  rw [hnum]
  simp only [lag, show 2 ≤ n by omega, show 4 ≤ n by omega, ↓reduceIte,
    tail n (by omega), tail (n-2) (by omega), tail (n-4) (by omega)]
  split_ifs <;> omega

end Recaman386969

theorem OMA.solution : type_of% @OMA.S_oeis_a386969.main := by
  intro a h0 ha
  rw [Recaman386969.unique a h0 ha]
  exact ⟨Recaman386969.tail, Recaman386969.generating⟩
