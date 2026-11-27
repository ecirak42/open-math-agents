import OMAStatements.S_oeis_a202440
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# A202440

The fourth differences of the individual suffix counts can oscillate.
Their sums at consecutive indices vanish in every state. The transfer
operator preserves this identity. The first fourth difference of the
total is zero, so every subsequent fourth difference of the total is zero.
-/

namespace OMA.S_oeis_a202440

private def rows : Nat → Array Int
  | 0 => #[1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1]
  | 1 => #[1, 2, 2, 0, 0, 2, 3, 6, 2, 1, 0, 0, 0, 2, 3, 2, 2, 3, 1, 0, 0, 3, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2, 3, 0, 0, 1, 3, 2, 2, 3, 2, 0, 0, 0, 1, 2, 6, 3, 2, 0, 0, 2, 2, 1]
  | 2 => #[1, 3, 3, 0, 0, 5, 5, 16, 3, 1, 0, 0, 0, 3, 3, 3, 3, 3, 1, 0, 0, 8, 3, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 3, 8, 0, 0, 1, 3, 3, 3, 3, 3, 0, 0, 0, 1, 3, 16, 5, 5, 0, 0, 3, 3, 1]
  | 3 => #[1, 4, 4, 0, 0, 8, 7, 33, 4, 1, 0, 0, 0, 4, 4, 4, 4, 4, 1, 0, 0, 16, 4, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 4, 16, 0, 0, 1, 4, 4, 4, 4, 4, 0, 0, 0, 1, 4, 33, 7, 8, 0, 0, 4, 4, 1]
  | 4 => #[1, 5, 5, 0, 0, 13, 9, 57, 5, 1, 0, 0, 0, 5, 5, 5, 5, 5, 1, 0, 0, 29, 5, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 5, 29, 0, 0, 1, 5, 5, 5, 5, 5, 0, 0, 0, 1, 5, 57, 9, 13, 0, 0, 5, 5, 1]
  | 5 => #[1, 6, 6, 0, 0, 18, 11, 90, 6, 1, 0, 0, 0, 6, 6, 6, 6, 6, 1, 0, 0, 47, 6, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 6, 47, 0, 0, 1, 6, 6, 6, 6, 6, 0, 0, 0, 1, 6, 90, 11, 18, 0, 0, 6, 6, 1]
  | 6 => #[1, 7, 7, 0, 0, 25, 13, 132, 7, 1, 0, 0, 0, 7, 7, 7, 7, 7, 1, 0, 0, 72, 7, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 7, 72, 0, 0, 1, 7, 7, 7, 7, 7, 0, 0, 0, 1, 7, 132, 13, 25, 0, 0, 7, 7, 1]
  | 7 => #[1, 8, 8, 0, 0, 32, 15, 185, 8, 1, 0, 0, 0, 8, 8, 8, 8, 8, 1, 0, 0, 104, 8, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 8, 104, 0, 0, 1, 8, 8, 8, 8, 8, 0, 0, 0, 1, 8, 185, 15, 32, 0, 0, 8, 8, 1]
  | _ => #[]

private def entry (n : Nat) (s : Fin 64) : Int := (rows n)[s.val]?.getD 0

set_option maxRecDepth 8192 in
private theorem firstRow : ∀ s : Fin 64, count 0 s = entry 0 s := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 14000000 in
private theorem transitions : ∀ n : Fin 7, ∀ s : Fin 64,
    step (entry n.val) s = entry (n.val+1) s := by decide

private theorem prefixRows (n : Nat) (hn : n ≤ 7) : count n = entry n := by
  induction n with
  | zero => exact funext firstRow
  | succ n ih =>
    change step (count n) = entry (n+1)
    rw [ih (by omega)]
    exact funext (transitions ⟨n, by omega⟩)

private def paired (f : Nat → Int) := fourth f + fourth (fun j => f (j+1))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem firstPairs : ∀ s : Fin 64,
    paired (fun k => entry (k+2) s) = 0 := by decide

private theorem firstPair (s : Fin 64) : paired (fun k => count (k+2) s) = 0 := by
  have e : (fun k => count (min (k+2) 7) s) = (fun k => entry (min (k+2) 7) s) := by
    funext k
    rw [prefixRows _ (Nat.min_le_right _ _)]
  exact (congrArg paired e).trans (firstPairs s)

private theorem pairedSum {ι : Type} (S : Finset ι) (f : ι → Nat → Int) :
    paired (fun j => ∑ i ∈ S, f i j) = ∑ i ∈ S, paired (f i) := by
  simp only [paired, fourth, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

private theorem propagate (f : Nat → Fin 64 → Int)
    (h : ∀ s, paired (fun j => f j s) = 0) (s : Fin 64) :
    paired (fun j => step (f j) s) = 0 := by
  unfold step
  rw [pairedSum]
  exact Finset.sum_eq_zero (fun c _ => h (nextPair s c))

private theorem allPairs (n : Nat) (s : Fin 64) :
    paired (fun j => count (n+(j+2)) s) = 0 := by
  induction n generalizing s with
  | zero => simpa only [Nat.zero_add] using firstPair s
  | succ n ih => exact propagate (fun j => count (n+(j+2))) ih s

private theorem totalPair (n : Nat) : paired (fun j => total (n+(j+2))) = 0 := by
  unfold total
  rw [pairedSum]
  exact Finset.sum_eq_zero (fun s _ => allPairs n s)

private def totals : Array Int := #[36, 80, 138, 224, 338, 484, 666, 888]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem tableTotals : ∀ k : Fin 8,
    (∑ s : Fin 64, entry k.val s) = totals[k.val]?.getD 0 := by decide

private theorem totalKnown (n : Nat) (h : n ≤ 7) : total n = totals[n]?.getD 0 := by
  unfold total
  rw [prefixRows n h]
  exact tableTotals ⟨n, by omega⟩

private theorem recurrence (n : Nat) : fourth (fun j => total (n+(j+2))) = 0 := by
  induction n with
  | zero =>
    change total 6 - 4*total 5 + 6*total 4 - 4*total 3 + total 2 = 0
    rw [totalKnown 6 (by decide), totalKnown 5 (by decide), totalKnown 4 (by decide),
      totalKnown 3 (by decide), totalKnown 2 (by decide)]
    decide
  | succ n ih =>
    have h := totalPair n
    unfold paired at h
    rw [ih, Int.zero_add] at h
    exact h

private theorem series (n : Nat) : productCoeff n = numerator n := by
  match n with
  | 0 => rfl
  | 1 | 2 | 3 | 4 | 5 =>
    simp only [productCoeff, fourth, a, numerator, Nat.zero_add]
    repeat first
      | rw [totalKnown 1 (by decide)] | rw [totalKnown 2 (by decide)]
      | rw [totalKnown 3 (by decide)] | rw [totalKnown 4 (by decide)]
      | rw [totalKnown 5 (by decide)]
    decide
  | k+6 => exact recurrence k

end OMA.S_oeis_a202440

open OMA.S_oeis_a202440

theorem OMA.solution : type_of% @OMA.S_oeis_a202440.main :=
  ⟨recurrence, series⟩
