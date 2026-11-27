import OMAStatements.S_oeis_a133552

/-!
# A transfer-matrix proof for OEIS A133552

The table records the first sixteen continuation-count vectors of the suffix
automaton, one entry per five-bit suffix. We verify every transition and
the recurrence on every suffix. Adding the allowed successors then propagates
the recurrence to all lengths. The initial numerator coefficients and the
same recurrence give the generating function.
-/

namespace OMA.S_oeis_a133552

private def rows : Nat → Array Int
  | 0 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0]
  | 1 => #[2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 1, 0]
  | 2 => #[4, 4, 4, 4, 4, 4, 4, 3, 4, 4, 4, 3, 4, 3, 3, 1, 4, 4, 4, 4, 4, 4, 4, 2, 4, 4, 4, 2, 4, 2, 2, 0]
  | 3 => #[8, 8, 8, 7, 8, 7, 7, 4, 8, 8, 8, 6, 8, 6, 6, 2, 8, 8, 8, 7, 8, 7, 7, 3, 8, 8, 8, 4, 8, 4, 4, 0]
  | 4 => #[16, 15, 15, 11, 16, 14, 14, 8, 16, 15, 15, 10, 16, 12, 12, 4, 16, 15, 15, 11, 16, 14, 14, 6, 16, 15, 15, 7, 16, 8, 8, 0]
  | 5 => #[31, 26, 30, 22, 31, 25, 28, 16, 31, 26, 30, 20, 31, 22, 24, 8, 31, 26, 30, 22, 31, 25, 28, 12, 31, 26, 30, 14, 31, 15, 16, 0]
  | 6 => #[57, 52, 56, 44, 57, 50, 53, 32, 57, 52, 56, 40, 57, 44, 46, 16, 57, 52, 56, 44, 57, 50, 53, 24, 57, 52, 56, 28, 57, 30, 31, 0]
  | 7 => #[109, 100, 107, 85, 109, 96, 101, 62, 109, 100, 107, 77, 109, 84, 87, 31, 109, 100, 107, 85, 109, 96, 101, 46, 109, 100, 107, 53, 109, 56, 57, 0]
  | 8 => #[209, 192, 205, 163, 209, 184, 193, 118, 209, 192, 205, 147, 209, 160, 165, 57, 209, 192, 205, 163, 209, 184, 193, 87, 209, 192, 205, 101, 209, 107, 109, 0]
  | 9 => #[401, 368, 393, 311, 401, 352, 369, 222, 401, 368, 393, 280, 401, 306, 316, 109, 401, 368, 393, 311, 401, 352, 369, 165, 401, 368, 393, 193, 401, 205, 209, 0]
  | 10 => #[769, 704, 753, 591, 769, 673, 707, 425, 769, 704, 753, 534, 769, 586, 606, 209, 769, 704, 753, 591, 769, 673, 707, 316, 769, 704, 753, 369, 769, 393, 401, 0]
  | 11 => #[1473, 1344, 1442, 1132, 1473, 1287, 1355, 815, 1473, 1344, 1442, 1023, 1473, 1122, 1162, 401, 1473, 1344, 1442, 1132, 1473, 1287, 1355, 606, 1473, 1344, 1442, 707, 1473, 753, 769, 0]
  | 12 => #[2817, 2574, 2760, 2170, 2817, 2465, 2595, 1563, 2817, 2574, 2760, 1961, 2817, 2149, 2226, 769, 2817, 2574, 2760, 2170, 2817, 2465, 2595, 1162, 2817, 2574, 2760, 1355, 2817, 1442, 1473, 0]
  | 13 => #[5391, 4930, 5282, 4158, 5391, 4721, 4966, 2995, 5391, 4930, 5282, 3757, 5391, 4115, 4259, 1473, 5391, 4930, 5282, 4158, 5391, 4721, 4966, 2226, 5391, 4930, 5282, 2595, 5391, 2760, 2817, 0]
  | 14 => #[10321, 9440, 10112, 7961, 10321, 9039, 9506, 5732, 10321, 9440, 10112, 7192, 10321, 7877, 8151, 2817, 10321, 9440, 10112, 7961, 10321, 9039, 9506, 4259, 10321, 9440, 10112, 4966, 10321, 5282, 5391, 0]
  | 15 => #[19761, 18073, 19360, 15238, 19761, 17304, 18198, 10968, 19761, 18073, 19360, 13765, 19761, 15078, 15603, 5391, 19761, 18073, 19360, 15238, 19761, 17304, 18198, 8151, 19761, 18073, 19360, 9506, 19761, 10112, 10321, 0]
  | _ => #[]

private def entry (k : Nat) (s : Fin 32) : Int := (rows k)[s.val]?.getD 0

private theorem firstRow : ∀ s : Fin 32, count 0 s = entry 0 s := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem nextRows : ∀ k : Fin 15, ∀ s : Fin 32,
    step (entry k.val) s = entry (k.val + 1) s := by decide

private theorem countsAgree (k : Nat) (hk : k ≤ 15) : count k = entry k := by
  induction k with
  | zero => exact funext firstRow
  | succ k ih =>
    change step (count k) = entry (k + 1)
    rw [ih (by omega)]
    exact funext (nextRows ⟨k, by omega⟩)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem rowRecurrence : ∀ s : Fin 32,
    deviation (fun j => entry j s) = 0 := by decide

private theorem firstRecurrence (s : Fin 32) :
    deviation (fun k => count k s) = 0 := by
  have e : (fun k => count (min k 15) s) = (fun k => entry (min k 15) s) := by
    funext k
    rw [countsAgree _ (Nat.min_le_right _ _)]
  exact (congrArg deviation e).trans (rowRecurrence s)

private theorem propagate (f : Nat → Fin 32 → Int)
    (hf : ∀ s, deviation (fun k => f k s) = 0) (s : Fin 32) :
    deviation (fun k => step (f k) s) = 0 := by
  have hz := hf (shift s 0)
  have ho := hf (shift s 1)
  by_cases h₀ : weight s ≤ 4 <;> by_cases h₁ : weight s < 4 <;>
    simp [deviation, step, h₀, h₁] at * <;> omega

private theorem recurrence (n : Nat) (s : Fin 32) :
    deviation (fun k => count (n + k) s) = 0 := by
  induction n generalizing s with
  | zero => simpa only [Nat.zero_add] using firstRecurrence s
  | succ n ih => exact propagate (fun k => count (n + k)) ih s

private theorem coeffCongr (f g : Nat → Int) (p : List Int) (n : Nat)
    (h : ∀ k, k ≤ n → f k = g k) : productCoeff f p n = productCoeff g p n := by
  induction p generalizing n with
  | nil => rfl
  | cons c cs ih =>
    cases n with
    | zero => simp only [productCoeff, h 0 (by decide)]
    | succ n =>
      simp only [productCoeff, h (n+1) (Nat.le_refl _)]
      rw [ih n (fun k hk => h k (by omega))]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem firstCoeffs : ∀ k : Fin 15,
    productCoeff (fun j => entry j 0) denominator k.val = numeratorCoeff k.val := by decide

private theorem lastCoeff (f : Nat → Int) (c : Int) (n : Nat) :
    productCoeff f [c] n = c * f n := by
  cases n <;> simp [productCoeff]

private theorem series (n : Nat) :
    productCoeff a denominator n = numeratorCoeff n := by
  by_cases hn : n < 15
  · refine (coeffCongr a (fun j => entry j 0) denominator n ?_).trans (firstCoeffs ⟨n, hn⟩)
    intro k hk
    exact congrFun (countsAgree k (by omega)) 0
  · let k := n - 15
    have e : n = k + 15 := by omega
    rw [e]
    have hr := recurrence k 0
    simp [denominator, productCoeff, lastCoeff, numeratorCoeff, deviation, a, Nat.add_assoc] at *
    omega

end OMA.S_oeis_a133552

open OMA.S_oeis_a133552

theorem OMA.solution : type_of% @OMA.S_oeis_a133552.main :=
  ⟨fun n => recurrence n 0, series⟩
