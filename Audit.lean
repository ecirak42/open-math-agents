
import Mathlib

/-!
# A183003: a(n) = A183002(n)/2.

Source: https://oeis.org/A183003
Credit: @marcelopierry

Conjecture (Sean A. Irvine, Jul 14 2022, in the comments of A183003): partial sums of A072670.

Conventions:
* A161840(n), the number of noncentral divisors of n, is tau(n) - 2 + (tau(n) mod 2) (the
  formula given in A161840 and A183002), where tau(n) is the number of divisors of n. For n >= 1
  the value is a natural number (tau(1) = 1 gives 0).
* A183002(n) = Sum_{k=1..n} A161840(k), the total number of noncentral divisors of 1, ..., n
  (offset 1), and A183003(n) = A183002(n)/2 (offset 1; data 0, 0, 0, 1, 1, 2, 2, 3, 4, 5, ...).
* A072670(m) (offset 0) is the number of ways to write m as i*j + i + j with 0 < i <= j; such
  i, j are at most m, so they are counted inside {1, ..., m} x {1, ..., m}
  (data 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 2, ...).
* Matching the offsets as in the data, the partial sums are A183003(n) = A072670(0) + ... +
  A072670(n-1) for n >= 1.
-/

namespace OMA.S_oeis_a183003

/-- A161840(n) = tau(n) - 2 + (tau(n) mod 2). -/
def A161840 (n : ℕ) : ℕ := n.divisors.card + n.divisors.card % 2 - 2

/-- A183002(n) = Sum_{k=1..n} A161840(k). -/
def A183002 (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, A161840 k

/-- A183003(n) = A183002(n)/2. -/
def a (n : ℕ) : ℕ := A183002 n / 2

/-- A072670(m): the number of ways to write m = i*j + i + j with 0 < i <= j. -/
def A072670 (m : ℕ) : ℕ :=
  ((Finset.Icc 1 m ×ˢ Finset.Icc 1 m).filter (fun p => p.1 ≤ p.2 ∧ p.1 * p.2 + p.1 + p.2 = m)).card

/-- Irvine's conjecture: A183003 is the partial sums of A072670. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = ∑ m ∈ Finset.range n, A072670 m := by
  sorry

end OMA.S_oeis_a183003


/-!
Adding one to each entry of (i,j) gives a nontrivial unordered factor pair
of m+1, as noted by Daniel Forgues in A072670 (2011). The fixed point of
factor exchange contributes the divisor-count parity term. This proves
Sean A. Irvine's partial-sums conjecture for the statement by @marcelopierry.
-/

namespace NoncentralDivisors
open Finset OMA.S_oeis_a183003

private def upper (m : ℕ) :=
  (m + 1).divisorsAntidiagonal.filter (fun p => p.1 ≤ p.2)

private theorem mainPair (m : ℕ) : (1, m + 1) ∈ upper m := by
  simp [upper, Nat.mem_divisorsAntidiagonal]

private theorem nontrivial (m : ℕ) :
    A072670 m = ((upper m).erase (1, m+1)).card := by
  apply Finset.card_bij' (fun (p : ℕ × ℕ) _ => (p.1+1,p.2+1))
    (fun (p : ℕ × ℕ) _ => (p.1-1,p.2-1))
  · rintro ⟨i,j⟩ hp
    simp only [mem_filter, mem_product, mem_Icc] at hp
    obtain ⟨⟨⟨hi, _⟩, _⟩, hij, h⟩ := hp
    simp only [mem_erase, upper, mem_filter, Nat.mem_divisorsAntidiagonal,
      Prod.mk.injEq, Nat.add_one_ne_zero, ne_eq, not_false_eq_true, and_true]
    exact ⟨by omega, by nlinarith, by omega⟩
  · rintro ⟨i,j⟩ hp
    simp only [mem_erase, upper, mem_filter, Nat.mem_divisorsAntidiagonal,
      Prod.mk.injEq] at hp
    obtain ⟨hne, ⟨hprod, _⟩, hij⟩ := hp
    have hi : 2 ≤ i := by
      by_contra! h
      interval_cases i <;> simp_all
    have hj : 2 ≤ j := by omega
    have hjm : j ≤ m + 1 := by nlinarith
    have hterm : (i-1)*(j-1)+(i-1)+(j-1) = m := by
      have hi' : i = i-1+1 := by omega
      have hj' : j = j-1+1 := by omega
      conv_lhs at hprod => rw [hi', hj']
      nlinarith
    simp only [mem_filter, mem_product, mem_Icc]
    exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, by omega, hterm⟩
  · rintro ⟨i,j⟩ _
    simp
  · rintro ⟨i,j⟩ hp
    have hmem := (mem_filter.mp (mem_erase.mp hp).2).1
    have hi := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hmem
    have hj := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hmem
    apply Prod.ext <;> dsimp at * <;> omega

private theorem pairs (m : ℕ) : A161840 (m+1) = 2 * A072670 m := by
  let D := (m+1).divisorsAntidiagonal
  let L := D.filter (fun p => p.1 < p.2)
  let E := D.filter (fun p => p.1 = p.2)
  let G := D.filter (fun p => p.2 < p.1)
  have hD : D.card = (m+1).divisors.card := by
    dsimp [D]
    rw [← Nat.map_div_right_divisors, Finset.card_map]
  have hswap : G.card = L.card := by
    apply Finset.card_bij' (fun p _ => p.swap) (fun p _ => p.swap)
    · intro p hp
      exact mem_filter.mpr ⟨Nat.swap_mem_divisorsAntidiagonal.mpr (mem_filter.mp hp).1,
        (mem_filter.mp hp).2⟩
    · intro p hp
      exact mem_filter.mpr ⟨Nat.swap_mem_divisorsAntidiagonal.mpr (mem_filter.mp hp).1,
        (mem_filter.mp hp).2⟩
    · intros; rfl
    · intros; rfl
  have he : E.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    rintro ⟨a,b⟩ hp ⟨c,d⟩ hq
    obtain ⟨h1, rfl⟩ := mem_filter.mp hp
    obtain ⟨h2, rfl⟩ := mem_filter.mp hq
    have hh := (Nat.mem_divisorsAntidiagonal.mp h1).1
    have hk := (Nat.mem_divisorsAntidiagonal.mp h2).1
    have : a = c := by dsimp at hh hk; nlinarith
    simp [this]
  have hu : (upper m).card + G.card = D.card := by
    simpa [upper, G, D, not_le] using card_filter_add_card_filter_not
      (s := D) (p := fun p : ℕ × ℕ => p.1 ≤ p.2)
  have hul : L.card + E.card = (upper m).card := by
    have t := card_filter_add_card_filter_not (s := upper m)
      (p := fun p : ℕ × ℕ => p.1 < p.2)
    convert t using 2
    · congr 1
      ext p
      simp [L, D, upper]
      omega
    · congr 1
      ext p
      simp [E, D, upper]
      omega
  have hn := card_erase_add_one (mainPair m)
  rw [← nontrivial] at hn
  unfold A161840
  omega

private theorem sumPairs (n : ℕ) :
    A183002 n = 2 * ∑ m ∈ range n, A072670 m := by
  induction n with
  | zero => simp [A183002]
  | succ n ih =>
    unfold A183002 at ih ⊢
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n+1), sum_range_succ, ih, pairs]
    ring

end NoncentralDivisors

theorem OMA.solution : type_of% @OMA.S_oeis_a183003.main := by
  intro n _
  unfold OMA.S_oeis_a183003.a
  rw [NoncentralDivisors.sumPairs]
  omega

#print axioms OMA.solution
