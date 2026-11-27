import OMAStatements.S_oeis_a183003

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
