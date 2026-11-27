import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Tactic
import Mathlib

/-!
# A174349: Square array: row n gives the indices i for which prime(i+1) = prime(i) + 2n; read by falling antidiagonals.

Source: https://oeis.org/A174349
Credit: @max-otc

Row n (n ≥ 1) of the array lists the indices i ≥ 1 with prime(i+1) = prime(i) + 2n, where prime(i) is the
i-th prime (prime(1) = 2, OEIS indexing; here prime(i) = Nat.nth Nat.Prime (i - 1)).
Statement: every positive integer except 1 occurs in the array, i.e. a positive integer i lies in some
row n ≥ 1 exactly when i ≠ 1. (M. F. Hasler, Oct 19 2018, notes that i appears in row
(prime(i+1) - prime(i))/2. The remark on Polignac's conjecture, that every row is infinite, is not part of
this statement.)
-/

namespace OMA.S_oeis_a174349

/-- The i-th prime, 1-indexed: prime 1 = 2, prime 2 = 3, prime 3 = 5, ... -/
noncomputable def prime (i : ℕ) : ℕ := Nat.nth Nat.Prime (i - 1)

/-- Row n of A174349: the indices i ≥ 1 with prime(i+1) = prime(i) + 2n. -/
def row (n : ℕ) : Set ℕ := {i | 1 ≤ i ∧ prime (i + 1) = prime i + 2 * n}

/-- Every positive integer except 1 occurs in some row n ≥ 1 of the array. -/
theorem main : ∀ i : ℕ, 1 ≤ i → ((∃ n : ℕ, 1 ≤ n ∧ i ∈ row n) ↔ i ≠ 1) := by
  sorry

end OMA.S_oeis_a174349


/-!
M. F. Hasler observed in 2018 that the relevant row is half the gap
between two consecutive odd primes. Statement formalization by @max-otc.
-/

open OMA.S_oeis_a174349

theorem OMA.solution : type_of% @OMA.S_oeis_a174349.main := by
  intro i hi
  constructor
  · rintro ⟨n, hn, _, h⟩ rfl
    have h1 : prime 1 = 2 := Nat.nth_prime_zero_eq_two
    have h2 : prime (1 + 1) = 3 := Nat.nth_prime_one_eq_three
    omega
  · intro hne
    have mono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
    have hlt : prime i < prime (i + 1) := mono (show i - 1 < i + 1 - 1 by omega)
    have htwo : 2 < prime i := by
      rw [← Nat.nth_prime_zero_eq_two]
      exact mono (show 0 < i - 1 by omega)
    have hpi : Nat.Prime (prime i) := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _
    have hpj : Nat.Prime (prime (i + 1)) := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _
    obtain ⟨x, hx⟩ := hpi.odd_of_ne_two (by omega)
    obtain ⟨y, hy⟩ := hpj.odd_of_ne_two (by omega)
    exact ⟨y - x, by omega, hi, by omega⟩

#print axioms OMA.solution
