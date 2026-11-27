import OMAStatements.S_oeis_a174349
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Tactic

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
    have mono := Nat.nth_strictMono Nat.infinite_setOf_prime
    have hlt : prime i < prime (i + 1) := mono (show i - 1 < i + 1 - 1 by omega)
    have htwo : 2 < prime i := by
      rw [← Nat.nth_prime_zero_eq_two]
      exact mono (show 0 < i - 1 by omega)
    have hpi : Nat.Prime (prime i) := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime _
    have hpj : Nat.Prime (prime (i + 1)) := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime _
    obtain ⟨x, hx⟩ := hpi.odd_of_ne_two (by omega)
    obtain ⟨y, hy⟩ := hpj.odd_of_ne_two (by omega)
    exact ⟨y - x, by omega, hi, by omega⟩
