import OMAStatements.S_oeis_a392943
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
Ronald van Luijk's The diameter of the circumcircle of a Heron triangle,
Theorem 2, implies the stated obstruction. Here the elementary parity
argument is formalized directly.
-/

namespace HeronianParity
open OMA.S_oeis_a392943

private theorem square_mod (t : ℤ) : t ^ 2 % 4 = 0 ∨ t ^ 2 % 4 = 1 := by
  rw [sq, Int.mul_emod]
  have hl := Int.emod_nonneg t (by decide : (4 : ℤ) ≠ 0)
  have hu := Int.emod_lt_of_pos t (by decide : (0 : ℤ) < 4)
  interval_cases t % 4 <;> decide

private theorem evenSide (a b c K R : ℕ) (hb : 0 < b) (hc : 0 < c)
    (hH : hasArea a b c K) (hR : 4 * R * K = a * b * c) : 2 ∣ a := by
  let z : ℤ := (2 * (R : ℤ)) ^ 2 - (a : ℤ) ^ 2
  have hs : IsSquare (z : ℚ) := by
    have hHq : (4 * (K : ℚ)) ^ 2 =
        (a + b + (c : ℚ)) * (-a + b + (c : ℚ)) * (a - b + (c : ℚ)) * (a + b - (c : ℚ)) := by
      unfold hasArea at hH
      exact_mod_cast hH
    have hRq : 4 * (R : ℚ) * K = a * b * (c : ℚ) := by exact_mod_cast hR
    refine ⟨(R : ℚ) * (b ^ 2 + c ^ 2 - (a : ℚ) ^ 2) / (b * c), ?_⟩
    dsimp [z]
    push_cast
    field_simp
    linear_combination -(R : ℚ)^2 * hHq + (4 * R * K + a * b * (c : ℚ)) * hRq
  obtain ⟨t, ht⟩ := Rat.isSquare_intCast_iff.mp hs
  have he : (a : ℤ) ^ 2 + t ^ 2 = 4 * (R : ℤ) ^ 2 := by
    dsimp [z] at ht
    linear_combination -ht
  have hm := congrArg (fun x : ℤ => x % 4) he
  simp only [Int.add_emod, Int.mul_emod_right] at hm
  have ha := square_mod (a : ℤ)
  have ht' := square_mod t
  have h0 : (a : ℤ) ^ 2 % 4 = 0 := by omega
  by_contra hn
  have hodd : Odd (a : ℤ) := by
    refine ⟨(a / 2 : ℕ), ?_⟩
    omega
  obtain ⟨s, hs⟩ := hodd
  rw [hs, show (2 * s + 1)^2 = 4 * (s^2 + s) + 1 by ring] at h0
  omega

end HeronianParity

theorem OMA.solution : type_of% @OMA.S_oeis_a392943.main := by
  rintro ⟨a, b, c, K, R, ha, hb, hc, _, _, _, hg, _, hH, _, hR⟩
  have e1 := HeronianParity.evenSide a b c K R hb hc hH hR
  have e2 := HeronianParity.evenSide b c a K R hc ha (by
    unfold OMA.S_oeis_a392943.hasArea at hH ⊢
    linear_combination hH) (by simpa [mul_comm, mul_left_comm, mul_assoc] using hR)
  have e3 := HeronianParity.evenSide c a b K R ha hb (by
    unfold OMA.S_oeis_a392943.hasArea at hH ⊢
    linear_combination hH) (by simpa [mul_comm, mul_left_comm, mul_assoc] using hR)
  have h2 := Nat.dvd_gcd (Nat.dvd_gcd e1 e2) e3
  rw [hg] at h2
  omega
