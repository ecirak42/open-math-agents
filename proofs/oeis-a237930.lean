import OMAStatements.S_oeis_a237930
import Mathlib.Tactic.NormNum.LegendreSymbol

/-! A proof of Klaus Purath's A237930 conjecture, using the periodicity
of the Jacobi symbol in its denominator at odd arguments. -/

namespace A237930Proof

open OMA.S_oeis_a237930

def forbidden (r : ℕ) : Prop :=
  r = 11 ∨ r = 13 ∨ r = 23 ∨ r = 61 ∨ r = 71 ∨ r = 73

private theorem twice_term_add_one (n : ℕ) : 2 * a n + 1 = 7 * 3 ^ n := by
  obtain ⟨k, hk⟩ := (show Odd (3 : ℕ) by decide).pow (n := n)
  simp only [a, pow_succ, hk]
  omega

private theorem symbols {p : ℕ} (h : forbidden (p % 84)) :
    jacobiSym 3 p = 1 ∧ jacobiSym 7 p = -1 := by
  have h₂ : p % 2 = 1 := by
    rw [← Nat.mod_mod_of_dvd p (show 2 ∣ 84 by decide)]
    rcases h with hr | hr | hr | hr | hr | hr <;> rw [hr]
  have ho : Odd p := by
    use p / 2
    omega
  have mod3 := jacobiSym.mod_right' 3 ho
  have mod7 := jacobiSym.mod_right' 7 ho
  norm_num at mod3 mod7
  rw [mod3, mod7]
  change jacobiSym 3 (p % 12) = 1 ∧ jacobiSym 7 (p % 28) = -1
  rw [← Nat.mod_mod_of_dvd p (show 12 ∣ 84 by decide),
      ← Nat.mod_mod_of_dvd p (show 28 ∣ 84 by decide)]
  rcases h with hr | hr | hr | hr | hr | hr <;> rw [hr] <;> norm_num

/-- The contradiction works for every divisor in the six classes, in particular for primes. -/
theorem excludes_divisor (n d : ℕ) (hd : d ∣ a n) : ¬ forbidden (d % 84) := by
  intro h
  obtain ⟨h₃, h₇⟩ := symbols h
  obtain ⟨k, hk⟩ := hd
  have hi : (2 : ℤ) * (↑(a n) : ℤ) + 1 = 7 * 3 ^ n := by
    exact_mod_cast twice_term_add_one n
  rw [hk, Nat.cast_mul] at hi
  have he : (7 : ℤ) * 3 ^ n = 1 + (2 * (k : ℤ)) * (d : ℤ) := by
    rw [← hi]
    ring
  have hj : jacobiSym ((7 : ℤ) * 3 ^ n) d = jacobiSym 1 d := by
    apply jacobiSym.mod_left'
    rw [he]
    simp
  rw [jacobiSym.mul_left, jacobiSym.pow_left, h₃, h₇, jacobiSym.one_left] at hj
  norm_num at hj

end A237930Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a237930.main := by
  intro n p _hp hd
  simpa [A237930Proof.forbidden] using A237930Proof.excludes_divisor n p hd
