import OMAStatements.S_oeis_a068128
import Mathlib.Tactic

/-!
The positive triangular target 1 has precisely two examples: 1 and 10.
The classification of triangular powers of ten was given in 2016 by Ross
Millikan and Sarvesh Ravichandran Iyer on Mathematics Stack Exchange,
question 1997050.
-/

namespace TriangularDigitSum
open OMA.S_oeis_a068128

private theorem zeroDigits (l : List ℕ) (h : l.sum = 0) : Nat.ofDigits 10 l = 0 := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    rw [List.sum_cons] at h
    rw [Nat.ofDigits_cons, ih (by omega)]
    omega

private theorem oneDigit (l : List ℕ) (h : l.sum = 1) : ∃ e : ℕ, Nat.ofDigits 10 l = 10^e := by
  induction l with
  | nil => simp at h
  | cons d l ih =>
    rw [List.sum_cons] at h
    rw [Nat.ofDigits_cons]
    by_cases hd : d = 0
    · obtain ⟨e, he⟩ := ih (by omega)
      exact ⟨e + 1, by rw [hd, he, pow_succ']; simp⟩
    · exact ⟨0, by rw [zeroDigits l (by omega)]; omega⟩

private theorem twice (k : ℕ) : 2 * triangular k = k * (k + 1) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h : triangular (k + 1) = (k + 1) + triangular k := by
      simpa only [triangular, Nat.choose_one_right] using Nat.choose_succ_succ (k + 1) 1
    rw [h]
    nlinarith

private theorem gap (e : ℕ) : 2^(e + 3) + 1 < 5^(e + 2) := by
  induction e with
  | zero => decide
  | succ e ih =>
    rw [pow_succ 2 (e + 3), pow_succ 5 (e + 2)]
    omega

private theorem onlySmall {k e : ℕ} (heq : triangular k = 10^e) : e ≤ 1 := by
  have hmul : k * (k + 1) = 2^(e+1) * 5^e := by
    rw [← twice, heq, show (10 : ℕ) = 2*5 by decide, mul_pow, pow_succ]
    ring
  by_contra! he
  have hgap : 2^(e+1) + 1 < 5^e := by
    obtain ⟨s,rfl⟩ : ∃ s, e = s + 2 := ⟨e-2, by omega⟩
    exact gap s
  have kd : 5^e ∣ k * (k+1) := by rw [hmul]; exact dvd_mul_left _ _
  have hp : 5^e ∣ k ∨ 5^e ∣ k+1 := by
    by_cases h5 : 5 ∣ k
    · have co : Nat.Coprime (5^e) (k+1) :=
        (Nat.prime_five.coprime_iff_not_dvd.mpr (by omega)).pow_left e
      exact Or.inl (co.dvd_of_dvd_mul_right kd)
    · have co : Nat.Coprime (5^e) k :=
        (Nat.prime_five.coprime_iff_not_dvd.mpr h5).pow_left e
      exact Or.inr (co.dvd_of_dvd_mul_left kd)
  have hk : 0 < k := by
    by_contra! hz
    have : k = 0 := by omega
    subst k
    have hpos : 0 < 2^(e+1) * 5^e := by positivity
    omega
  have hlarge : 5^e ≤ k + 1 := hp.elim (fun h => by have := Nat.le_of_dvd hk h; omega)
    (Nat.le_of_dvd (Nat.succ_pos k))
  have hgt : 2^(e+1) < k := by omega
  have hlt := Nat.mul_lt_mul_of_pos_right hgt (by positivity : 0 < 5^e)
  have hle := Nat.mul_le_mul_left k hlarge
  omega

private theorem finiteExamples : Set.Finite
    {t : ℕ | (∃ k : ℕ, t = triangular k) ∧ (Nat.digits 10 t).sum = 1} := by
  apply (Set.toFinite ({1, 10} : Set ℕ)).subset
  rintro t ⟨⟨k, hk⟩, ht⟩
  obtain ⟨e, he⟩ := oneDigit _ ht
  rw [Nat.ofDigits_digits] at he
  have hs := onlySmall (hk.symm.trans he)
  interval_cases e <;> simp_all

end TriangularDigitSum

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a068128.main) := by
  intro h
  exact (h 1) TriangularDigitSum.finiteExamples
