import OMAStatements.S_oeis_a397588
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

namespace A397588Proof

open PowerSeries

private theorem parity_indices (g : PowerSeries (ZMod 2)) (hg : g = X + g ^ 2) :
    ∀ n : ℕ, 1 ≤ n → (g.coeff n = 1 ↔ ∃ k : ℕ, n = 2 ^ k) := by
  have he : g ^ 2 = g.expand 2 (by decide) := by
    simpa only [PowerSeries.expand, ZMod.frobenius_zmod, MvPowerSeries.map_id, RingHom.id_apply] using
      (MvPowerSeries.map_frobenius_expand 2 (by decide) (f := g)).symm
  have hc (n : ℕ) : g.coeff n = (if n = 1 then 1 else 0) +
      (if 2 ∣ n then g.coeff (n / 2) else 0) := by
    conv_lhs => rw [hg, he]
    rw [map_add, coeff_X, coeff_expand]
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hone : n = 1
    · subst n
      constructor
      · exact fun _ => ⟨0, rfl⟩
      · exact fun _ => by simpa using hc 1
    by_cases hd : 2 ∣ n
    · obtain ⟨m, rfl⟩ := hd
      have hm : 1 ≤ m := by omega
      have hrec : g.coeff (2 * m) = g.coeff m := by simpa [hone] using hc (2 * m)
      rw [hrec, ih m (by omega) hm]
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨k + 1, by rw [pow_succ']⟩
      · rintro ⟨k, hk⟩
        cases k with
        | zero => simp at hk
        | succ k => exact ⟨k, by rw [pow_succ'] at hk; omega⟩
    · have hz : g.coeff n = 0 := by simpa [hone, hd] using hc n
      rw [hz]
      constructor
      · intro h
        exact (zero_ne_one h).elim
      · rintro ⟨k, rfl⟩
        cases k with
        | zero => exact (hone rfl).elim
        | succ k => exact (hd ⟨2 ^ k, pow_succ' 2 k⟩).elim

end A397588Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a397588.main := by
  intro A _hzero hA
  let red := Int.castRingHom (ZMod 2)
  let g := PowerSeries.map red A
  have h2 : PowerSeries.map red (2 : PowerSeries ℤ) = 0 := by
    calc
      _ = (2 : PowerSeries (ZMod 2)) := map_ofNat _ _
      _ = PowerSeries.C (2 : ZMod 2) := (map_ofNat _ _).symm
      _ = 0 := by rw [show (2 : ZMod 2) = 0 by decide, map_zero]
  rw [Derivation.leibniz, PowerSeries.derivative_pow, PowerSeries.derivative_X] at hA
  have hg : g = PowerSeries.X + g ^ 2 := by
    simpa [g, smul_eq_mul, map_add, map_mul, map_pow, h2] using congrArg (PowerSeries.map red) hA
  simpa [g, red, PowerSeries.coeff_map] using A397588Proof.parity_indices g hg
