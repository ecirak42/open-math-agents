import OMAStatements.S_oeis_a395839
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

namespace A395839Proof

open PowerSeries OMA.S_oeis_a395839

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

private abbrev red (p : ℕ) := PowerSeries.map (Int.castRingHom (ZMod p))

private theorem cat_eq (p : ℕ) : red p catalanZ = 1 + X * (red p catalanZ) ^ 2 := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom ℤ)) catalanSeries_sq_mul_X_add_one
  have hz : catalanZ = 1 + X * catalanZ ^ 2 := by
    simpa [catalanZ, map_add, map_mul, map_pow, add_comm, mul_comm] using h.symm
  simpa [map_add, map_mul, map_pow, red] using congrArg (red p) hz

private theorem red_ten (p : ℕ) : red p (10 : PowerSeries ℤ) = C (10 : ZMod p) := calc
  _ = (10 : PowerSeries (ZMod p)) := map_ofNat _ _
  _ = C (10 : ZMod p) := (map_ofNat _ _).symm

private theorem shift {R : Type*} [CommSemiring R] (f : PowerSeries R) (n : ℕ) :
    (f * X).coeff (n + 1) = f.coeff n := by
  simp

theorem parity (n : ℕ) :
    ((series.coeff n : ℤ) : ZMod 2) = 1 ↔ ∃ k : ℕ, n + 1 = 2 ^ k := by
  let c := red 2 catalanZ
  have hten : red 2 (10 : PowerSeries ℤ) = 0 := by
    rw [red_ten 2, show (10 : ZMod 2) = 0 by decide, map_zero]
  have ha : red 2 series = c := by
    rw [series, map_sub, map_mul, hten, zero_mul, zero_sub]
    ext i
    simp [c]
  have hy : c * X = X + (c * X) ^ 2 := calc
    c * X = (1 + X * c ^ 2) * X := congrArg (· * X) (cat_eq 2)
    _ = X + (c * X) ^ 2 := by ring
  change (red 2 series).coeff n = 1 ↔ _
  rw [ha, ← shift c n]
  exact parity_indices _ hy (n + 1) (by omega)

theorem modThree (n : ℕ) :
    ((series.coeff (3 * n + 1) : ℤ) : ZMod 3) = (catalan n : ZMod 3) ∧
    ((series.coeff (3 * n) : ℤ) : ZMod 3) = 0 ∧
    ((series.coeff (3 * n + 2) : ℤ) : ZMod 3) = 0 := by
  let c := red 3 catalanZ
  have hten : red 3 (10 : PowerSeries ℤ) = 1 := by
    rw [red_ten 3, show (10 : ZMod 3) = 1 by decide, map_one]
  have hf : c ^ 3 = c.expand 3 (by decide) := by
    simpa only [PowerSeries.expand, ZMod.frobenius_zmod, MvPowerSeries.map_id, RingHom.id_apply] using
      (MvPowerSeries.map_frobenius_expand 3 (by decide) (f := c)).symm
  have ha : red 3 series = c.expand 3 (by decide) * X := by
    rw [series, map_sub, map_mul, map_pow, hten, one_mul, ← hf]
    change c ^ 2 - c = c ^ 3 * X
    linear_combination c * (cat_eq 3)
  have hc (i : ℕ) : (red 3 series).coeff (i+1) =
      (if 3 ∣ i then c.coeff (i/3) else 0) := by
    rw [ha, shift, coeff_expand]
  have hcat (i : ℕ) : c.coeff i = (catalan i : ZMod 3) := by
    simp [c, red, catalanZ, coeff_map]
  change (red 3 series).coeff (3*n+1) = _ ∧ (red 3 series).coeff (3*n) = 0 ∧
    (red 3 series).coeff (3*n+2) = 0
  refine ⟨by simpa [hcat] using hc (3*n), ?_, ?_⟩
  · cases n with
    | zero =>
      rw [ha]
      simp [coeff_zero_eq_constantCoeff_apply]
    | succ m =>
      rw [show 3*(m+1) = (3*m+2)+1 by omega, hc]
      simp [show ¬ 3 ∣ 3*m+2 by omega]
  · rw [show 3*n+2 = (3*n+1)+1 by omega, hc]
    simp [show ¬ 3 ∣ 3*n+1 by omega]

end A395839Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a395839.main :=
  ⟨A395839Proof.parity, A395839Proof.modThree⟩

