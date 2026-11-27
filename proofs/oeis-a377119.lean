import OMAStatements.S_oeis_a377119
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

/-!
# OEIS A377119

Multiplication by t+t² has determinant six. If this vanishes in a prime field,
the square coefficient vanishes at every exponent from three onwards. Otherwise
the multiplication is injective, so its finite orbit is periodic from exponent
zero. Counting hits per period converts this to periodicity of the gaps.

The first actual gap for p=2 is three, contradicting the specified block.
-/

namespace OMA.S_oeis_a377119

private theorem castThird (p n : Nat) :
    ((a n : Nat) : ZMod p) = (coefficients (ZMod p) n).2.2 := by
  have aux : ∀ k : Nat,
      (((coefficients Nat k).1 : ZMod p), ((coefficients Nat k).2.1 : ZMod p),
        ((coefficients Nat k).2.2 : ZMod p)) = coefficients (ZMod p) k := by
    intro k
    induction k with
    | zero => simp [coefficients]
    | succ k ih =>
      simp only [coefficients, ← ih, advance, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  exact congrArg (fun v : ZMod p × ZMod p × ZMod p => v.2.2) (aux n)

private theorem advanceInjective (p : Nat) [Fact p.Prime] (h6 : (6 : ZMod p) ≠ 0) :
    Function.Injective (@advance (ZMod p) _) := by
  rintro ⟨a,b,c⟩ ⟨u,v,w⟩ h
  have hx : 2*(b+c) = 2*(v+w) := congrArg Prod.fst h
  have hy : a+2*c = u+2*w := congrArg (fun t => t.2.1) h
  have hz : a+b = u+v := congrArg (fun t => t.2.2) h
  have ha : (6 : ZMod p)*(a-u) = 0 := by linear_combination 2*hy + 4*hz - 2*hx
  have hb : (6 : ZMod p)*(b-v) = 0 := by linear_combination 2*hx - 2*hy + 2*hz
  have hc : (6 : ZMod p)*(c-w) = 0 := by linear_combination hx + 2*hy - 2*hz
  obtain rfl := sub_eq_zero.mp <| (mul_eq_zero.mp ha).resolve_left h6
  obtain rfl := sub_eq_zero.mp <| (mul_eq_zero.mp hb).resolve_left h6
  obtain rfl := sub_eq_zero.mp <| (mul_eq_zero.mp hc).resolve_left h6
  rfl

private theorem periodicOrbit (p : Nat) [Fact p.Prime] (h6 : (6 : ZMod p) ≠ 0) :
    ∃ T : Nat, 0 < T ∧ ∀ n, coefficients (ZMod p) (n+T) = coefficients (ZMod p) n := by
  let f := coefficients (ZMod p)
  have cancel (i d : Nat) : f (i+d) = f i → f d = f 0 := by
    induction i with
    | zero => simp
    | succ i ih =>
      intro h
      apply ih
      apply advanceInjective p h6
      simpa only [Nat.succ_add, f, coefficients] using h
  obtain ⟨x,y,hne,he⟩ := Finite.exists_ne_map_eq_of_infinite f
  have ordered : ∃ i j, i < j ∧ f i = f j := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨x,y,h,he⟩
    · exact ⟨y,x,h,he.symm⟩
  obtain ⟨i,j,hij,hf⟩ := ordered
  refine ⟨j-i, by omega, ?_⟩
  have base : f (j-i) = f 0 := cancel i (j-i) (by
    rw [show i+(j-i) = j by omega]
    exact hf.symm)
  intro n
  induction n with
  | zero => simpa [f] using base
  | succ n ih =>
    simpa only [Nat.succ_add, coefficients] using congrArg advance ih

private theorem periodicHits (p : Nat) (hp : Nat.Prime p) :
    ∃ L T : Nat, 0 < T ∧ p ∣ a L ∧ ∀ n ≥ L, (p ∣ a (n+T) ↔ p ∣ a n) := by
  let : Fact p.Prime := ⟨hp⟩
  have bridge (n : Nat) : p ∣ a n ↔ (coefficients (ZMod p) n).2.2 = 0 := by
    rw [← castThird]
    exact (ZMod.natCast_eq_zero_iff _ _).symm
  by_cases h6 : (6 : ZMod p) = 0
  · have vanishes (n : Nat) : p ∣ a (n+3) := by
      rw [bridge]
      let v := coefficients (ZMod p) n
      change (advance (advance (advance v))).2.2 = 0
      calc
        _ = 6*(v.1+v.2.1+v.2.2) := by simp [advance]; ring
        _ = 0 := by rw [h6, zero_mul]
    have all (m : Nat) (hm : 3 ≤ m) : p ∣ a m := by
      have eq : m-3+3 = m := by omega
      simpa only [eq] using vanishes (m-3)
    refine ⟨3,1,by decide,vanishes 0,?_⟩
    intro n hn
    exact iff_of_true (all _ (by omega)) (all _ hn)
  · obtain ⟨T,hT,per⟩ := periodicOrbit p h6
    refine ⟨0,T,hT,by simp [a,coefficients],?_⟩
    intro n _
    rw [bridge,bridge,per]

private theorem gapsOfPeriodicHits (P : Nat → Prop) [DecidablePred P] (L T : Nat)
    (hT : 0 < T) (hL : P L) (per : ∀ n ≥ L, P (n+T) ↔ P n) :
    (Set.ofPred P).Infinite ∧ ∃ N C : Nat, 0 < C ∧ ∀ i ≥ N,
      Nat.nth P (i+C+1) - Nat.nth P (i+C) = Nat.nth P (i+1) - Nat.nth P i := by
  have hitting (k : Nat) : P (L+k*T) := by
    induction k with
    | zero => simpa using hL
    | succ k ih =>
      rw [Nat.succ_mul, ← Nat.add_assoc]
      exact (per _ (by omega)).2 ih
  have mono : StrictMono (fun k : Nat => L+k*T) := by
    intro i j hij
    exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right hij hT) L
  have inf : (Set.ofPred P).Infinite :=
    (Set.infinite_range_of_injective mono.injective).mono (by rintro _ ⟨k,rfl⟩; exact hitting k)
  let C := Nat.count P (L+T) - Nat.count P L
  have h1 : Nat.count P (L+1) = Nat.count P L+1 := by simp [Nat.count_succ,hL]
  have h2 : Nat.count P (L+1) ≤ Nat.count P (L+T) := Nat.count_monotone P (by omega)
  have positive : 0 < C := by dsimp [C]; omega
  have counts (x : Nat) (hx : L ≤ x) : Nat.count P (x+T) = Nat.count P x + C := by
    induction x, hx using Nat.le_induction with
    | base => dsimp [C]; omega
    | succ x hx ih =>
      rw [Nat.succ_add, Nat.count_succ, Nat.count_succ P x, ih]
      simp only [per x hx]
      omega
  have shift (i : Nat) (hi : L ≤ i) : Nat.nth P (i+C) = Nat.nth P i + T := by
    have hx : L ≤ Nat.nth P i := le_trans hi ((Nat.nth_strictMono inf).id_le i)
    have member : P (Nat.nth P i+T) := (per _ hx).2 (Nat.nth_mem_of_infinite inf i)
    have eq := counts _ hx
    rw [Nat.count_nth_of_infinite inf i] at eq
    rw [← eq]
    exact Nat.nth_count member
  refine ⟨inf,L,C,positive,?_⟩
  intro i hi
  rw [show i+C+1 = (i+1)+C by omega, shift _ (by omega), shift i hi]
  omega

/-- The infinite-divisibility and eventual-gap-periodicity assertions both hold. -/
theorem generalPeriodicity : generalClaim := by
  intro p hp
  obtain ⟨L,T,hT,hL,per⟩ := periodicHits p hp
  exact gapsOfPeriodicHits (fun n => p ∣ a n) L T hT hL per

private theorem firstGap : gap 2 0 = 3 := by
  let P := fun n : Nat => 2 ∣ a n
  have h0 : Nat.nth P (Nat.count P 0) = 0 := Nat.nth_count (by decide : P 0)
  have h3 : Nat.nth P (Nat.count P 3) = 3 := Nat.nth_count (by decide : P 3)
  have c0 : Nat.count P 0 = 0 := by decide
  have c3 : Nat.count P 3 = 1 := by decide
  rw [c0] at h0
  rw [c3] at h3
  change Nat.nth P 1 - Nat.nth P 0 = 3
  rw [h0,h3]

end OMA.S_oeis_a377119

open OMA.S_oeis_a377119

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a377119.main) := by
  intro h
  have hwrong : gap 2 0 = 2 := h.2.1 0
  have hright := firstGap
  omega
