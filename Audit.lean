
import Mathlib

/-!
# The gcd sum at composite indices (OEIS A006579)

Source: https://oeis.org/A006579, conjecture of Thomas Ordowski, June 11, 2025.
Credit: @Mmexicann
-/

namespace OMA.S_oeis_a006579

/-- Sum of the gcds of `n` with the positive integers strictly below `n`. -/
def gcdSum (n : ℕ) : ℕ :=
  (Finset.Ico 1 n).sum (fun k => Nat.gcd n k)

theorem main : ∀ n : ℕ, 1 < n → ¬ n.Prime →
    ¬ Int.ModEq (n : ℤ) (gcdSum n : ℤ) (-1) := by
  sorry

end OMA.S_oeis_a006579


/-!
Varun Vejalla published the counterexample on 19 June 2025 in A018804.
The two sequences differ by the endpoint n. Grouping by gcd identifies
the inclusive sum with the Dirichlet convolution of the identity and
Euler's totient, which is multiplicative.
-/

namespace GcdSumCounterexample
open OMA.S_oeis_a006579 Finset ArithmeticFunction

private def phi : ArithmeticFunction ℕ := ⟨Nat.totient, Nat.totient_zero⟩
private def pillai := ArithmeticFunction.id * phi

private theorem multiplicative : pillai.IsMultiplicative :=
  isMultiplicative_id.mul (show phi.IsMultiplicative from
    ⟨Nat.totient_one, fun h => Nat.totient_mul h⟩)

private theorem divisorsFormula (n : ℕ) :
    pillai n = ∑ d ∈ n.divisors, d * (n/d).totient := by
  exact Nat.sum_divisorsAntidiagonal (fun x y => x * y.totient)

private theorem sumFormula (n : ℕ) (hn : 0 < n) : n + gcdSum n = pillai n := by
  have hm (k : ℕ) (_ : k ∈ range n) : n.gcd k ∈ n.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, hn.ne'⟩
  calc
    n + gcdSum n = ∑ k ∈ range n, n.gcd k := by
      rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hn]
      simp [gcdSum]
    _ = ∑ d ∈ n.divisors, ∑ k ∈ (range n).filter (fun k => n.gcd k = d), d :=
      (sum_fiberwise_of_maps_to' hm (fun d => d)).symm
    _ = pillai n := by
      rw [divisorsFormula]
      apply sum_congr rfl
      intro d hd
      rw [Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd), sum_const, nsmul_eq_mul, mul_comm]

private theorem primeValue (p : ℕ) (hp : p.Prime) : pillai p = 2*p-1 := by
  rw [divisorsFormula, hp.divisors]
  simp [Ne.symm hp.ne_one, hp.pos, Nat.totient_prime hp]
  omega

private theorem value : pillai 23492890653051 = 610815156979325 := by
  change pillai ((((3*37)*43)*42307)*116341) = _
  rw [multiplicative.map_mul_of_coprime (m := 3*37*43*42307) (n := 116341) (by decide),
      multiplicative.map_mul_of_coprime (m := 3*37*43) (n := 42307) (by decide),
      multiplicative.map_mul_of_coprime (m := 3*37) (n := 43) (by decide),
      multiplicative.map_mul_of_coprime (m := 3) (n := 37) (by decide)]
  rw [primeValue 3 (by norm_num), primeValue 37 (by norm_num),
      primeValue 43 (by norm_num), primeValue 42307 (by norm_num),
      primeValue 116341 (by norm_num)]

end GcdSumCounterexample

open OMA.S_oeis_a006579

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a006579.main) := by
  intro h
  have hnp : ¬ Nat.Prime 23492890653051 := by
    intro hp
    have hh := (Nat.dvd_prime hp).mp (show 3 ∣ 23492890653051 from ⟨7830963551017, rfl⟩)
    omega
  apply h 23492890653051 (by decide) hnp
  have hg := GcdSumCounterexample.sumFormula 23492890653051 (by decide)
  rw [GcdSumCounterexample.value] at hg
  rw [show gcdSum 23492890653051 = 587322266326274 by omega]
  decide

#print axioms OMA.disproof
