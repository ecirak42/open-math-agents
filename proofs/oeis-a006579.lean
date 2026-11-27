import OMAStatements.S_oeis_a006579

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
      simp

private theorem primeValue (p : ℕ) (hp : p.Prime) : pillai p = 2*p-1 := by
  rw [divisorsFormula, hp.divisors]
  simp [Ne.symm hp.ne_one, hp.pos, Nat.totient_prime hp]
  omega

private theorem value : pillai 23492890653051 = 610815156979325 := by
  change pillai ((((3*37)*43)*42307)*116341) = _
  simp (disch := decide) only [multiplicative.map_mul_of_coprime]
  simp (disch := norm_num) only [primeValue]
  decide

end GcdSumCounterexample

open OMA.S_oeis_a006579

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a006579.main) := by
  intro h
  apply h 23492890653051 (by decide) (by norm_num)
  have hg := GcdSumCounterexample.sumFormula 23492890653051 (by decide)
  rw [GcdSumCounterexample.value] at hg
  rw [show gcdSum 23492890653051 = 587322266326274 by omega]
  decide
