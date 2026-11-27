import OMAStatements.S_oeis_a265284
import Mathlib.Tactic

/-!
# OEIS A265284

Starting with the second generation, each row has an alternating interior.
The two outer blocks of black cells alternate between length two and length
three. Michael De Vlieger recorded the row counts in A118102 in 2015.
Here the row pattern follows from the local rule, after which summing
the row counts gives Barker's five formulas for the cumulative count.
-/

namespace OMA.S_oeis_a265284

private def pairs : Nat → List Bool
  | 0 => []
  | k+1 => false :: true :: pairs k

private def evenWord (k : Nat) : List Bool := true :: true :: (pairs k ++ [true])
private def oddWord (k : Nat) : List Bool := true :: true :: true :: (pairs k ++ [true,true])

private theorem scanPairs (k : Nat) (tail ending : List Bool)
    (h : scan false true tail = true :: ending) :
    scan false true (pairs k ++ tail) = true :: (pairs k ++ ending) := by
  induction k with
  | zero => simpa [pairs] using h
  | succ k ih =>
    change true :: false :: scan false true (pairs k ++ tail) = _
    rw [ih]
    rfl

private theorem scanPairs11 (k : Nat) (tail ending : List Bool)
    (h : scan false true tail = true :: ending) :
    scan true true (pairs (k+1) ++ tail) = true :: (pairs (k+1) ++ ending) := by
  change true :: false :: scan false true (pairs k ++ tail) = _
  rw [scanPairs k tail ending h]
  rfl

private theorem snocPair (k : Nat) (tail : List Bool) :
    pairs k ++ false :: true :: tail = pairs (k+1) ++ tail := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change false :: true :: (pairs k ++ false :: true :: tail) = _
    rw [ih]
    rfl

private theorem nextEven (k : Nat) : next (evenWord (k+1)) = oddWord (k+1) := by
  unfold next evenWord oddWord
  simp only [List.cons_append,List.append_assoc,List.nil_append]
  change true :: true :: scan true true (pairs (k+1) ++ [true,false,false]) = _
  rw [scanPairs11 k _ [true,true] (by rfl)]

private theorem nextOdd (k : Nat) : next (oddWord (k+1)) = evenWord (k+3) := by
  unfold next evenWord oddWord
  simp only [List.cons_append,List.append_assoc,List.nil_append]
  change true :: true :: false :: scan true true (pairs (k+1) ++ [true,true,false,false]) = _
  rw [scanPairs11 k _ [false,true,true] (by rfl),snocPair (k+1) [true]]
  rfl

private theorem words (k : Nat) : row (2*k+2) = evenWord (2*k+1) ∧
    row (2*k+3) = oddWord (2*k+1) := by
  induction k with
  | zero => exact ⟨rfl,rfl⟩
  | succ k ih =>
    have he : row (2*(k+1)+2) = evenWord (2*(k+1)+1) := by
      rw [show 2*(k+1)+2 = (2*k+3)+1 by omega,
        show 2*(k+1)+1 = 2*k+3 by omega,row,ih.2,nextOdd]
    refine ⟨he,?_⟩
    rw [show 2*(k+1)+3 = (2*(k+1)+2)+1 by omega,row,he,nextEven]

private theorem onesPairs (k : Nat) (tail : List Bool) :
    ones (pairs k ++ tail) = (k:Int) + ones tail := by
  induction k with
  | zero => simp [pairs]
  | succ k ih => simp [pairs,ones,ih]; omega

private theorem black (k : Nat) : ones (row (2*k+2)) = 2*(k:Int)+4 ∧
    ones (row (2*k+3)) = 2*(k:Int)+6 := by
  obtain ⟨he,ho⟩ := words k
  rw [he,ho]
  simp [evenWord,oddWord,ones,onesPairs]
  omega

private theorem totals (k : Nat) : a (2*k+2) = 2*(k:Int)^2+10*k+8 ∧
    a (2*k+3) = 2*(k:Int)^2+12*k+14 := by
  induction k with
  | zero => decide
  | succ k ih =>
    obtain ⟨be,bo⟩ := black (k+1)
    have he : a (2*(k+1)+2) = 2*((k+1:Nat):Int)^2+10*(k+1:Nat)+8 := by
      calc
        a (2*(k+1)+2) = a (2*k+3) + ones (row (2*(k+1)+2)) := by
          rw [show 2*(k+1)+2 = (2*k+3)+1 by omega,a]
        _ = _ := by rw [ih.2,be]; push_cast; ring
    refine ⟨he,?_⟩
    calc
      a (2*(k+1)+3) = a (2*(k+1)+2) + ones (row (2*(k+1)+3)) := rfl
      _ = _ := by rw [he,bo]; push_cast; ring

private theorem closed (n : Nat) (hn : 0 < n) :
    4*a n = 2*(n:Int)^2 + 12*n - (-1)^n + 1 := by
  by_cases h : n = 1
  · subst n; decide
  generalize hk : (n-2)/2 = k
  have cases2 : n = 2*k+2 ∨ n = 2*k+3 := by omega
  rcases cases2 with rfl | rfl
  · rw [(totals k).1]
    simp only [pow_add,pow_mul,neg_one_sq,one_pow]
    push_cast
    ring
  · rw [(totals k).2]
    simp only [pow_add,pow_mul,neg_one_sq,one_pow]
    push_cast
    ring

private theorem recurrence (n : Nat) (hn : 0 < n) :
    a (n+4) = 2*a (n+3) - 2*a (n+1) + a n := by
  have h0 := closed n hn
  have h1 := closed (n+1) (by omega)
  have h3 := closed (n+3) (by omega)
  have h4 := closed (n+4) (by omega)
  simp only [pow_add,pow_one,Nat.cast_add,Nat.cast_ofNat] at h1 h3 h4
  have h : 4*(a (n+4) - 2*a (n+3) + 2*a (n+1) - a n) = 0 := by
    linear_combination h4 - 2*h3 + 2*h1 - h0
  omega

private theorem series (n : Nat) : productCoeff n = numeratorCoeff n := by
  match n with
  | 0 | 1 | 2 | 3 | 4 => decide
  | k+5 =>
    have h := recurrence (k+1) (by omega)
    change a (k+5) = 2*a (k+4) - 2*a (k+2) + a (k+1) at h
    change a (k+5) - 2*a (k+4) + 2*a (k+2) - a (k+1) = 0
    omega

end OMA.S_oeis_a265284

open OMA.S_oeis_a265284

theorem OMA.solution : type_of% @OMA.S_oeis_a265284.main := by
  refine ⟨closed,?_,?_,?_,series⟩
  · intro n hn he
    have h := closed n (by omega)
    rw [he.neg_one_pow] at h
    omega
  · intro n ho
    have hn : 0 < n := by obtain ⟨k,hk⟩ := ho; omega
    have h := closed n hn
    rw [ho.neg_one_pow] at h
    omega
  · intro n hn
    have h := recurrence (n-4) (by omega)
    simpa only [show n-4+4 = n by omega,show n-4+3 = n-1 by omega,
      show n-4+1 = n-3 by omega] using h
