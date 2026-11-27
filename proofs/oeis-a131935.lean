import OMAStatements.S_oeis_a131935

/-!
# OEIS A131935

Advancing the endpoint counts four times proves the same linear
identity in each parity. The recurrence then gives every coefficient of
the generating-function identity beyond the first five.
-/

namespace OMA.S_oeis_a131935

lemma fourSteps (s : Bool × Endpoints) :
    (advance (advance (advance (advance s)))).2.total + (advance s).2.total + s.2.total =
      (advance (advance (advance s))).2.total + 3 * (advance (advance s)).2.total := by
  rcases s with ⟨phase, ⟨w, x, y, z⟩⟩
  cases phase <;> simp [advance, oddToEven, evenToOdd, Endpoints.total] <;> omega

lemma recurrence {n : Nat} (hn : 1 ≤ n) :
    a (n + 4) + a (n + 1) + a n = a (n + 3) + 3 * a (n + 2) := by
  cases n with
  | zero => omega
  | succ k => exact fourSteps (state k)

lemma generatingFunction (n : Nat) :
    productCoeff (fun k => (a k : Int)) [1, -1, -3, 1, 1] n = numeratorCoeff n := by
  match n with
  | 0 | 1 | 2 | 3 | 4 => decide
  | k + 5 =>
    have h := recurrence (n := k + 1) (by omega)
    simp [productCoeff, numeratorCoeff, Nat.add_assoc] at *
    omega

end OMA.S_oeis_a131935

open OMA.S_oeis_a131935

theorem OMA.solution : type_of% @OMA.S_oeis_a131935.main :=
  ⟨fun _ hn => recurrence hn, generatingFunction⟩
