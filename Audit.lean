import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Mathlib

/-!
# OEIS A382605

Daniel Mondot asks when the cyclic chain of rods 1, 2, ..., n can be folded
into two equal sides, with both turns at joints. Between two joints i < j,
one side consists of the consecutive rods i+1 through j. The other side
consists of the remaining rods in their cyclic order.

The second equivalence uses the original difference-of-squares definition
of the index sequence A154708. Both sequences start at positive indices.

Sources: https://oeis.org/A382605 and https://oeis.org/A154708
Formalization: @ecirak42.
-/

namespace OMA.S_oeis_a382605

def total : ℕ → ℕ
  | 0 => 0
  | n+1 => total n + (n+1)

def folds (n : ℕ) : Prop :=
  ∃ i j : ℕ, i < j ∧ j ≤ n ∧ 2 * total j = total n + 2 * total i

def inA154708 (n : ℕ) : Prop :=
  ∃ b c : ℕ, b ≤ n ∧ n < c ∧ n*(n+1) + b^2 = c^2

theorem main : ∀ n : ℕ, 0 < n →
    (folds n ↔ Even (total n)) ∧ (folds n ↔ inA154708 n) := by
  sorry

end OMA.S_oeis_a382605


/-!
Kenneth Graves gave the two-post construction for Bob Wainwright's chain
problem in MIT Technology Review, Puzzle Corner, May 2004, DEC 2.
Here the cut positions and the A154708 square witnesses are explicit.
-/

namespace RodFolds
open OMA.S_oeis_a382605

private theorem twice (n : ℕ) : 2 * total n = n*(n+1) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [total]; nlinarith

private theorem residues (n : ℕ) (b c : ZMod 4)
    (h : (n : ZMod 4)*((n : ZMod 4)+1) + b^2 = c^2) :
    n % 4 = 0 ∨ n % 4 = 3 := by
  have allCases : ∀ x y z : ZMod 4, x*(x+1)+y^2=z^2 → x=0 ∨ x=3 := by decide
  rcases allCases n b c h with he | he
  · left
    simpa using congrArg ZMod.val he
  · right
    simpa using congrArg ZMod.val he

private theorem witnesses (n : ℕ) (hn : 0 < n) (h : n % 4 = 0 ∨ n % 4 = 3) :
    folds n ∧ inA154708 n := by
  let k := n / 4
  rcases h with h | h
  · have e : n = 4*k := by dsimp [k]; omega
    have hk : 0 < k := by omega
    rw [e]
    constructor
    · refine ⟨k, 3*k, by omega, by omega, ?_⟩
      nlinarith [twice (3*k), twice k, twice (4*k)]
    · exact ⟨3*k+1, 5*k+1, by omega, by omega, by ring⟩
  · have e : n = 4*k+3 := by dsimp [k]; omega
    rw [e]
    constructor
    · refine ⟨k, 3*k+2, by omega, by omega, ?_⟩
      nlinarith [twice (3*k+2), twice k, twice (4*k+3)]
    · exact ⟨3*k+2, 5*k+4, by omega, by omega, by ring⟩

end RodFolds

open OMA.S_oeis_a382605

theorem OMA.solution : type_of% @OMA.S_oeis_a382605.main := by
  intro n hn
  have ef : Even (total n) → folds n ∧ inA154708 n := by
    rintro ⟨a, ha⟩
    have ht := RodFolds.twice n
    have eq : n*(n+1) = 4*a := by omega
    have hz := congrArg (fun x : ℕ => (x : ZMod 4)) eq
    push_cast at hz
    have zero : (4 : ZMod 4) = 0 := by decide
    rw [zero, zero_mul] at hz
    exact RodFolds.witnesses n hn (RodFolds.residues n 0 0 (by simpa using hz))
  have fe : folds n → Even (total n) := by
    rintro ⟨i, j, _, _, h⟩
    exact ⟨total j - total i, by omega⟩
  refine ⟨⟨fe, fun h => (ef h).1⟩, ⟨fun h => (ef (fe h)).2, ?_⟩⟩
  rintro ⟨b, c, _, _, h⟩
  have hz := congrArg (fun x : ℕ => (x : ZMod 4)) h
  push_cast at hz
  exact (RodFolds.witnesses n hn (RodFolds.residues n b c hz)).1

#print axioms OMA.solution
