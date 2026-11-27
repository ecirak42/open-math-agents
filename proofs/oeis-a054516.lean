import OMAStatements.S_oeis_a054516
import Mathlib.Tactic.Ring

open OMA.S_oeis_a054516

theorem OMA.solution : type_of% @OMA.S_oeis_a054516.main := by
  intro k
  dsimp only
  simp only [fromThree, Nat.cast_succ]
  ring
