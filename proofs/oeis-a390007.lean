import OMAStatements.S_oeis_a390007
import Mathlib.Tactic

/-!
# OEIS A390007

The full strip has the width nearest to n/3, and the second cut is the
most balanced unequal split. For each of the six residue classes we
compare the proposed defect with the nearest competing widths, and
then use monotonicity to eliminate all other widths.

The six optimal defect values and a constructive analysis are given
by C. Dalfó, M. A. Fiol and N. López, "New results for the Mondrian art
problem", Theorem 2.1. Here the inequalities are strict away from the
candidate except for the two minimizers when n=4.
-/

namespace OMA.S_oeis_a390007

private def A (n : Int) := (n+1)/3
private def B (n : Int) := (n-1)/2

private theorem dimensions (n : Int) (hn : 3 ≤ n) : valid n (.tee (A n) (B n)) := by
  simp only [valid, A, B]
  omega

private theorem adjacentBounds (n : Int) (hn : 3 ≤ n) (h4 : n ≠ 4) :
    defect n (.tee (A n) (B n)) < 2*n ∧
    defect n (.tee (A n) (B n)) < (n-B n)*(n-(A n-1)) - n*(A n-1) ∧
    defect n (.tee (A n) (B n)) < n*(A n+1) - B n*(n-(A n+1)) := by
  generalize hq : n/6 = q
  have cases6 : n=6*q ∨ n=6*q+1 ∨ n=6*q+2 ∨ n=6*q+3 ∨ n=6*q+4 ∨ n=6*q+5 := by omega
  have work (a b : Int) (ha : A n = a) (hb : B n = b) :
      defect n (.tee (A n) (B n)) < 2*n ∧
      defect n (.tee (A n) (B n)) < (n-B n)*(n-(A n-1)) - n*(A n-1) ∧
      defect n (.tee (A n) (B n)) < n*(A n+1) - B n*(n-(A n+1)) ↔
      spread (n*a) (b*(n-a)) ((n-b)*(n-a)) < 2*n ∧
      spread (n*a) (b*(n-a)) ((n-b)*(n-a)) < (n-b)*(n-(a-1)) - n*(a-1) ∧
      spread (n*a) (b*(n-a)) ((n-b)*(n-a)) < n*(a+1) - b*(n-(a+1)) := by
    rw [ha,hb]
    rfl
  rcases cases6 with h | h | h | h | h | h
  · apply (work (2*q) (3*q-1) (by unfold A; omega) (by unfold B; omega)).2
    rw [h]
    simp only [spread,max_lt_iff]
    repeat' constructor <;> ring_nf <;> omega
  · apply (work (2*q) (3*q) (by unfold A; omega) (by unfold B; omega)).2
    rw [h]
    simp only [spread,max_lt_iff]
    repeat' constructor <;> ring_nf <;> omega
  · apply (work (2*q+1) (3*q) (by unfold A; omega) (by unfold B; omega)).2
    rw [h]
    simp only [spread,max_lt_iff]
    repeat' constructor <;> ring_nf <;> omega
  · apply (work (2*q+1) (3*q+1) (by unfold A; omega) (by unfold B; omega)).2
    rw [h]
    simp only [spread,max_lt_iff]
    repeat' constructor <;> ring_nf <;> omega
  · apply (work (2*q+1) (3*q+1) (by unfold A; omega) (by unfold B; omega)).2
    rw [h]
    simp only [spread,max_lt_iff]
    repeat' constructor <;> ring_nf <;> omega
  · apply (work (2*q+2) (3*q+2) (by unfold A; omega) (by unfold B; omega)).2
    rw [h]
    simp only [spread,max_lt_iff]
    repeat' constructor <;> ring_nf <;> omega

private theorem wider (x l h e : Int) (he : 0 < e) :
    spread x l h < spread x (l-e) (h+e) := by
  unfold spread
  apply max_lt
  · exact lt_of_lt_of_le (by omega : h-l < h+e-(l-e)) (le_max_left _ _)
  · apply max_lt
    · exact lt_of_lt_of_le (by omega : x-l < x-(l-e)) ((le_max_left _ _).trans (le_max_right _ _))
    · exact lt_of_lt_of_le (by omega : h-x < h+e-x) ((le_max_right _ _).trans (le_max_right _ _))

private theorem strictCompetitor (n : Int) (hn : 3 ≤ n) (h4 : n ≠ 4)
    (s : TileSet) (hs : valid n s) (hne : s ≠ .tee (A n) (B n)) :
    defect n (.tee (A n) (B n)) < defect n s := by
  obtain ⟨hstrips,hleft,hright⟩ := adjacentBounds n hn h4
  cases s with
  | strips x y z =>
    obtain ⟨_,hxy,hyz,_⟩ := hs
    exact lt_of_lt_of_le hstrips (by
      change 2*n ≤ n*(z-x)
      nlinarith only [mul_nonneg (by omega : 0 ≤ n) (by omega : 0 ≤ z-x-2)])
  | tee a b =>
    obtain ⟨_,ha,_,hb⟩ := hs
    have hB : b ≤ B n := by unfold B; omega
    have hBpos : 0 < B n := (dimensions n hn).2.2.1
    have hBlt : B n < n := by unfold B; omega
    have slack : 0 ≤ (n-a)*(B n-b) := mul_nonneg (by omega) (by omega)
    rcases lt_trichotomy a (A n) with hlo | heq | hhi
    · have slope : 0 ≤ (2*n-B n)*(A n-1-a) := mul_nonneg (by omega) (by omega)
      have bound : (n-B n)*(n-(A n-1))-n*(A n-1) ≤ (n-b)*(n-a)-n*a := by
        nlinarith only [slack,slope]
      exact hleft.trans_le (bound.trans ((le_max_right _ _).trans (le_max_right _ _)))
    · subst a
      have hblt : b < B n := by
        by_contra! h
        exact hne (by congr 1; omega)
      let e := (n-A n)*(B n-b)
      have he : 0 < e := mul_pos (by omega) (by omega)
      change spread _ _ _ < spread _ _ _
      rw [show b*(n-A n) = B n*(n-A n)-e by dsimp [e]; ring,
        show (n-b)*(n-A n) = (n-B n)*(n-A n)+e by dsimp [e]; ring]
      exact wider _ _ _ _ he
    · have slope : 0 ≤ (n+B n)*(a-A n-1) := mul_nonneg (by omega) (by omega)
      have bound : n*(A n+1)-B n*(n-(A n+1)) ≤ n*a-b*(n-a) := by
        nlinarith only [slack,slope]
      exact hright.trans_le (bound.trans ((le_max_left _ _).trans (le_max_right _ _)))

private theorem uniqueAway (n : Int) (hn : 3 ≤ n) (h4 : n ≠ 4) :
    ∃! s, optimal n s := by
  let best := TileSet.tee (A n) (B n)
  have hbest : optimal n best := by
    refine ⟨dimensions n hn, ?_⟩
    intro s hs
    by_cases h : s = best
    · rw [h]
    · exact (strictCompetitor n hn h4 s hs h).le
  refine ⟨best,hbest,?_⟩
  intro s hs
  by_contra h
  exact (not_lt_of_ge (hs.2 best hbest.1)) (strictCompetitor n hn h4 s hs.1 h)

private theorem four : ¬ ∃! s, optimal 4 s := by
  have bound : ∀ t, valid 4 t → 6 ≤ defect 4 t := by
    intro t ht
    cases t with
    | strips x y z =>
      obtain ⟨_,_,_,_⟩ := ht
      omega
    | tee a b =>
      obtain ⟨ha,han,hb,hd⟩ := ht
      have : b = 1 := by omega
      subst b
      interval_cases a <;> decide
  have first : optimal 4 (.tee 1 1) := ⟨by decide,bound⟩
  have second : optimal 4 (.tee 2 1) := ⟨by decide,bound⟩
  rintro ⟨w,_,h⟩
  have e := (h _ first).trans (h _ second).symm
  cases e

end OMA.S_oeis_a390007

open OMA.S_oeis_a390007

theorem OMA.solution : type_of% @OMA.S_oeis_a390007.main := by
  intro n hn
  constructor
  · rintro h rfl
    exact four h
  · exact uniqueAway n hn
