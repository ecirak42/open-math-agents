import OMAStatements.S_oeis_a301977
import Mathlib.Tactic

/-!
# OEIS A301977

Appending a binary digit updates the counts of even and odd subsequence
values by one of the two Stern recurrences. For the Stirling row, split the
columns into even and odd positions. The odd-column entries modulo two
satisfy a Fibonacci-polynomial recurrence, which gives exactly the same
two Stern recurrences for their row counts.
-/

namespace OMA.S_oeis_a301977

private def oddAt (n r : Nat) := Nat.stirlingSecond n (2*r+1) % 2
private def oddCount (n : Nat) := ∑ r ∈ Finset.range n, oddAt n r

private theorem oddBound (n r : Nat) : oddAt n r < 2 := Nat.mod_lt _ (by decide)

private theorem firstOdd (n : Nat) : oddAt (n+1) 0 = 1 := by
  simp [oddAt, Nat.stirlingSecond_one_right]

private theorem evenStep (n r : Nat) :
    Nat.stirlingSecond (n+1) (2*r+2) % 2 = oddAt n r := by
  rw [Nat.stirlingSecond_succ_succ, Nat.add_mod, Nat.mul_mod]
  rw [show (2*r+1+1)%2 = 0 by omega]
  simp [oddAt]

private theorem oddStep (n r : Nat) :
    oddAt (n+2) (r+1) = (oddAt (n+1) (r+1) + oddAt n r) % 2 := by
  have he : Nat.stirlingSecond (n+1) (2*(r+1)) % 2 = oddAt n r := by
    simpa only [Nat.mul_succ] using evenStep n r
  unfold oddAt at ⊢
  rw [Nat.stirlingSecond_succ_succ, Nat.add_mod, Nat.mul_mod]
  rw [show (2*(r+1)+1)%2 = 1 by omega, he]
  simp [oddAt]

private theorem doubling (n : Nat) : ∀ r : Nat,
    oddAt (2*n) (2*r) = oddAt n r ∧ oddAt (2*n) (2*r+1) = 0 ∧
    oddAt (2*n+1) (2*r) = oddAt (n+1) r ∧ oddAt (2*n+1) (2*r+1) = oddAt n r := by
  induction n with
  | zero =>
    intro r
    cases r with
    | zero => decide
    | succ r => simp (disch := omega) [oddAt, Nat.stirlingSecond_eq_zero_of_lt]
  | succ n ih =>
    have evenEven (r : Nat) : oddAt (2*n+2) (2*r) = oddAt (n+1) r := by
      cases r with
      | zero => simp only [Nat.mul_zero, firstOdd]
      | succ r =>
        rw [show 2*(r+1) = (2*r+1)+1 by omega, oddStep,
          show 2*r+1+1 = 2*(r+1) by omega, (ih (r+1)).2.2.1, (ih r).2.1]
        simp [Nat.mod_eq_of_lt (oddBound _ _)]
    have evenOdd (r : Nat) : oddAt (2*n+2) (2*r+1) = 0 := by
      rw [oddStep, (ih r).2.2.2, (ih r).1]
      omega
    have oddEven (r : Nat) : oddAt (2*n+3) (2*r) = oddAt (n+2) r := by
      cases r with
      | zero => simp only [Nat.mul_zero, firstOdd]
      | succ r =>
        rw [show 2*(r+1) = (2*r+1)+1 by omega, oddStep,
          show 2*r+1+1 = 2*(r+1) by omega, evenEven, (ih r).2.2.2, oddStep]
    have oddOdd (r : Nat) : oddAt (2*n+3) (2*r+1) = oddAt (n+1) r := by
      rw [oddStep, evenOdd, (ih r).2.2.1]
      simp [Nat.mod_eq_of_lt (oddBound _ _)]
    intro r
    simpa only [Nat.mul_succ, Nat.add_assoc] using
      And.intro (evenEven r) ⟨evenOdd r, oddEven r, oddOdd r⟩

private theorem pairSum (f : Nat → Nat) (n : Nat) :
    (∑ k ∈ Finset.range (2*n), f k) =
      ∑ k ∈ Finset.range n, (f (2*k) + f (2*k+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.mul_succ, Finset.sum_range_succ, ih]
    omega

private theorem countEven (n : Nat) : oddCount (2*n) = oddCount n := by
  unfold oddCount
  rw [pairSum]
  simp only [(doubling n _).1, (doubling n _).2.1, Nat.add_zero]

private theorem countOdd (n : Nat) : oddCount (2*n+1) = oddCount (n+1) + oddCount n := by
  unfold oddCount
  rw [Finset.sum_range_succ, pairSum]
  simp only [(doubling n _).2.2.1, (doubling n _).2.2.2,
    Finset.sum_add_distrib, Finset.sum_range_succ]
  omega

private theorem stirlingTotal (n : Nat) :
    (∑ k ∈ Finset.range n, Nat.stirlingSecond (n+1) (k+1)%2) + 1 =
      oddCount (n+1) + oddCount n := by
  let f := fun k => Nat.stirlingSecond (n+1) (k+1)%2
  have pad : (∑ k ∈ Finset.range (n+1), f k) =
      ∑ k ∈ Finset.range (2*(n+1)), f k := by
    have incl : Finset.range (n+1) ⊆ Finset.range (2*(n+1)) := by
      intro k hk
      simp only [Finset.mem_range] at hk ⊢
      omega
    apply Finset.sum_subset incl
    intro k _ hk
    simp only [Finset.mem_range] at hk
    simp [f, Nat.stirlingSecond_eq_zero_of_lt (by omega : n+1 < k+1)]
  have left : (∑ k ∈ Finset.range (n+1), f k) =
      (∑ k ∈ Finset.range n, f k) + 1 := by
    rw [Finset.sum_range_succ]
    simp [f, Nat.stirlingSecond_self]
  rw [pairSum] at pad
  have hf (k : Nat) : f (2*k) + f (2*k+1) = oddAt (n+1) k + oddAt n k := by
    change oddAt (n+1) k + Nat.stirlingSecond (n+1) (2*k+2)%2 = _
    rw [evenStep]
  have last : oddAt n n = 0 := by
    simp [oddAt, Nat.stirlingSecond_eq_zero_of_lt (by omega : n < 2*n+1)]
  rw [left] at pad
  simp only [hf, Finset.sum_add_distrib] at pad
  have tail : (∑ k ∈ Finset.range (n+1), oddAt n k) = oddCount n := by
    simp only [Finset.sum_range_succ, last, Nat.add_zero, oddCount]
  rw [tail] at pad
  exact pad

private def box (S : Finset Nat) (b : Nat) := S.filter (fun x => x%2=b)

private theorem boxTotal (S : Finset Nat) : (box S 0).card + (box S 1).card = S.card := by
  have e : box S 1 = S.filter (fun x => ¬ x%2=0) := by
    ext x
    simp only [box, Finset.mem_filter]
    constructor <;> rintro ⟨hx, hr⟩ <;> exact ⟨hx, by omega⟩
  rw [e]
  exact Finset.card_filter_add_card_filter_not _

private theorem halving (n : Nat) : ∀ x ∈ subseqs n, x/2 ∈ subseqs n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · subst n
      simp [subseqs]
    · rw [subseqs]
      simp only [hn, ite_false]
      intro x hx
      simp only [appendDigit, Finset.mem_union, Finset.mem_image] at hx ⊢
      rcases hx with hx | ⟨y, hy, rfl⟩
      · exact Or.inl (ih (n/2) (by omega) x hx)
      · left
        rwa [show (2*y+n%2)/2=y by omega]

private theorem boxAppSame (n b : Nat) (hb : b<2) :
    (box (appendDigit (subseqs n) b) b).card = (subseqs n).card := by
  have e : box (appendDigit (subseqs n) b) b = (subseqs n).image (fun x => 2*x+b) := by
    ext x
    simp only [box, appendDigit, Finset.mem_filter, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨hx,hb'⟩
      rcases hx with hx | hx
      · exact ⟨x/2, halving n x hx, by omega⟩
      · exact hx
    · rintro ⟨y, hy, rfl⟩
      exact ⟨Or.inr ⟨y,hy,rfl⟩, by omega⟩
  rw [e]
  apply Finset.card_image_of_injective
  intro x y h
  dsimp at h
  omega

private theorem boxAppOther (n b c : Nat) (hb : b<2) (hbc : b≠c) :
    box (appendDigit (subseqs n) b) c = box (subseqs n) c := by
  ext x
  simp only [box, appendDigit, Finset.mem_filter, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨hx, hc⟩
    rcases hx with hx | ⟨y, _, rfl⟩
    · exact ⟨hx,hc⟩
    · omega
  · rintro ⟨hx,hc⟩
    exact ⟨Or.inl hx,hc⟩

private theorem matchBoxes (n : Nat) :
    (box (subseqs n) 0).card = oddCount (n+1) ∧
    (box (subseqs n) 1).card = oddCount n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · subst n
      simp [subseqs, box, oddCount, oddAt]
      decide
    · let m := n/2
      have hlt : m<n := by dsimp [m]; omega
      obtain ⟨h0,h1⟩ := ih m hlt
      have ht := boxTotal (subseqs m)
      have e : subseqs n = appendDigit (subseqs m) (n%2) := by
        rw [subseqs]
        simp only [hn, ite_false, m]
      rw [e]
      rcases (by omega : n%2=0 ∨ n%2=1) with hb | hb
      · have en : n = 2*m := by dsimp [m]; omega
        rw [hb, boxAppSame m 0 (by decide), boxAppOther m 0 1 (by decide) (by decide), en,
          countOdd, countEven]
        omega
      · have en : n = 2*m+1 := by dsimp [m]; omega
        rw [hb, boxAppOther m 1 0 (by decide) (by decide), boxAppSame m 1 (by decide), en,
          show 2*m+1+1=2*(m+1) by omega, countEven, countOdd]
        omega

end OMA.S_oeis_a301977

open OMA.S_oeis_a301977

theorem OMA.solution : type_of% @OMA.S_oeis_a301977.main := by
  intro n _
  obtain ⟨h0,h1⟩ := matchBoxes n
  have hc := boxTotal (subseqs n)
  have hs := stirlingTotal n
  omega
