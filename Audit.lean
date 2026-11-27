
import Mathlib

/-!
# The two formulas conjectured for OEIS A122554

Source: https://oeis.org/A122554
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A122/A122554.seq
Credit: @Heart-galaxy

The source has offset 1. Starting with S(1) = {1}, S(n) is the smallest set
containing x, 2*x, and x+2 for each x in S(n-1); a(n) is its cardinality.
The union below is exactly that smallest set. S(0) is an unused convention.

R. J. Mathar conjectured the order-four recurrence for n > 6 and the Lucas
formula for n > 2 on November 18, 2009. The source reports both conjectures
proved by Sela Fried on February 18, 2026; see
https://oeis.org/A122554/a122554.pdf . This file states the known result.
LucasNat uses the canonical initial values L(0)=2 and L(1)=1.

The recurrence is written as an equality of sums to avoid truncated subtraction.
-/

namespace OMA.S_oeis_a122554

/-- Layman's sets; index zero is an unused convention. -/
def S : ℕ → Finset ℕ
  | 0 => ∅
  | 1 => {1}
  | n + 2 => S (n + 1) ∪ (S (n + 1)).image (fun x => x + 2) ∪
      (S (n + 1)).image (fun x => 2 * x)

/-- The cardinality sequence A122554 at its positive indices. -/
def a (n : ℕ) : ℕ := (S n).card

/-- The Lucas numbers with their canonical zero-indexed initial values. -/
def LucasNat : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => LucasNat n + LucasNat (n + 1)

/-- Mathar's two conjectures, reported proved in the source in 2026. -/
theorem main :
    (∀ n : ℕ, 6 < n →
      a n + 2 * a (n - 2) + a (n - 3) = 3 * a (n - 1) + a (n - 4)) ∧
    (∀ n : ℕ, 2 < n → a n = LucasNat n + n - 1) := by
  sorry

end OMA.S_oeis_a122554


/-!
We formalize Sela Fried's proof in Section 2 of "Proof of two conjectures
on Layman sets stated in A000126 and A122554" (2026). The odd elements form
an interval in steps of two. Dividing the even elements by two produces a
union of two smaller sets whose intersection is a consecutive interval.
-/

namespace Layman122554
open OMA.S_oeis_a122554 Finset

private theorem step (n x : ℕ) : x ∈ S (n+2) ↔ x ∈ S (n+1) ∨
    (∃ y ∈ S (n+1), y+2=x) ∨ (∃ y ∈ S (n+1), 2*y=x) := by
  simp only [S, mem_union, mem_image, or_assoc]

private theorem keep (n : ℕ) {x : ℕ} (h : x ∈ S (n+1)) :
    x ∈ S (n+2) := (step n x).mpr (Or.inl h)

private theorem addTwo (n : ℕ) {x : ℕ} (h : x ∈ S (n+1)) :
    x+2 ∈ S (n+2) := (step n _).mpr (Or.inr (Or.inl ⟨x, h, rfl⟩))

private theorem double (n : ℕ) {x : ℕ} (h : x ∈ S (n+1)) :
    2*x ∈ S (n+2) := (step n _).mpr (Or.inr (Or.inr ⟨x, h, rfl⟩))

private theorem positive (n x : ℕ) (h : x ∈ S (n+1)) : 0 < x := by
  induction n generalizing x with
  | zero =>
    have hx : x = 1 := by simpa [S] using h
    omega
  | succ n ih =>
    rcases (step n x).mp h with h | ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
    · exact ih x h
    · omega
    · have := ih y hy
      omega

private theorem odds (n x : ℕ) : 2*x+1 ∈ S (n+1) ↔ x ≤ n := by
  induction n generalizing x with
  | zero => simp [S]
  | succ n ih =>
    constructor
    · intro h
      rcases (step n _).mp h with h | ⟨y, hy, eq⟩ | ⟨y, _, eq⟩
      · have := (ih x).mp h
        omega
      · have ey : y = 2*(x-1)+1 := by omega
        rw [ey] at hy
        have := (ih (x-1)).mp hy
        omega
      · omega
    · intro h
      by_cases hx : x ≤ n
      · exact keep n ((ih x).mpr hx)
      · have := addTwo n ((ih n).mpr (le_refl n))
        rwa [show 2*n+1+2 = 2*x+1 by omega] at this

private theorem initialInterval (n x : ℕ) (hp : 0 < x) (hx : x ≤ 2*(n+3)) : x ∈ S (n+3) := by
  induction n generalizing x with
  | zero =>
    have h3 : S 3 = {1,2,3,4,5,6} := by decide
    rw [h3]
    simp only [mem_insert, mem_singleton]
    omega
  | succ n ih =>
    by_cases h : x ≤ 2*(n+3)
    · exact keep (n+2) (ih x hp h)
    · have hm := ih (x-2) (by omega) (by omega)
      have ha := addTwo (n+2) hm
      rwa [show x-2+2 = x by omega] at ha

private theorem halves (n x : ℕ) : 2*x ∈ S (n+3) ↔
    x ∈ S (n+2) ∨ ∃ y ∈ S (n+1), y+1 = x := by
  induction n generalizing x with
  | zero =>
    have h1 : S 1 = {1} := rfl
    have h2 : S 2 = {1,2,3} := by decide
    have h3 : S 3 = {1,2,3,4,5,6} := by decide
    simp only [h1,h2,h3,mem_insert,mem_singleton,exists_eq_left]
    omega
  | succ n ih =>
    constructor
    · intro hx
      rcases (step (n+2) _).mp hx with h | ⟨y, hy, eq⟩ | ⟨y, hy, eq⟩
      · rcases (ih x).mp h with h | ⟨z, hz, eq⟩
        · exact Or.inl (keep (n+1) h)
        · exact Or.inr ⟨z, keep n hz, eq⟩
      · rw [show y=2*(x-1) by omega] at hy
        rcases (ih (x-1)).mp hy with h | ⟨z, hz, ez⟩
        · exact Or.inr ⟨x-1, h, by omega⟩
        · have h2 := keep (n+1) (addTwo n hz)
          exact Or.inl (by rwa [show z+2=x by omega] at h2)
      · exact Or.inl (by rwa [show y=x by omega] at hy)
    · rintro (h | ⟨y, hy, rfl⟩)
      · exact double (n+2) h
      · simpa [Nat.mul_add] using addTwo (n+2) (double (n+1) hy)

private theorem overlap (n : ℕ) :
    S (n+4) ∩ (S (n+3)).image (fun x => x+1) = Icc 2 (2*n+7) := by
  ext x
  simp only [mem_inter, mem_image, mem_Icc]
  constructor
  · rintro ⟨hx, y, hy, eq⟩
    have hp := positive (n+2) y hy
    refine ⟨by omega, ?_⟩
    by_cases he : x%2=0
    · rw [show y=2*(y/2)+1 by omega] at hy
      have := (odds (n+2) (y/2)).mp hy
      omega
    · rw [show x=2*(x/2)+1 by omega] at hx
      have := (odds (n+3) (x/2)).mp hx
      omega
  · rintro ⟨hl, hu⟩
    exact ⟨initialInterval (n+1) x (by omega) (by omega),
      x-1, initialInterval n (x-1) (by omega) (by omega), by omega⟩

private theorem recurrence (n : ℕ) : a (n+5) + (n+1) = a (n+4) + a (n+3) := by
  let H := S (n+4) ∪ (S (n+3)).image (fun x => x+1)
  let O := (range (n+5)).image (fun x => 2*x+1)
  let E := H.image (fun x => 2*x)
  have heq : S (n+5) = O ∪ E := by
    ext x
    simp only [O,E,H,mem_union,mem_image,mem_range]
    constructor
    · intro hx
      by_cases he : x%2=0
      · have eq : 2*(x/2)=x := by omega
        exact Or.inr ⟨x/2, (halves (n+2) (x/2)).mp (by rwa [eq]), eq⟩
      · have eq : 2*(x/2)+1=x := by omega
        have h := (odds (n+4) (x/2)).mp (by rwa [eq])
        exact Or.inl ⟨x/2, by omega, eq⟩
    · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
      · exact (odds (n+4) y).mpr (by omega)
      · exact (halves (n+2) y).mpr hy
  have hd : Disjoint O E := by
    rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨u, _, hu⟩ := mem_image.mp hx
    obtain ⟨v, _, hv⟩ := mem_image.mp hy
    change 2*u+1 = x at hu
    change 2*v = x at hv
    omega
  have ia : Function.Injective (fun x : ℕ => x+1) := by intro x y h; dsimp at h; omega
  have io : Function.Injective (fun x : ℕ => 2*x+1) := by intro x y h; dsimp at h; omega
  have ie : Function.Injective (fun x : ℕ => 2*x) := by intro x y h; dsimp at h; omega
  have hsum := Finset.card_union_add_card_inter (S (n+4)) ((S (n+3)).image (fun x => x+1))
  rw [overlap, Nat.card_Icc, card_image_of_injective _ ia] at hsum
  change H.card + _ = _ at hsum
  unfold a
  rw [heq, card_union_of_disjoint hd]
  simp only [O,E,card_image_of_injective _ io,card_image_of_injective _ ie,card_range]
  omega

private theorem closedForm (k : ℕ) : a (k+3)+1 = LucasNat (k+3)+(k+3) := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rcases k with _|k
    · decide
    rcases k with _|k
    · decide
    have h0 := ih k (by omega)
    have h1 := ih (k+1) (by omega)
    change a (k+4)+1 = LucasNat (k+4)+(k+4) at h1
    have hl : LucasNat (k+5) = LucasNat (k+3) + LucasNat (k+4) := rfl
    have hr := recurrence k
    change a (k+5)+1 = LucasNat (k+5)+(k+5)
    omega

end Layman122554

open OMA.S_oeis_a122554

theorem OMA.solution : type_of% @OMA.S_oeis_a122554.main := by
  constructor
  · intro n hn
    obtain ⟨k,rfl⟩ : ∃ k, n=k+7 := ⟨n-7, by omega⟩
    have h := Layman122554.recurrence k
    have h1 := Layman122554.recurrence (k+1)
    have h2 := Layman122554.recurrence (k+2)
    change a (k+6)+(k+2) = a (k+5)+a (k+4) at h1
    change a (k+7)+(k+3) = a (k+6)+a (k+5) at h2
    simp only [show ∀ i : ℕ, i+7-2=i+5 by omega,
      show ∀ i : ℕ, i+7-3=i+4 by omega, show ∀ i : ℕ, i+7-4=i+3 by omega,
      show ∀ i : ℕ, i+7-1=i+6 by omega]
    omega
  · intro n hn
    obtain ⟨k,rfl⟩ : ∃ k, n=k+3 := ⟨n-3, by omega⟩
    have := Layman122554.closedForm k
    omega

#print axioms OMA.solution
