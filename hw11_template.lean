import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.ParityModular
import Library.Theory.Prime
import Mathlib.Tactic.Set
import Library.Tactic.ExistsDelaborator
import Library.Tactic.FiniteInductive
import Library.Tactic.Induction
import Library.Tactic.Rel
import Library.Tactic.ModCases
import Mathlib.Tactic.GCongr
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

set_option push_neg.use_distrib true
open Function

/- 2 points -/
theorem problem4a : ¬ ∀ (f : ℤ → ℤ), Surjective f → Surjective (fun x ↦ 2 * f x) := by
  dsimp [Surjective]
  push_neg
  use fun x ↦ x
  constructor
  ·
    intro x
    use x
    ring
  ·
    use 1
    intro x
    simp
    push_neg
    intro h1
    have h2x : Int.Even (2 * x) := by
      dsimp [Int.Even]
      simp
    have h2 : Int.Odd 1 := by
      dsimp [Int.Odd]
      simp
    have h2' := Int.odd_iff_not_even 1
    simp [h2] at h2'
    rw [h1] at h2x
    exact h2' h2x


/- 2 points -/
theorem problem4b : ¬ ∀ c : ℝ, Surjective (fun x ↦ c * x) := by
  dsimp [Surjective]
  push_neg
  use 0 -- c = 0
  use 1 -- b = 1
  simp


/- 3 points -/
theorem problem4c {f : ℚ → ℚ} (hf : ∀ x y, x < y → f x < f y) : Injective f := by
  dsimp [Injective]
  intros x y hxy
  have hrel := lt_trichotomy x y
  cases hrel with
  | inl xlt =>
    have hfxlt := hf x y xlt
    rw [hxy] at hfxlt
    simp at hfxlt
  | inr lteq =>
    cases lteq with
    | inl xeqy =>
      rw [xeqy]
    | inr ylt =>
      have hfylt := hf y x ylt
      rw [hxy] at hfylt
      simp at hfylt


/- 3 points -/
theorem problem4d {f : X → ℕ} {x0 : X} (h0 : f x0 = 0) {i : X → X}
    (hi : ∀ x, f (i x) = f x + 1) : Surjective f := by
  dsimp [Surjective]
  intro n
  simple_induction n with k IH
  · -- n = 0
    use x0
    exact h0
  · -- n = k + 1
    cases IH with
    | intro x hx =>
      use i x
      rw [hi, hx]

/-
/- 2 points -/
theorem problem5a : Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
  sorry

/- 2 points -/
theorem problem5b : ¬ Bijective (fun (x : ℝ) ↦ x ^ 2 + 2 * x) := by
  sorry

def Inverse (f : X → Y) (g : Y → X) : Prop := g ∘ f = id ∧ f ∘ g = id

def u (x : ℝ) : ℝ := 5 * x + 1

noncomputable def v (x : ℝ) : ℝ := sorry

/- 3 points -/
theorem problem5c : Inverse u v := by
  sorry

/- 3 points -/
theorem problem5d {f : X → Y} (hf : Injective f) {g : Y → Z} (hg : Injective g) :
    Injective (g ∘ f) := by
  sorry
-/
