import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.ParityModular
import Library.Theory.Prime
import Library.Theory.InjectiveSurjective
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
import Library.Tactic.Product

set_option push_neg.use_distrib true
open Function

/- 3 points -/
theorem problem4a {f : X → Y} (hf : Surjective f) {g : Y → Z} (hg : Surjective g) :
    Surjective (g ∘ f) := by
  dsimp [Surjective] at *
  intro z
  obtain ⟨y, hy⟩ := hg z
  obtain ⟨x, hx⟩ := hf y
  use x
  rw [hx, hy]

/- 2 points -/
theorem problem4b {f : X → Y} (hf : Surjective f) : ∃ g : Y → X, f ∘ g = id := by
/-based on usage of choose in example 8.3.7-/
  dsimp [Surjective] at *
  choose g hg using hf
  use g
  ext x
  rel [hg, x]


/- 2 points -/
theorem problem4c {f : X → Y} {g : Y → X} (h : Inverse f g) : Inverse g f := by
  dsimp [Inverse] at *
  obtain ⟨h1, h2⟩ := h
  use h2
  apply h1

/- 3 points -/
theorem problem4d {f : X → Y} {g1 g2 : Y → X} (h1 : Inverse f g1) (h2 : Inverse f g2) :
    g1 = g2 := by
  dsimp [Inverse] at *
  obtain ⟨hg1f, hfg1⟩ := h1
  obtain ⟨hg2f, hfg2⟩ := h2
  dsimp [id] at *
  funext x
  have heq : (f ∘ g1) x = (f ∘ g2) x := by rw [hfg1, hfg2]
  have hg1x : (f ∘ g1) x = x := by rw [hfg1]
  have hg2x : (f ∘ g2) x = x := by rw [hfg2]
  have heq' : g1 ((f ∘ g1) x) = g1 ((f ∘ g2) x) := by rw [heq]

  have hidk : g1 ((f ∘ g1) x) = (g1 x) := by rw [hg1x]
  have hwe : g1 x = g2 x := by
    calc
      g1 x = g1 ((f ∘ g1) x) := by rw [hidk]
      _ = g1 ((f ∘ g2) x) := by rw [heq']
      _ = (g1 ∘ f ∘ g2) x := by rfl
      _ = (g1 ∘ f) (g2 x) := by rfl
      _ = g2 x := by rw [hg1f]
  rw [hwe]
  






/-
      _ = g2 ((f ∘ g2) ((f ∘ g2) x)) := by rw [←hg1f, ←hg2f]
      _ = g2 ((f ∘ g2) ((f ∘ g2) x)) := by rw [←hg1x, ←hg2x, ←heq]
      _ = g2 x := by rw [←hg2x]
-/




























/-
/- 1 points -/
theorem problem5a1 : ¬ Injective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  sorry

/- 1 points -/
theorem problem5a2 : Surjective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  sorry

/- 2 points -/
theorem problem5b : ¬ Surjective (fun ((x, y) : ℚ × ℚ) ↦ x ^ 2 + y ^ 2) := by
  sorry

/- 3 points -/
theorem problem5c : ¬ Injective
    (fun ((x, y, z) : ℝ × ℝ × ℝ) ↦ (x + y + z, x + 2 * y + 3 * z)) := by
  sorry

/- 3 points -/
theorem problem5d : Injective (fun ((x, y) : ℝ × ℝ) ↦ (x + y, x + 2 * y, x + 3 * y)) := by
  sorry
-/
