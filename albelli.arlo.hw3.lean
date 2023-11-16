import Mathlib.Data.Real.Basic
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

/-4a-/  
example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  · have := calc 
      0 < -x * t := by addarith[hxt]
      _ = x*(-t) := by ring
    cancel x at this
    have : 0 > t := by exact Iff.mp neg_pos this
    exact ne_of_lt this

/-4b-/  
example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a+1
  use a
  ring

/-4c-/  
example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by 
  use (p + q) / 2
  have h2 : p < (p + q) / 2 := by linarith
  have h3 : (p + q) / 2 < q := by linarith
  exact ⟨h2, h3⟩
  
/-5a-/
example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  use x + 1
  have h : x < x + 1 := by linarith
  have h4 : x < (x + 1) ^ 2 := by nlinarith
  exact h4

/-5b-/
example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  intro ht
  rcases h with ⟨a, h⟩ 
  rw[ht] at h
  apply Iff.mp (lt_self_iff_false (a+1))
  simp at h

/-5c-/
example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨a, h⟩ := h
  intro hm
  rw[hm] at h
  obtain h1 | h1 :=  le_or_gt a 2 
  · have := calc
      5 = 2*a := by rw[h]
      _ ≤ 2 * 2 := by rel[h1] 
    simp at this
  · have h1 : a ≥ 3 := by exact h1
    have := calc
      5 = 2 * a := by rw[h]
      _ ≥ 2 * 3 := by rel[h1]
      _ = 6 := by numbers
    simp at this

