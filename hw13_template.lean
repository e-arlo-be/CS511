import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Set
import Library.Theory.Comparison
import Library.Theory.InjectiveSurjective
import Library.Theory.Parity
import Library.Theory.ParityModular
import Library.Theory.Prime
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Define
import Library.Tactic.ExistsDelaborator
import Library.Tactic.Extra
import Library.Tactic.FiniteInductive
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Numbers
import Library.Tactic.Product
import Library.Tactic.Rel
import Library.Tactic.Use

set_option push_neg.use_distrib true
open Set

notation:50 a:50 " ⊈ " b:50 => ¬ (a ⊆ b)

/- 3 points -/
theorem problem4a : {a : ℕ | 5 ∣ a} ⊈ {x : ℕ | 20 ∣ x} := by
/-Based on example 9.1.4-/
  dsimp [Set.subset_def]
  push_neg
  use 5
  simp


/- 3 points -/
theorem problem4b : {k : ℤ | 7 ∣ 9 * k} = {l : ℤ | 7 ∣ l} := by
/-Based on example 9.1.7-/
  ext x
  dsimp
  constructor
  . intro h
    obtain ⟨k, hk⟩ := h
    use (-3 * k + 4 * x)
    calc
      x = - 3 * (9 * x) + 28 * x := by ring
      _ = -3 * (7 * k) + 28 * x := by rw [hk]
      _ = -3 * (7 * k) + 4 * 7 * x := by ring
      _ = 7 * (-3 * k + 4 * x) := by ring
  . intro h
    obtain ⟨k, hk⟩ := h
    use (9 * k)
    calc
      9 * x = 9 * (7 * k) := by rw[hk]
      _ = 7 * (9 * k) := by ring

/- 4 points -/
theorem problem4c : {x : ℝ | x ^ 2 + 3 * x + 2 = 0} = {-1, -2} := by
/-Based on example 9.1.8-/
  ext x
  dsimp
  constructor
  · intro h
    have hx :=
    calc
      (x + 1) * (x + 2) = x ^ 2 + 3 * x + 2 := by ring
      _ = 0 := by rw [h]
    rw [mul_eq_zero] at hx
    obtain (hx | hx) := hx
    · left
      addarith [hx]
    · right
      addarith [hx]
  intro h
  obtain (h | h) := h
  · calc x ^ 2 + 3 * x + 2 = (-1) ^ 2 + 3 * (-1) + 2 := by rw [h]
    _ = 0 := by ring
  · calc x ^ 2 + 3 * x + 2 = (-2) ^ 2 + 3 * (-2) + 2 := by rw [h]
    _ = 0 := by ring


/- 3 points -/
theorem problem5a : {r : ℤ | r ≡ 7 [ZMOD 10] }
    ⊆ {s : ℤ | s ≡ 1 [ZMOD 2]} ∩ {t : ℤ | t ≡ 2 [ZMOD 5]} := by
  dsimp [Set.subset_def]
  intro x hx
  obtain ⟨k, hk⟩ := hx
  constructor
  · use (5 * k + 3)
    calc
      x - 1 = (x - 7) + 6 := by ring
      _ = 10 * k + 6 := by rw [hk]
      _ = 2 * (5 * k + 3) := by ring
  · use (2 * k + 1)
    calc
      x - 2 = (x - 7) + 5 := by ring
      _ = 10 * k + 5 := by rw [hk]
      _ = 5 * (2 * k + 1) := by ring

/- 3 points -/
theorem problem5b : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} ⊆ {n : ℤ | 40 ∣ n} := by
  dsimp [Set.subset_def]
  intro x hx
  obtain ⟨h5, h8⟩ := hx
  obtain ⟨k, hk⟩ := h5
  obtain ⟨l, hl⟩ := h8
  use (-3 * l + 2 * k)
  calc
    x = -15 * x + 16 * x := by ring
    _ = -15 * (8 * l) + 16 * x := by rw [hl]
    _ = -15 * (8 * l) + 16 * (5 * k) := by rw [hk]
    _ = 40 * (-3 * l + 2 * k) := by ring

/- 4 points -/
theorem problem5c :
    {n : ℤ | 3 ∣ n} ∪ {n : ℤ | 2 ∣ n} ⊆ {n : ℤ | n ^ 2 ≡ 1 [ZMOD 6]}ᶜ := by
  dsimp [Set.subset_def]
  intro x hx
  obtain (h3 | h2) := hx
  · intro h
    obtain ⟨k, hk⟩ := h
    obtain ⟨l, hl⟩ := h3
    
