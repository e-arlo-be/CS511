import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

/-4a-/
example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 7 * k + 1
  calc
    7 * n - 4 = 7 * (2 * k + 1) - 4 := by rw [hk]
    _ = 2 * (7 * k + 1) + 1 := by ring

/-4b-/
example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use 2 * a * b + a + 3 * b + 1
  calc
    x * y + 2 * y = (2 * a + 1) * (2 * b + 1) + 2 * (2 * b + 1) := by rw [ha, hb]
    _ = 4 * a * b + 2 * a + 6 * b + 3 := by ring
    _ = 2 * (2 * a * b + a + 3 * b + 1) + 1 := by ring

/-4c-/
example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  dsimp [Even, Odd] at *
  obtain ⟨r, hr⟩ := hn
  use 2 * r ^ 2 + 2 * r - 3
  calc
    n ^ 2 + 2 * n - 5 = (r + r)^2 + 2 * (r + r) - 5 := by rw [hr]
    _ = 2 * (2 * r ^ 2 + 2 * r - 3) + 1 := by ring

/-4d-/
example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  obtain ha | ha := Int.even_or_odd a
  · obtain hb | hb := Int.even_or_odd b
    · left
      obtain ⟨r, hr⟩ := ha
      obtain ⟨s, hs⟩ := hb
      use r - s
      calc
        a - b = 2 * r - b := by rw [hr]
        _ = 2 * r - 2 * s := by rw [hs]
        _ = (r - s) + (r - s) := by ring
    · obtain hc | hc := Int.even_or_odd c
      · right; left
        obtain ⟨r, hr⟩ := ha
        obtain ⟨s, hs⟩ := hc
        use r + s
        calc
          a + c = 2 * r + c := by rw [hr]
          _ = 2 * r + 2 * s := by rw [hs]
          _ = (r + s) + (r + s) := by ring
      · right; right
        obtain ⟨r, hr⟩ := hb
        obtain ⟨s, hs⟩ := hc
        use r - s
        calc
          b - c = 2 * r + 1 - c := by rw [hr]
          _ = 2 * r + 1 - (2 * s + 1) := by rw [hs]
          _ = (r - s) + (r - s) := by ring
  · obtain hb | hb := Int.even_or_odd b
    · obtain hc | hc := Int.even_or_odd c
      · right; right
        obtain ⟨r, hr⟩ := hb
        obtain ⟨s, hs⟩ := hc
        use r - s
        calc
          b - c = 2 * r - c := by rw [hr]
          _ = 2 * r - (2 * s) := by rw [hs]
          _ = (r - s) + (r - s) := by ring
      · right; left
        obtain ⟨r, hr⟩ := ha
        obtain ⟨s, hs⟩ := hc
        use r + s + 1
        calc
          a + c = 2 * r + 1 + c := by rw [hr]
          _ = 2 * r + 1 + (2 * s + 1) := by rw [hs]
          _ = (r + s + 1) + (r + s + 1) := by ring
    · left
      obtain ⟨r, hr⟩ := ha
      obtain ⟨s, hs⟩ := hb
      use r - s
      calc
        a - b = 2 * r + 1 - b := by rw [hr]
        _ = 2 * r + 1 - (2 * s + 1) := by rw [hs]
        _ = (r - s) + (r - s) := by ring

/-5a-/
example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  have h' : (a + b) / 2 ≥ a ∨ (a + b) / 2 ≤ b := by apply h
  obtain ha | hb := h'
  · calc
    b = 2 * ((a + b) / 2) - a := by ring
    _ ≥ 2 * a - a := by rel [ha]
    _ = a := by ring
  · calc
    a = 2 * ((a + b) / 2) - b := by ring
    _ ≤ 2 * b - b := by rel [hb]
    _ = b := by ring

/-5b-/
example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  use -3
  intro x y
  intro h
  have h1 := calc
    (x+y)^2 ≤ (x+y)^2 + (x-y)^2 := by extra
    _ = 2 * (x^2 + y^2) := by ring
    _ ≤ 2 * 4 := by rel [h]
    _ ≤ (3)^2 := by numbers
  have h2 : (0:ℝ) ≤ 3 := by numbers
  exact And.left (abs_le_of_sq_le_sq' h1 h2)

/-5c-/
example {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n := by
  sorry

/-5d-/
example : forall_sufficiently_large x : ℝ, x ^ 3 + 3 * x ≥ 7 * x ^ 2 + 12 := by
  sorry

/-6a-/
example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  sorry

/-6b-/
example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  sorry