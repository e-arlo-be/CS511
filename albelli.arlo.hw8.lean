import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Use

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

theorem problem4a {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by
  simple_induction n with k IH
  · -- base case
    extra
  · -- inductive step
    obtain ⟨x, hx⟩ := IH
    obtain ⟨y, hy⟩ := h
    use a * x + b ^ k * y
    calc
      a ^ (k + 1) - b ^ (k + 1) = a * (a ^ k - b ^ k) + b ^ k * (a - b) := by ring
      _ = a * (d * x) + b ^ k * (d * y) := by rw [hx, hy]
      _ = d * (a * x + b ^ k * y) := by ring

/-4b-/
theorem problem4b : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc
      2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * k ^ 2 := by rel[IH]
      _ = k ^ 2 + k * k := by ring
      _ ≥ k ^ 2 + 4 * k := by rel[hk]
      _ = k ^ 2 + 2 * k + 2 * k := by ring
      _ ≥ k ^ 2 + 2 * k + 2 * 4 := by rel[hk]
      _ = (k + 1) ^ 2 + 7 := by ring
      _ ≥ (k + 1) ^ 2 := by extra

/-4c-/
theorem problem4c {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  simp
  simple_induction n with k IH
  · -- base case
    have h0 : 1 + 0 * a ≤ (1 + a) ^ 0 := by
      calc
        1 + 0 * a = 1 := by ring
        _ ≤ 1 := by numbers
    apply h0
  · -- inductive step
    have ha : 1 + a ≥ 0 := by addarith[ha]
    calc
      (1 + a) ^ (k + 1) = (1 + a) ^ k * (1 + a) := by ring
      _ ≥ (1 + k * a) * (1 + a) := by rel[IH]
      _ = 1 + a + k * a + k * a ^ 2:= by ring
      _ = 1 + (k + 1) * a + k * a ^ 2:= by ring
      _ ≥ 1 + (k + 1) * a := by extra

/-4d-/
theorem problem4d : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  use 5
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc
      (3:ℤ) ^ (k + 1) = 3 * 3 ^ k := by ring
      _ ≥ 3 * (2 ^ k + 100) := by rel[IH]
      _ = 2 * (2 ^ k + 100) + (2 ^ k + 100) := by ring
      _ ≥ 2 * (2 ^ k + 100) := by extra
      _ = 2 ^ (k + 1) + 100 + 100 := by ring
      _ ≥ 2 ^ (k + 1) + 100 := by extra

/-5b-/
def recursive_sum : ℕ → ℕ
  | 0 => 0
  | (n + 1) =>  2 * n + 1 + (recursive_sum n)

theorem problem5b (n : ℕ) (hn : 1 ≤ n): ∃ j : ℕ, recursive_sum n = j ^ 2 := by
  use n
  induction_from_starting_point n, hn with k hk IH
  · dsimp[recursive_sum]
    numbers
  · dsimp[recursive_sum]
    ring
    rw[IH]
