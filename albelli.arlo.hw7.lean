import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.Rel
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

/-4a-/
example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  push_neg
  intro n
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers
  · apply ne_of_gt
    calc
      2 < 2 ^ 2 := by numbers
      _ ≤ n ^ 2 := by rel [hn]

/-4b-/
/-cant use not_imp or push_neg in this one-/
/-NEED TO USE LEM-/
example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  by_cases hpq : P → Q
  · simp [hpq]
  · simp [hpq]
    simp at hpq
    exact hpq

/-5a-/
example {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  intros hp
  use k
  constructor
  · apply hk
  · constructor
    · apply hk1
    · apply hkp

/-5b-/
/-Suggested structure: Set up an intermediate goal that any natural number
2 ≤ m < p  is not a factor of p, and prove it by contradiction using the
lemma prime_test from Example 4.4.4. Then negation-normalize that result.-/
example {p : ℕ} (hp : ¬ Prime p) (hp2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have H : ¬ (∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p)
  · intro H
    apply hp
    apply prime_test
    · exact hp2
    · exact H
  push_neg at H
  exact H
