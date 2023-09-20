import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Mathlib.Algebra.Order.Group.Defs

/- 5a -/
example {p q : Prop} : ¬p ∧ ¬q → ¬(p ∨ q) := by
  intros h_npnq h_pq
  have h_np : ¬p := by apply And.left h_npnq
  have h_nq : ¬q := by apply And.right h_npnq
  cases h_pq with
  | inr h_p => contradiction
  | inl h_q => contradiction

/- 5b -/
example {p q : Prop} : (¬p ∨ ¬q) → ¬(p ∧ q) := by
  intros h1 h2
  have h_p : p := And.left h2
  have h_q : q := And.right h2
  cases h1 with 
  | inr h_np => contradiction
  | inl h_nq => contradiction


/- 6a -/
example {x y : ℤ} (h1 : x + 3 ≥ 2 * y) (h2 : 1 ≤ y) : x ≥ -1 := by
  calc
    x ≥ 2 * y - 3 := by linarith
    _ ≥ 2 * 1 - 3 := by rel [h2]
    _ ≥ -1 := by numbers

/- 6b -/
example {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 :=
by linarith

/- 6c -/
example {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 :=
  calc
    x ^ 3 - 8 * x ^ 2 + 2 * x 
    = x * x ^ 2 - 8 * x ^ 2 + 2 * x := by ring
    _ ≥ 9 * x ^ 2 - 8 * x ^ 2 + 2 * x := by rel [hx]
    _ = x ^ 2 + 2 * x := by ring
    _ ≥ 9 ^ 2 + 2 * 9 := by rel [hx]
    _ ≥ 3 := by numbers

















