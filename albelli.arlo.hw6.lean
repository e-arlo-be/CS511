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

/-4a-/
example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h
    use x
    have hpq : P x ↔ Q x := h x
    rw [hpq] at hx
    exact hx
  · intro h
    obtain ⟨x, hx⟩ := h
    use x
    have hpq : Q x ↔ P x := by rw [h x]
    rw [hpq] at hx
    exact hx

/-4b-/
example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  · intro h
    obtain ⟨x, y, hxy⟩ := h
    use y
    use x
    exact hxy
  · intro h
    obtain ⟨y, x, hxy⟩ := h
    use x
    use y
    exact hxy

/-4c-/
example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  · intro h
    intro y
    intro x
    exact h x y
  · intro h
    intro x
    intro y
    exact h y x

/-4d-/
example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h.left
    use x
    constructor
    · exact hx
    · exact h.right
  · intro h
    obtain ⟨x, hx, hq⟩ := h
    constructor
    · use x
      exact hx
    · exact hq


    
    

  
    




example {P : α → β → Prop} (h : ∃ x : α, ∀ y : β, P x y) :
    ∀ y : β, ∃ x : α, P x y := by
  obtain ⟨x, hx⟩ := h
  intro y
  use x
  apply hx

example (P : α → Prop) : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x := by
  constructor
  · intro h a ha
    have : ∃ x, P x
    · use a
      apply ha
    contradiction
  · intro h h'
    obtain ⟨x, hx⟩ := h'
    have : ¬ P x := h x
    contradiction