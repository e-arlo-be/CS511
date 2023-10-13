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

namespace Nat
/-4a-/
example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor
  ·intro h
   obtain ⟨k, hk⟩ := h
   constructor
   ·use 9 * k
    calc
      n = 63 * k := by apply hk
      _ = 7 * (9 * k) := by ring
   ·use 7 * k
    calc
      n = 63 * k := by apply hk
      _ = 9 * (7 * k) := by ring
  ·intro h
   obtain ⟨h7, h9⟩ := h
   obtain ⟨k, hk⟩ := h7
   obtain ⟨l, hl⟩ := h9
   use (4 * l) - (3 * k)
   calc
      n = 28 * n - 27 * n := by ring
      _ = 4 * 7 * n + (-3) * 9 * n := by ring
      _ = 4 * 7 * (n) + (-3) * 9 * (7 * k) := by rw [hk]
      _ = 4 * 7 * (9 * l) + (-3) * 9 * (7 * k) := by rw [hl]
      _ = 63 * (4 * l - 3 * k) := by ring

/-4b-/
example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  · intros h
    have h0 := le_or_gt k 0
    obtain h0 | h0 := h0
    · left
      simp at h0
      exact h0
    · right
      have h1 := le_or_gt k 1
      obtain h1 | h1 := h1
      · left
        have h1' : k ≥ 1 := by addarith [h0]
        apply le_antisymm h1 h1'
      · right
        have h2 : k ≥ 2 := by addarith [h1]
        have h3 : ¬(k ≥ 3) := by
          intros h4
          have h5 : 3 * 2 ≥ 3 * k := 
          calc
            3 * 2 = 6 := by ring
            _ ≥ k ^ 2 := by rel[h]
            _ = k * k := by ring
            _ ≥ 3 * k := by rel[h4]
          cancel 3 at h5
          have h6 : k = 2 := le_antisymm h5 h2
          rw [h6] at h4
          numbers at h4
        simp at h3
        addarith [h2, h3]
  · intros h
    obtain h0 | h1 | h2 := h
    · simp [h0]
    · simp [h1]
    · simp [h2]

/-5a-/

example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  dsimp
  constructor
  · intros a h1 h2
    have h1' : 1 ≤ a := by rel[h1]
    have h1'' : -1 ≤ a - 2 := by addarith [h1']
    have h2' : a - 2 ≤ 1 := by addarith [h2]
    have h3 := sq_le_sq' h1'' h2'
    calc
      (a - 2) ^ 2 ≤ 1 ^ 2 := by rel[h3]
      _ = 1 := by ring
  · intros x h
    have h1 := h 1
    have h3 := h 3
    have h1' := by
      apply h1
      simp
      simp
    have h3' := by
      apply h3
      simp
      simp
    have h4 : (x - 2) ^ 2 ≤ 0 := by
      calc
        (x - 2) ^ 2 = ((1 - x) ^ 2 + (3 - x) ^ 2 - 2) / 2 := by ring
        _ ≤ (1 + (3 - x) ^ 2 - 2) / 2 := by rel [h1']
        _ ≤ (1 + 1 - 2) / 2 := by rel [h3']
        _ = 0:= by numbers
    have h5 : (x - 2) ^ 2 ≥ 0 := by extra
    have h5' : (x - 2) ^ 2 = 0 := by apply le_antisymm h4 h5
    have h5'' : (x - 2) * (x - 2) = 0 := by
      calc
        (x - 2) * (x - 2) = (x - 2) ^ 2 := by ring
        _ = 0 := by rw [h5']
    have h6 := eq_zero_or_eq_zero_of_mul_eq_zero h5''
    cases h6 with
    | inl l => addarith [l]
    | inr r => addarith [r]

/-5b-/
example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  simp
  constructor
  · numbers
  · intros y hy
    have h : 4 * y = 4 * 3 :=
      calc
        4 * y = 4 * y - 3 + 3 := by ring
        _ = 9 + 3 := by rw [hy]
        _ = 12 := by numbers
        _ = 4 * 3 := by numbers
    cancel 4 at h

/-5c-/
example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  constructor
  · simp
  · simp
    intros y hy
    have hy0 : y ≥ 0 := by extra
    have hy1 := by apply hy 0
    apply le_antisymm hy1 hy0

/-6a-/
example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp -- show that `2 ≤ p`
  intro m hmp
  have hp' : 0 < p := by extra
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
  obtain hm | hm_left : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  · -- the case `m = 1`
    left
    addarith [hm]
  -- the case `1 < m`
  · 
    have h1 : m ≤ p := Nat.le_of_dvd hp' hmp
    have h2 : m = p ∨ m < p := eq_or_lt_of_le h1
    cases h2 with 
    | inl l =>
      right
      apply l
    | inr r =>
      have hn1 := H m
      have hn2 : ¬m ∣ p := by
        apply hn1
        apply hm_left
        apply r
      contradiction

/-6b-/

/-6c-/
example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
  cancel n at h

/-6d-/
example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  -- dsimp [Prime] at *
  obtain ⟨h1, h2⟩ := h
  have h3 := le_or_gt p 2
  obtain h3 | h3 := h3
  · left
    apply le_antisymm h3 h1
  · right
    have heo := Nat.even_or_odd p
    dsimp [Even] at heo
    cases heo with
    | inr r =>
      apply r
    | inl l => 
      



      

      

  
    
    


      

    


      

    
  












    
    

    
    
    


    
    
    

    

    
    







            







   
    
   




      
      
