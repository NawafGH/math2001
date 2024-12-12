import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq

math2001_init

/-# Exercise 3-/

--Exercise 10.1.5.4

section
local infix:50 "∼" => fun (x y : ℤ) ↦ y ≡ x + 1 [ZMOD 5]

example : Reflexive (· ∼ ·) := by
  sorry

example : ¬ Reflexive (· ∼ ·) := by
  dsimp[Reflexive]
  push_neg
  use 0
  dsimp[Int.ModEq]
  dsimp[Int.instDvdInt]
  push_neg
  intro c
  by_cases h : c>-1
  apply ne_of_lt
  have hh : 0<=c := by addarith[h]
  calc
    0 - (0 + 1) = -1 := by ring
    _ < 5 * 0 := by numbers
    _ <= 5 * c := by rel[hh]
  apply ne_of_gt
  have h := le_of_not_gt h
  calc
    5*c <= 5 * (-1) := by rel[h]
    _ < -1 := by numbers
    _ = 0 - (0 + 1) := by ring

example : Symmetric (· ∼ ·) := by
  sorry

example : ¬ Symmetric (· ∼ ·) := by
  dsimp[Symmetric]
  push_neg
  use 0
  use 1
  constructor
  dsimp[Int.ModEq]
  use 0
  ring
  dsimp[Int.ModEq]
  dsimp[Int.instDvdInt]
  push_neg
  intro c
  by_cases h : c>-1
  apply ne_of_lt
  have hh : 0<=c := by addarith[h]
  calc
    0 - (1 + 1) = -2 := by ring
    _ < 5 * 0 := by numbers
    _ <= 5 * c := by rel[hh]
  apply ne_of_gt
  have h := le_of_not_gt h
  calc
    5*c <= 5 * (-1) := by rel[h]
    _ < -2 := by numbers
    _ = 0 - (1 + 1) := by ring

example : AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]
  intro x y
  intro h1 h2
  have h3 := by apply Int.ModEq.add h1 h2
  have h4 : (x + y) - (y + x) ≡ (x + y) - (x + 1 + (y + 1)) [ZMOD 5] := Int.ModEq.sub_left h3
  have rw1 : x + y - (y + x) = 0 := by ring
  rw[rw1] at h4
  have rw2 : x + y - (x + 1 + (y + 1)) = -2 := by ring
  rw[rw2] at h4
  have contra : ¬ 0 ≡ -2 [ZMOD 5] := by {
    dsimp[Int.ModEq]
    dsimp[Int.instDvdInt]
    push_neg
    intro c
    by_cases h : c>0
    apply ne_of_lt
    have hh : 1<=c := by addarith[h]
    calc
      0 - (-2) = 2 := by ring
      _ < 5 * 1 := by numbers
      _ <= 5 * c := by rel[hh]
    apply ne_of_gt
    have h := le_of_not_gt h
    calc
      5*c <= 5 * (0) := by rel[h]
      _ < 2 := by numbers
      _ = 0 - (-2) := by ring

  }
  contradiction




example : ¬ AntiSymmetric (· ∼ ·) := by
  sorry

example : Transitive (· ∼ ·) := by
  sorry

example : ¬ Transitive (· ∼ ·) := by
  dsimp[Transitive]
  push_neg
  use 0
  use 1
  use 2
  constructor
  use 0
  ring
  constructor
  use 0
  ring
  dsimp[Int.ModEq]
  dsimp[Int.instDvdInt]
  push_neg
  intro c
  by_cases h : c>0
  apply ne_of_lt
  have hh : 1<=c := by addarith[h]
  calc
    - (- (2 - (0 + 1))) = 1 := by numbers
    _ < 5 * 1 := by numbers
    _ <= 5 * c := by rel[hh]
  apply ne_of_gt
  have h := le_of_not_gt h
  calc
    5*c <= 5 * (0) := by rel[h]
    _ < 1 := by numbers
    _ = 2 - (1) := by ring

end

/-# Exercise 4-/

--Exercise 10.1.5.5

section
local infix:50 "∼" => fun (x y : ℤ) ↦ x + y ≡ 0 [ZMOD 3]

example : Reflexive (· ∼ ·) := by
  sorry

example : ¬ Reflexive (· ∼ ·) := by
  dsimp[Reflexive]
  push_neg
  use 1
  dsimp[Int.ModEq]
  dsimp[Int.instDvdInt]
  push_neg
  intro c
  by_cases h : c>0
  apply ne_of_lt
  have hh : 1<=c := by addarith[h]
  calc
    -(-(1 + 1)) = 2 := by ring
    _ < 3 * 1 := by numbers
    _ <= 3 * c := by rel[hh]
  apply ne_of_gt
  have h := le_of_not_gt h
  calc
    3*c <= 3 * (0) := by rel[h]
    _ = 0 := by numbers
    _ < 1 + 1 := by numbers

example : Symmetric (· ∼ ·) := by
  dsimp[Symmetric]
  intro x y h
  have hh : y+x=x+y := by ring
  rw[hh]
  apply h

example : ¬ Symmetric (· ∼ ·) := by
  sorry

example : AntiSymmetric (· ∼ ·) := by
  sorry

example : ¬ AntiSymmetric (· ∼ ·) := by
  dsimp[AntiSymmetric]
  push_neg
  use 1
  use 2
  constructor
  use 1
  ring
  constructor
  use 1
  ring
  numbers

example : Transitive (· ∼ ·) := by
  sorry

example : ¬ Transitive (· ∼ ·) := by
  dsimp[Transitive]
  push_neg
  use 1
  use 2
  use 1
  constructor
  use 1
  ring
  constructor
  use 1
  ring
  dsimp[Int.ModEq]
  dsimp[Int.instDvdInt]
  push_neg
  intro c
  by_cases h : c>0
  apply ne_of_lt
  have hh : 1<=c := by addarith[h]
  calc
    -(-(1+1)) = 2 := by ring
    _ < 3 * 1 := by numbers
    _ <= 3 * c := by rel[hh]
  apply ne_of_gt
  have h := le_of_not_gt h
  calc
    3*c <= 3 * (0) := by rel[h]
    _ < 2 := by numbers
    _ = 1+1 := by ring

end

/-# Problem 2-/

--Exercise 10.1.5.6

example : Reflexive ((· : Set ℕ) ⊆ ·) := by
  sorry

example : ¬ Reflexive ((· : Set ℕ) ⊆ ·) := by
  sorry

example : Symmetric ((· : Set ℕ) ⊆ ·) := by
  sorry

example : ¬ Symmetric ((· : Set ℕ) ⊆ ·) := by
  sorry

example : AntiSymmetric ((· : Set ℕ) ⊆ ·) := by
  sorry

example : ¬ AntiSymmetric ((· : Set ℕ) ⊆ ·) := by
  sorry

example : Transitive ((· : Set ℕ) ⊆ ·) := by
  sorry

example : ¬ Transitive ((· : Set ℕ) ⊆ ·) := by
  sorry
