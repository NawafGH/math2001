import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Homework 2 -/

/- # Exercise 3 -/

-- Example 1.4.6
example {n : ℤ} (hn : n ≥ 5) : n ^ 2 > 2 * n + 11 :=
  calc
    n ^ 2 = n * n := by ring
    _ >= 5 * n := by rel [hn]
    _ = 2 * n + 3 * n := by ring
    _ >= 2 * n + 3 * 5 := by rel [hn]
    _ = 2 * n + 11 + 4 := by ring
    _ > 2 * n + 11 := by extra



-- Example 2.1.3
example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by
  have h3 : r ≤ 3 + s := by addarith [h1] -- justify with one tactic
  have h4 : r ≤ 3 - s := by addarith [h2] -- justify with one tactic
  calc
    r = (r + r) / 2 := by ring -- justify with one tactic
    _ ≤ (3 - s + (3 + s)) / 2 := by rel [h3, h4] -- justify with one tactic
    _ = 3 := by ring -- justify with one tactic

-- Example 2.1.7
example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have h3: 0 <= b + a := by addarith [h1]
  have h4: 0 <= b - a := by addarith [h2]
  calc
    a ^ 2 <= a ^ 2 := by rfl
    _ <= a ^ 2 + (b + a) * (b - a) := by extra
    _ = b ^ 2 := by ring


/- # Exercise 4 -/

example {a b : ℝ} (h1 : a ^ 2 = b ^ 2 + 1) (h2 : a ≥ 0) : a ≥ 1 := by
  have h3 :=
  calc
    a ^ 2 = b ^ 2 + 1 := by rw [h1]
    _ ≥ 1 := by extra
    _ = 1 ^ 2 := by ring
  cancel 2 at h3

-- Exercise 2.1.9 (1)
example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 :=
  calc
    0 = x ^ 2 - x ^ 2 := by ring
    _ = x ^ 2 - 4 := by rw [h1]
    _ = (x - 2) * (x + 2) := by ring
  have h4 :=
  calc
    (x - 2) * (x + 2) = 0 := by rw [h3]
    _ = 0 * (x + 2) := by ring
  cancel (x + 2) at h4
  calc
    x = (x - 2) + 2 := by ring
    _ = 0 + 2 := by rw [h4]
    _ = 2 := by ring



-- Exercise 2.1.9 (3)
example (x y : ℚ) (h : x * y = 1) (h2 : x ≥ 1) : y ≤ 1 := by
have h3 :=
calc
  y >= y := by rfl
  _ = y * 1 := by ring
  _ = y * (x * y) := by rw [h]
  _ = y ^ 2 * x := by ring
  _ >= y ^ 2 * 1 := by rel [h2]
  _ = y ^ 2 := by ring
have h4 :=
calc
  y >= y := by rfl
  _ >= y ^ 2 := by rel [h3]
  _ = y ^ 2 + 0 := by ring
  _ >= 0 := by extra
calc
  y = y * 1 := by ring
  _ <= y * x := by rel [h2]
  _ = x * y := by ring
  _ = 1 := by rw [h]


--Exercise 2.2.4 (1)
example {m : ℤ} (hm : m + 1 = 5) : 3 * m ≠ 6 := by
  apply ne_of_gt
  calc
    3 * m = 3 * (m + 1) - 3 := by ring
    _ = 3 * (5) - 3 := by rw [hm]
    _ = 6 + 6 := by numbers
    _ > 6 := by extra


/- # Problem 2 -/

-- Example 2.1.8
example (a b : ℝ) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by sorry

-- Exercise 2.1.9 (2)
example {n : ℤ} (hn : n ^ 2 + 4 = 4 * n) : n = 2 := by sorry

-- Exercise 2.2.4 (2)
example {s : ℚ} (h1 : 3 * s ≤ -6) (h2 : 2 * s ≥ -4) : s = -2 := by sorry
