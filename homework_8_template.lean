import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel
import Library.Tactic.ModEq
import AutograderLib

math2001_init
set_option pp.funBinderTypes true

--# Exercise 3

--Slides 18, Page 25

example (h : ∃x : Type, ∀y : Type, (x = y)) : (∀x : Type, ∀y : Type, (x = y)) := by
  obtain ⟨w, hw⟩ := h
  intro x y
  have hx : w = x := hw x
  have hy : w = y := hw y
  calc
    x = x := by ring
    _ = w := by rw[hx]
    _ = y := by rw[hy]

--Slides 29 Part III, Page 8

example : (∃x : Type, ∀y : Type, (x = y)) → (∀v : Type, ∀w : Type, (v = w)) := by
  intro h
  obtain ⟨u, hu⟩ := h
  intro v w
  have hv : u = v := hu v
  have hw : u = w := hu w
  calc
    v = v := by ring
    _ = u := by rw[hv]
    _ = w := by rw[hw]

--# Exercise 4

--Exercise 5.3.6.9

example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  push_neg
  intro t
  by_cases h : t>4
  left
  apply h
  right
  by_cases h1 : t >= 5
  have hc : t > 4 := by
    calc
      t > t - 1 := by addarith[h]
      _ >= 5 - 1 := by rel[h1]
      _ = 4 := by ring
  contradiction
  apply lt_of_not_ge h1





--Example 6.1.2

example (n : ℕ) : Even n ∨ Odd n := by
  simple_induction n with k IH
  · -- base case
    dsimp [Even, Odd]
    left
    use 0
    ring
  · -- inductive step
    obtain ⟨x, hx⟩ | ⟨x, hx⟩ := IH
    · right
      dsimp [Odd]
      use x
      calc
        k + 1 = (x + x) + 1 := by rw[hx]
        _ = 2*x + 1 := by ring
    · left
      dsimp [Even]
      use x+1
      calc
        k+1 = (2*x+1) +1 := by rw[hx]
        _ = x + 1 + (x + 1) := by ring

--Example 6.1.6

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc
      2 ^ (k+1) = 2*(2^k) := by ring
      _ >= 2 * (k^2) := by rel[IH]
      _ = k^2 + k*k := by ring
      _ >= k^2 + 4*k := by rel[hk]
      _ = k^2+2*k+2*k := by ring
      _ >= k^2+2*k+2*4 := by rel[hk]
      _ = (k+1)^2 +7 := by ring
      _ >= (k+1)^2 := by extra

--# Problem 2

--Exercise 5.3.6.12

example : ¬ ∃ a : ℤ, ∀ n : ℤ, 2 * a ^ 3 ≥ n * a + 7 := by
  push_neg
  intro a
  use 2*a^2
  calc
    2 * a ^ 3 = 2* a ^ 2 * a := by ring
    _ < 2*a ^ 2 * a + 7 := by extra

--Exercise 6.1.7.2

example {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  sorry

--Exercise 6.1.7.3

example (n : ℕ) : 5 ^ n ≡ 1 [ZMOD 8] ∨ 5 ^ n ≡ 5 [ZMOD 8] := by
  sorry
