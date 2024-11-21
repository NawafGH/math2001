import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Theory.InjectiveSurjective
import Library.Tactic.ModEq

math2001_init
set_option pp.funBinderTypes true

open Function

/-# Exercise 3-/

--Exercise 8.3.10.2

def u (x : ℝ) : ℝ := 5 * x + 1

noncomputable def v (x : ℝ) : ℝ := (x-1)/5

example : Inverse u v := by
  dsimp[Inverse]
  constructor
  ext x
  calc
    (v ∘ u) x = v (u x) := by rfl
    _ = ((5 * x + 1) - 1)/5 := by rfl
    _ = x := by ring
    _ = id x := by rfl
  ext x
  calc
    (u ∘ v) x = u (v x) := by rfl
    _ = 5* ((x-1)/5) +1 := by rfl
    _ = x := by ring
    _ = id x := by rfl



--Exercise 8.3.10.3

example {f : X → Y} (hf : Injective f) {g : Y → Z} (hg : Injective g) :
    Injective (g ∘ f) := by
  dsimp[Injective]
  intro a b h
  apply hg at h
  apply hf at h
  apply h
--Exercise 8.3.10.4

example {f : X → Y} (hf : Surjective f) {g : Y → Z} (hg : Surjective g) :
    Surjective (g ∘ f) := by
  dsimp[Surjective]
  intro b
  have hgg := hg b
  obtain ⟨t, ht⟩ := hgg
  have hff := hf t
  obtain ⟨r, hr⟩ := hff
  use r; rw[hr, ht]


/-# Exercise 4-/

--Exercise 8.4.10.1

example : Bijective (fun ((r, s) : ℚ × ℚ) ↦ (s, r - s)) := by
  dsimp[Bijective]
  constructor
  dsimp[Injective]
  intro a b h
  obtain ⟨h', h''⟩ := h
  have h''' : a.1 = b.1 := by {
    calc
      a.1 = (a.1 - a.2) +a.2 := by ring
      _ = (b.1 - b.2) + a.2 := by rw[h'']
      _ = (b.1 - b.2) + b.2 := by rw[h']
      _ = b.1 := by ring
  }
  calc
    a = (a.1, a.2) := by rfl
    _ = (b.1, b.2) := by rw[h',h''']
    _ = b := by rfl
  dsimp[Surjective]
  intro (x, y)
  use (x + y, x)
  calc
    ((x + y, x).2, (x + y, x).1 - (x + y, x).2) = (x, x + y - x) := by rfl
    _ = (x, y) := by ring




--Exercise 8.4.10.2.1

example : ¬ Injective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  dsimp[Injective]
  push_neg
  use (0, 0)
  use (2, 1)
  constructor
  ring
  numbers

--Exercise 8.4.10.2.2

example : Surjective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  dsimp[Surjective]
  intro b
  use (3 * b + 1, b)
  ring

/-# Problem 2-/

--Exercise 8.3.10.5

example {f : X → Y} (hf : Surjective f) : ∃ g : Y → X, f ∘ g = id := by
  sorry

--Exercise 8.3.10.7

example {f : X → Y} {g1 g2 : Y → X} (h1 : Inverse f g1) (h2 : Inverse f g2) :
    g1 = g2 := by
  sorry
