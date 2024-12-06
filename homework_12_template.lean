import Library.Basic
import Library.Tactic.ModEq
import Library.Tactic.Exhaust
import Mathlib.Data.Real.Basic


math2001_init

open Set Function

/-# Exercise 4-/

--Exercise 6.4.3.1

theorem extract_pow_two (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
match n with
|0 =>
have contra := Nat.not_lt_zero 0
contradiction
|1 =>
  use 0, 1
  constructor
  dsimp[Odd]
  use 0
  numbers
  numbers
|2 =>
  use 1, 1
  constructor
  dsimp[Odd]
  use 0
  numbers
  numbers
|k+3 =>
  let hevod := Nat.even_or_odd k
  let t := (Nat.succ k)
  have hk : Nat.succ k > 0 := by extra
  obtain heven | hodd := hevod
  have IH := extract_pow_two t hk
  obtain ⟨a, x, hodd, ht⟩ := IH
  use 0, k + 3
  constructor
  dsimp[Odd]
  obtain ⟨r, heven⟩ := heven
  use r+1
  rw[heven]
  ring
  ring
  have IH := extract_pow_two t hk
  obtain ⟨a, x, hod, ht⟩ := IH
  match a with
  |0 =>
  use 0, x+2
  constructor
  obtain ⟨l, hl⟩ := hod
  use l+1
  rw[hl]
  ring
  calc
    k + 3 = t + 2 := by rfl
    _ = 2 ^ 0 * x + 2 := by rw[ht]
    _ = 2 ^ 0 * (x + 2) := by ring
  |1 =>
    have hx : x + 1 > 0 := by extra
    have IH := extract_pow_two (x + 1) hx
    obtain ⟨y, u, huodd, hxx⟩ := IH
    use y+1, u
    constructor
    apply huodd
    calc
      k + 3 = t + 2 := by rfl
      _ = 2 ^ 1 * x + 2 := by rw[ht]
      _ = 2 * (x + 1) := by ring
      _ = 2 * (2 ^ y * u) := by rw[hxx]
      _ = 2 ^ (y + 1) * u := by ring
  |s + 2 =>
  use 1, 2 ^ (s + 1) * x + 1
  constructor
  use 2^s*x
  ring
  calc
    k + 3 = t + 2 := by rfl
    _ = 2 ^ (s + 2) * x + 2:= by rw[ht]
    _ = 2 ^ 1 * (2 ^ (s + 1) * x + 1) := by ring



/-# Exercise 5-/

------------------------------------------------------------------------------------
--Exercise 9.1.10.1

example : 4 ∈ {a : ℚ | a < 3} := by
  sorry

example : 4 ∉ {a : ℚ | a < 3} := by
  dsimp
  numbers

------------------------------------------------------------------------------------
--Exercise 9.1.10.2

example : 6 ∈ {n : ℕ | n ∣ 42} := by
  dsimp
  use 7
  numbers

example : 6 ∉ {n : ℕ | n ∣ 42} := by
  sorry

------------------------------------------------------------------------------------
--Exercise 9.1.10.3


example : 8 ∈ {k : ℤ | 5 ∣ k} := by
  sorry

example : 8 ∉ {k : ℤ | 5 ∣ k} := by
  dsimp
  dsimp[Int.instDvdInt]
  push_neg
  intro c
  by_cases h : c>=2
  apply ne_of_lt
  calc
    8 < 5 * 2 := by numbers
    _ <= 5 * c := by rel[h]
  apply ne_of_gt
  have h := lt_of_not_ge h
  have hh : c <= 1 := by addarith[h]
  calc
    5 * c <= 5 * 1 := by rel[hh]
    _ < 8 := by numbers


/-# Exercise 6-/
------------------------------------------------------------------------------------
--Exercise 9.1.10.6

example : {a : ℕ | 20 ∣ a} ⊆ {x : ℕ | 5 ∣ x} := by
  dsimp [Set.subset_def]
  intro a ha
  obtain ⟨k, hk⟩ := ha
  use 4 * k
  rw[hk]
  ring

example : {a : ℕ | 20 ∣ a} ⊈ {x : ℕ | 5 ∣ x} := by
  sorry

------------------------------------------------------------------------------------
--Exercise 9.1.10.7

example : {a : ℕ | 5 ∣ a} ⊆ {x : ℕ | 20 ∣ x} := by
  sorry

example : {a : ℕ | 5 ∣ a} ⊈ {x : ℕ | 20 ∣ x} := by
  dsimp [Set.subset_def]
  push_neg
  use 5
  constructor
  use 1
  ring
  dsimp[Nat.instDvdNat]
  push_neg
  intro c
  by_cases h : c>=1
  apply ne_of_lt
  calc
    5 < 20 * 1 := by numbers
    _ <= 20 * c := by rel[h]
  apply ne_of_gt
  have h := lt_of_not_ge h
  have hh : c <= 0 := by addarith[h]
  calc
    20 * c <= 20 * 0 := by rel[hh]
    _ < 5 := by numbers

------------------------------------------------------------------------------------
--Exercise 9.2.8.5

example : {r : ℤ | r ≡ 7 [ZMOD 10] }
    ⊆ {s : ℤ | s ≡ 1 [ZMOD 2]} ∩ {t : ℤ | t ≡ 2 [ZMOD 5]} := by
  dsimp [Set.subset_def]
  intro x hx
  constructor
  obtain ⟨t, ht⟩ := hx
  use 5*t + 3
  calc
    x - 1 = (x - 7) + 6 := by ring
    _ = (10 * t) + 6 := by rw[ht]
    _ = 2 * (5 * t + 3) := by ring
  obtain ⟨t, ht⟩ := hx
  use 2*t + 1
  calc
    x - 2 = (x - 7) + 5 := by ring
    _ = (10 * t) + 5 := by rw[ht]
    _ = 5 * (2 * t + 1) := by ring



/-# Problem 2-/

--Exercise 9.2.8.6

example : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} ⊆ {n : ℤ | 40 ∣ n} := by
  sorry

--Exercise 9.3.6.1

def r (s : Set ℕ) : Set ℕ := s ∪ {3}

example : ¬ Injective r := by
  sorry
