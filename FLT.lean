import Library.Basic
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.ModEq.Defs
import Library.Tactic.ModEq
import Library.Theory.ParityModular

math2001_init

-- Definition of Divides
def Divides (m n : ℕ) : Prop := ∃ k : ℕ, n = m * k

-- Definition of composite numbers
def composite (n : ℕ) : Prop := ∃ m : ℕ, 1 < m ∧ m < n ∧ Divides m n

-- Definition of prime numbers (as not composite)
def prime (n : ℕ) : Prop := n > 1 ∧ ¬ composite n

-- Lemma: If a | b and a | c, then a | b + c
lemma divides_add {a b c : ℕ} (hab : Divides a b) (hac : Divides a c) : Divides a (b + c) :=
  sorry

-- Lemma: For prime p, p divides (a + b)^p - a^p - b^p
lemma fermat_little_lemma {p a b : ℕ} (hp : prime p) : Divides p ((a + b)^p - a^p - b^p) :=
  sorry

lemma zero_pow_n {n : ℕ} (hn : 0 < n) : 0^n = 0 := by
  exact Nat.zero_pow hn

-- Main Theorem: For prime p and any natural number a, p divides a^p - a
theorem fermat_little_theorem {p a : ℕ} (hp : prime p) : Divides p (a^p - a) := by

  have hp : 0 < p := by {
    unfold prime at hp
    obtain ⟨p_gt_one, p_not_composite⟩ := hp
    extra
  }

  match a with
  |0 =>
  dsimp
  use 0
  calc
    0 ^ p = 0 := zero_pow_n hp
    _ = p * 0 := by rw [Nat.mul_zero]

  |a+1 => sorry
