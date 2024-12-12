import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Order.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.PushNeg
import Mathlib.Tactic.Use
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Basic


namespace flt

open flt

-- Definition of Divides
def Divides (m n : ℕ) : Prop := ∃ k : ℕ, n = m * k

-- Definition of composite numbers
def composite (n : ℕ) : Prop := ∃ m : ℕ, 1 < m ∧ m < n ∧ Divides m n

-- Definition of prime numbers (as not composite)
def prime (n : ℕ) : Prop := n > 1 ∧ ¬ composite n

-- Lemma: If a | b and a | c, then a | b + c
lemma divides_add (a b c : ℕ) (hab : Divides a b) (hac : Divides a c) : Divides a (b + c) := by
  obtain ⟨k, hk⟩ := hab
  obtain ⟨l, hl⟩ := hac
  use k + l
  calc
    b + c = a * k + a * l := by rw [hk, hl]
    _ = a * (k + l)       := by ring

lemma prime_dvd_binomial_coeff {p k : ℕ} (hp : Nat.Prime p) (hk : 1 ≤ k ∧ k <= p-1) :
  Divides p (Nat.choose p k) := by
  -- Extract the bounds on k
  have h1 : k > 0 := hk.1
  have h2 : k < p := sorry
  have h3 : p - k < p := sorry
  have h4 : p <= p := sorry
  -- Apply the divisibility property of binomial coefficients
  exact Nat.Prime.dvd_choose hp h2 h3 h4

  lemma binomial_theorem_as_list_sum (a b n : ℕ) :
  (a + b)^n = ((List.range (n + 1)).map (λ k => Nat.choose n k * a^k * b^(n - k))).sum := by
  sorry

  lemma list_sum_cons {hd : ℕ} {tl : List ℕ} :
  List.sum (hd :: tl) = hd + List.sum tl := by
  sorry

lemma list_sum_divisible_of_all_divisible {l : List ℕ} {p : ℕ} (hp : ∀ x ∈ l, p ∣ x) :
  p ∣ l.sum := by
  induction l with
  |nil =>
    -- Base case: The list is empty, so l.sum = 0
    exact dvd_zero p
  |cons hd tl ih =>
    -- Inductive step: The list is of the form hd :: tl
    have h_hd : p ∣ hd := hp hd (List.mem_cons_self hd tl)
    have h_tl : p ∣ tl.sum := ih (λ x hx => hp x (List.mem_cons_of_mem hd hx))
    -- Combine results using divides_add
    dsimp [Nat.instDvdNat]
    rw[list_sum_cons]
    exact divides_add p hd tl.sum h_hd h_tl


-- Lemma: For prime p, p divides (a + b)^p - a^p - b^p
lemma fermat_little_lemma (p a b : ℕ) (hp : Nat.Prime p) : Divides p ((a + b)^p - a^p - b^p) := by
  rw [binomial_theorem_as_list_sum]
  dsimp[Divides]
  have h_sep : List.sum (List.map (fun k ↦ Nat.choose p k * a ^ k * b ^ (p - k)) (List.range (p + 1))) =
    a^p + b^p + List.sum (List.map (fun k ↦ Nat.choose p k * a ^ k * b ^ (p - k)) (List.iota (p - 1))) := by sorry
  rw[h_sep]
  have h_simp : a ^ p + b ^ p + List.sum (List.map (fun k ↦ Nat.choose p k * a ^ k * b ^ (p - k)) (List.iota (p - 1))) - a ^ p - b ^ p =
   List.sum (List.map (fun k ↦ Nat.choose p k * a ^ k * b ^ (p - k)) (List.iota (p - 1))) := by sorry
  rw[h_simp]
  apply list_sum_divisible_of_all_divisible
  intro k hk
  obtain ⟨s, hs⟩ := List.mem_map.mp hk
  dsimp[Nat.instDvdNat]
  have hs2 : k = Nat.choose p s * a ^ s * b ^ (p - s) := by rw[hs.right]
  rw[hs2]
  apply dvd_mul_of_dvd_left
  apply dvd_mul_of_dvd_left
  exact prime_dvd_binomial_coeff hp (List.mem_iota.mp hs.left)


lemma zero_pow_n {n : ℕ} (hn : 0 < n) : 0^n = 0 := by
  exact Nat.zero_pow hn

-- Main Theorem: For prime p and any natural number a, p divides a^p - a
theorem fermat_little_theorem {p a : ℕ} (hp : Nat.Prime p) : Divides p (a^p - a) := by

  have hpp : 0 < p := by {
    unfold Nat.Prime at hp
    obtain ⟨p_gt_one, p_not_composite⟩ := hp
    sorry
  }

  induction a with
  |zero =>
  dsimp
  use 0
  calc
    0 ^ p = 0 := zero_pow_n hpp
    _ = p * 0 := by rw [Nat.mul_zero]


  |succ k IH =>
  have hlm := fermat_little_lemma p k 1 hp
  obtain ⟨r, h1⟩ := IH
  obtain ⟨s, h2⟩ := hlm
  use r + s
  calc
    (k + 1) ^ p - (k + 1) = ((k + 1) ^ p - k ^ p - 1 ^ p) + (k ^ p - k) := by sorry
    _ = (p*s) + (p*r) := by rw[h1, h2]
    _ = p * (r + s) := by ring
