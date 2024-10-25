import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel
import AutograderLib

math2001_init
set_option pp.funBinderTypes true

--Exercise 5.1.7.6

@[autograded 2]
example {P Q R : Prop} (h : P ↔ Q) : (P ∧ R) ↔ (Q ∧ R) := by
  constructor
  intro hpr
  constructor
  obtain ⟨hp, hr⟩ := hpr
  obtain ⟨hph, hqh⟩ := h
  apply hph
  apply hp
  ----
  obtain ⟨hp, hr⟩ := hpr
  apply hr
  ----
  intro hqr
  constructor
  obtain ⟨hq, hr⟩ := hqr
  obtain ⟨hph, hqh⟩ := h
  apply hqh
  apply hq
  ----
  obtain ⟨hq, hr⟩ := hqr
  apply hr




--Exercise 5.1.7.8

@[autograded 2]
example (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
  constructor
  intro hpq
  obtain hp | hq := hpq
  right
  apply hp
  left
  apply hq
  intro hqp
  obtain hq | hp := hqp
  right
  apply hq
  left
  apply hp

--Exercise 5.1.7.9

@[autograded 2]
example (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  constructor
  intro hnPorQ
  constructor
  intro hp
  apply hnPorQ
  left
  apply hp
  intro hq
  apply hnPorQ
  right
  apply hq
  ----
  intro hnPandnQ
  obtain ⟨ hnp, hnq ⟩ := hnPandnQ
  intro hPorQ
  obtain hp | hq := hPorQ
  apply hnp
  apply hp
  apply hnq
  apply hq



--Exercise 5.1.7.11

@[autograded 2]
example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  intro hp
  obtain ⟨x, hx⟩ := hp
  use x
  have hpq : P x ↔ Q x := by apply h
  obtain ⟨hph, hqh⟩ := hpq
  apply hph
  apply hx
  intro hq
  obtain ⟨x, hx⟩ := hq
  use x
  have hqp : P x ↔ Q x := by apply h
  obtain ⟨hph, hqh⟩ := hqp
  apply hqh
  apply hx


--Exercise 5.1.7.12

@[autograded 2]
example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  intro hp
  obtain ⟨x, y, hxy⟩ := hp
  use y, x
  apply hxy
  intro hp
  obtain ⟨y, x, hyx⟩ := hp
  use x, y
  apply hyx

--Exercise 5.1.7.13

@[autograded 2]
example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  intro hp y x
  apply hp
  intro hp x y
  apply hp



--Exercise 5.1.7.14

@[autograded 3]
example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  intro hpq
  obtain ⟨hp, hq⟩ := hpq
  obtain ⟨x, hx⟩ := hp
  use x
  constructor
  apply hx
  apply hq
  intro hpq
  obtain ⟨x, hpq⟩ := hpq
  obtain ⟨hp, hq⟩ := hpq
  constructor
  use x
  apply hp
  apply hq


--Exercise 5.2.7.2

@[autograded 3]
example (P Q : Prop) : (¬P → ¬Q) ↔ (Q → P) := by
  constructor
  intro h1 h2
  by_cases h3 : P
  apply h3
  have h4 : ¬Q := by {
    apply h1
    apply h3
  }
  contradiction
  intro h1 h2
  by_cases h3 : Q
  have h4 : P := by {
    apply h1
    apply h3
  }
  contradiction
  apply h3
